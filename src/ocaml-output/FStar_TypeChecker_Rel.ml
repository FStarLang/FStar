
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

let k' = (let _152_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _152_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) None r)
in (let _152_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_152_8), (uv))))))
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


let term_to_string = (fun env t -> (match ((let _152_91 = (FStar_Syntax_Subst.compress t)
in _152_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(let _152_93 = (FStar_Syntax_Print.uvar_to_string u)
in (let _152_92 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _152_93 _152_92)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = _55_77; FStar_Syntax_Syntax.pos = _55_75; FStar_Syntax_Syntax.vars = _55_73}, args) -> begin
(let _152_96 = (FStar_Syntax_Print.uvar_to_string u)
in (let _152_95 = (FStar_Syntax_Print.term_to_string ty)
in (let _152_94 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _152_96 _152_95 _152_94))))
end
| _55_87 -> begin
(FStar_Syntax_Print.term_to_string t)
end))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _152_115 = (let _152_114 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _152_113 = (let _152_112 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _152_111 = (let _152_110 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _152_109 = (let _152_108 = (let _152_107 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _152_106 = (let _152_105 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _152_104 = (let _152_103 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _152_102 = (let _152_101 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_152_101)::[])
in (_152_103)::_152_102))
in (_152_105)::_152_104))
in (_152_107)::_152_106))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_152_108)
in (_152_110)::_152_109))
in (_152_112)::_152_111))
in (_152_114)::_152_113))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _152_115))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _152_117 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _152_116 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _152_117 (rel_to_string p.FStar_TypeChecker_Common.relation) _152_116)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _152_122 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _152_122 FStar_Util.string_of_int))
end
in (let _152_123 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _152_123)))
end
| TERM ((u, _55_103), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _152_124 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _152_124 FStar_Util.string_of_int))
end
in (let _152_125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _152_125)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _152_130 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _152_130 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _152_134 = (let _152_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _152_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _152_134 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _152_137 = (FStar_All.pipe_right args (FStar_List.map (fun _55_116 -> (match (_55_116) with
| (x, _55_115) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _152_137 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = true; smt_ok = true; tcenv = env})


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _55_121 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_121.wl_deferred; ctr = _55_121.ctr; defer_ok = _55_121.defer_ok; smt_ok = smt_ok; tcenv = _55_121.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let _55_127 = (empty_worklist env)
in (let _152_152 = (FStar_List.map Prims.snd g)
in {attempting = _152_152; wl_deferred = _55_127.wl_deferred; ctr = _55_127.ctr; defer_ok = false; smt_ok = _55_127.smt_ok; tcenv = _55_127.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _55_132 = wl
in {attempting = _55_132.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = _55_132.ctr; defer_ok = _55_132.defer_ok; smt_ok = _55_132.smt_ok; tcenv = _55_132.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _55_136 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_136.wl_deferred; ctr = _55_136.ctr; defer_ok = _55_136.defer_ok; smt_ok = _55_136.smt_ok; tcenv = _55_136.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _55_141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_169 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _152_169))
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
(FStar_All.pipe_right (maybe_invert p) (fun _152_176 -> FStar_TypeChecker_Common.TProb (_152_176)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _152_177 -> FStar_TypeChecker_Common.CProb (_152_177)))
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
(FStar_All.pipe_left (fun _152_196 -> FStar_TypeChecker_Common.TProb (_152_196)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _152_197 -> FStar_TypeChecker_Common.CProb (_152_197)) (invert p))
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


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _152_210 = (next_pid ())
in (let _152_209 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _152_210; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _152_209; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _152_220 = (next_pid ())
in (let _152_219 = (let _152_218 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _152_218 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _152_220; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _152_219; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _152_227 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _152_227; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _152_239 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _152_238 = (prob_to_string env d)
in (let _152_237 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _152_239 _152_238 _152_237 s))))
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
(let _152_241 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _152_240 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_152_241), (_152_240))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _152_243 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _152_242 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_152_243), (_152_242))))
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


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_262 = (let _152_261 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _152_261))
in (FStar_Syntax_Subst.compress _152_262)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _152_267 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _152_267)))


let norm_arg = (fun env t -> (let _152_270 = (sn env (Prims.fst t))
in ((_152_270), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_293 -> (match (_55_293) with
| (x, imp) -> begin
(let _152_277 = (

let _55_294 = x
in (let _152_276 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_276}))
in ((_152_277), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _152_284 = (aux u)
in FStar_Syntax_Syntax.U_succ (_152_284))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _152_285 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_152_285))
end
| _55_306 -> begin
u
end)))
in (let _152_286 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _152_286))))


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
(let _152_300 = (let _152_299 = (FStar_Syntax_Print.term_to_string tt)
in (let _152_298 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _152_299 _152_298)))
in (FStar_All.failwith _152_300))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _152_301 = (FStar_Syntax_Subst.compress t1')
in _152_301.FStar_Syntax_Syntax.n)) with
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
(let _152_304 = (let _152_303 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_302 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _152_303 _152_302)))
in (FStar_All.failwith _152_304))
end))
in (let _152_305 = (whnf env t1)
in (aux false _152_305))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _152_310 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _152_310 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _152_313 = (FStar_Syntax_Syntax.null_bv t)
in ((_152_313), (FStar_Syntax_Util.t_true))))


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
(let _152_326 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _152_325 = (let _152_322 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _152_322))
in (let _152_324 = (let _152_323 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _152_323))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _152_326 _152_325 (rel_to_string p.FStar_TypeChecker_Common.relation) _152_324))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _152_329 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _152_328 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _152_327 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _152_329 _152_328 (rel_to_string p.FStar_TypeChecker_Common.relation) _152_327))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _152_335 = (let _152_334 = (let _152_333 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_422 -> (match (_55_422) with
| (_55_418, _55_420, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _152_333))
in (FStar_List.map (wl_prob_to_string wl) _152_334))
in (FStar_All.pipe_right _152_335 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _55_441 = (match ((let _152_342 = (FStar_Syntax_Subst.compress k)
in _152_342.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _152_343 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_152_343)))
end else begin
(

let _55_432 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_432) with
| (ys', t) -> begin
(let _152_344 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_152_344)))
end))
end
end
| _55_434 -> begin
(let _152_346 = (let _152_345 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_152_345)))
in ((((ys), (t))), (_152_346)))
end)
in (match (_55_441) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(

let c = (let _152_347 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _152_347 c))
in (let _152_351 = (let _152_350 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _152_348 -> FStar_Util.Inl (_152_348)))
in (FStar_All.pipe_right _152_350 (fun _152_349 -> Some (_152_349))))
in (FStar_Syntax_Util.abs ys t _152_351)))
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

let _55_466 = (match ((let _152_362 = (FStar_Syntax_Subst.compress uv)
in _152_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _55_462 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _152_365 = (FStar_Util.string_of_int (p_pid prob))
in (let _152_364 = (FStar_Syntax_Print.term_to_string uv)
in (let _152_363 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _152_365 _152_364 _152_363))))
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
(let _152_374 = (FStar_Util.string_of_int pid)
in (let _152_373 = (let _152_372 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _152_372 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _152_374 _152_373)))
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
(let _152_387 = (FStar_Syntax_Util.mk_conj t f)
in Some (_152_387))
end))
in (

let _55_501 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_390 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _152_389 = (let _152_388 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _152_388 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _152_390 _152_389)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _152_400 = (let _152_398 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _152_398 FStar_Util.set_elements))
in (FStar_All.pipe_right _152_400 (FStar_Util.for_some (fun _55_510 -> (match (_55_510) with
| (uv, _55_509) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _152_407 = (let _152_406 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _152_405 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _152_406 _152_405)))
in Some (_152_407))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _55_525 = (occurs_check env wl uk t)
in (match (_55_525) with
| (occurs_ok, msg) -> begin
(let _152_413 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_152_413), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _55_543 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_535 _55_538 -> (match (((_55_535), (_55_538))) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _152_422 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _152_422)) then begin
((isect), (isect_set))
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _152_423 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_152_423)))
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
(let _152_438 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _152_438))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _152_441 = (FStar_Syntax_Subst.compress t)
in _152_441.FStar_Syntax_Syntax.n)) with
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
(let _152_477 = (head_matches env f g)
in (FStar_All.pipe_right _152_477 head_match))
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
(let _152_478 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _152_478 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_763), _55_767) -> begin
(let _152_479 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _152_479 head_match))
end
| (_55_770, FStar_Syntax_Syntax.Tm_refine (x, _55_773)) -> begin
(let _152_480 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _152_480 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_793), FStar_Syntax_Syntax.Tm_app (head', _55_798)) -> begin
(let _152_481 = (head_matches env head head')
in (FStar_All.pipe_right _152_481 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_804), _55_808) -> begin
(let _152_482 = (head_matches env head t2)
in (FStar_All.pipe_right _152_482 head_match))
end
| (_55_811, FStar_Syntax_Syntax.Tm_app (head, _55_814)) -> begin
(let _152_483 = (head_matches env t1 head)
in (FStar_All.pipe_right _152_483 head_match))
end
| _55_819 -> begin
(let _152_486 = (let _152_485 = (delta_depth_of_term env t1)
in (let _152_484 = (delta_depth_of_term env t2)
in ((_152_485), (_152_484))))
in MisMatch (_152_486))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let _55_829 = (FStar_Syntax_Util.head_and_args t)
in (match (_55_829) with
| (head, _55_828) -> begin
(match ((let _152_493 = (FStar_Syntax_Util.un_uinst head)
in _152_493.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (let _152_494 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _152_494 FStar_Option.isSome)) then begin
(let _152_496 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right _152_496 (fun _152_495 -> Some (_152_495))))
end else begin
None
end
end
| _55_833 -> begin
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
(match ((let _152_516 = (maybe_inline t1)
in (let _152_515 = (maybe_inline t2)
in ((_152_516), (_152_515))))) with
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

let _55_897 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _152_517 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_152_517))))
end
in (match (_55_897) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (_55_899) -> begin
(fail r)
end
| _55_902 -> begin
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
| T (_55_905) -> begin
_55_905
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_908) -> begin
_55_908
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let _55_914 = (FStar_Syntax_Util.type_u ())
in (match (_55_914) with
| (t, _55_913) -> begin
(let _152_588 = (new_uvar r binders t)
in (Prims.fst _152_588))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _152_593 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_593 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_923) -> begin
false
end
| _55_926 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((_55_936, imp), T (t, _55_941)) -> begin
((t), (imp))
end
| _55_946 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args)))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_951 -> (match (_55_951) with
| (t, _55_950) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _55_958 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _55_961 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_961) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, _55_976))::tcs) -> begin
(aux (((((

let _55_981 = x
in {FStar_Syntax_Syntax.ppname = _55_981.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_981.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_989 -> begin
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
in (let _152_655 = (decompose [] bs)
in ((rebuild), (matches), (_152_655)))))
end)))
end
| _55_998 -> begin
(

let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_1002 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t, _55_1008) -> begin
t
end
| _55_1012 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t, _55_1016) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_1020 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_55_1033, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let _55_1043 = (new_uvar r scope k)
in (match (_55_1043) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_1046 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _152_687 = (let _152_686 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _152_685 -> FStar_TypeChecker_Common.TProb (_152_685)) _152_686))
in ((T (((gi_xs), (mk_kind)))), (_152_687))))
end)))
end
| (_55_1049, _55_1051, C (_55_1053)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let _55_1141 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = _55_1071; FStar_Syntax_Syntax.pos = _55_1069; FStar_Syntax_Syntax.vars = _55_1067})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _55_1081), prob) -> begin
(let _152_700 = (let _152_699 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _152_698 -> C (_152_698)) _152_699))
in ((_152_700), ((prob)::[])))
end
| _55_1087 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = _55_1095; FStar_Syntax_Syntax.pos = _55_1093; FStar_Syntax_Syntax.vars = _55_1091})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _55_1105), prob) -> begin
(let _152_707 = (let _152_706 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _152_705 -> C (_152_705)) _152_706))
in ((_152_707), ((prob)::[])))
end
| _55_1111 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1113, _55_1115, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1121; FStar_Syntax_Syntax.pos = _55_1119; FStar_Syntax_Syntax.vars = _55_1117})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let _55_1132 = (let _152_713 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _152_713 FStar_List.unzip))
in (match (_55_1132) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _152_718 = (let _152_717 = (let _152_714 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _152_714 un_T))
in (let _152_716 = (let _152_715 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _152_715 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _152_717; FStar_Syntax_Syntax.effect_args = _152_716; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _152_718))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| _55_1135 -> begin
(

let _55_1138 = (sub_prob scope args q)
in (match (_55_1138) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_55_1141) with
| (tc, probs) -> begin
(

let _55_1154 = (match (q) with
| (Some (b), _55_1145, _55_1147) -> begin
(let _152_720 = (let _152_719 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_152_719)::args)
in ((Some (b)), ((b)::scope), (_152_720)))
end
| _55_1150 -> begin
((None), (scope), (args))
end)
in (match (_55_1154) with
| (bopt, scope, args) -> begin
(

let _55_1158 = (aux scope args qs)
in (match (_55_1158) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _152_723 = (let _152_722 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_152_722)
in (FStar_Syntax_Util.mk_conj_l _152_723))
end
| Some (b) -> begin
(let _152_727 = (let _152_726 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _152_725 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_152_726)::_152_725))
in (FStar_Syntax_Util.mk_conj_l _152_727))
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1186), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1191)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1205 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1211 _55_1215 -> (match (((_55_1211), (_55_1215))) with
| ((a1, _55_1210), (a2, _55_1214)) -> begin
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

let _55_1218 = p
in (let _152_749 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _152_748 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1218.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _152_749; FStar_TypeChecker_Common.relation = _55_1218.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _152_748; FStar_TypeChecker_Common.element = _55_1218.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1218.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1218.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1218.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1218.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1218.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _152_755 = (compress_tprob wl p)
in (FStar_All.pipe_right _152_755 (fun _152_754 -> FStar_TypeChecker_Common.TProb (_152_754))))
end
| FStar_TypeChecker_Common.CProb (_55_1225) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _152_760 = (compress_prob wl pr)
in (FStar_All.pipe_right _152_760 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _55_1235 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1235) with
| (lh, _55_1234) -> begin
(

let _55_1239 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1239) with
| (rh, _55_1238) -> begin
(

let _55_1295 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1241), FStar_Syntax_Syntax.Tm_uvar (_55_1244)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1260), _55_1263) -> begin
(

let _55_1267 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1267) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _55_1270 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _152_762 = (

let _55_1272 = tp
in (let _152_761 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1272.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1272.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1272.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _152_761; FStar_TypeChecker_Common.element = _55_1272.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1272.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1272.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1272.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1272.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1272.FStar_TypeChecker_Common.rank}))
in ((rank), (_152_762))))
end)
end))
end
| (_55_1275, FStar_Syntax_Syntax.Tm_uvar (_55_1277)) -> begin
(

let _55_1282 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1282) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _55_1285 -> begin
(let _152_764 = (

let _55_1286 = tp
in (let _152_763 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _55_1286.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _152_763; FStar_TypeChecker_Common.relation = _55_1286.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1286.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1286.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1286.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1286.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1286.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1286.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1286.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_152_764)))
end)
end))
end
| (_55_1289, _55_1291) -> begin
((rigid_rigid), (tp))
end)
in (match (_55_1295) with
| (rank, tp) -> begin
(let _152_766 = (FStar_All.pipe_right (

let _55_1296 = tp
in {FStar_TypeChecker_Common.pid = _55_1296.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1296.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1296.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1296.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1296.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1296.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1296.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1296.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1296.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _152_765 -> FStar_TypeChecker_Common.TProb (_152_765)))
in ((rank), (_152_766)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _152_768 = (FStar_All.pipe_right (

let _55_1300 = cp
in {FStar_TypeChecker_Common.pid = _55_1300.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1300.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1300.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1300.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1300.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1300.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1300.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1300.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1300.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _152_767 -> FStar_TypeChecker_Common.CProb (_152_767)))
in ((rigid_rigid), (_152_768)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _55_1307 probs -> (match (_55_1307) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _55_1315 = (rank wl hd)
in (match (_55_1315) with
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
| UDeferred (_55_1326) -> begin
_55_1326
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1329) -> begin
_55_1329
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1332) -> begin
_55_1332
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _55_1348 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1348) with
| (k, _55_1347) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1352 -> begin
false
end)
end)))))
end
| _55_1354 -> begin
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
| _55_1379 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _152_848 = (let _152_847 = (FStar_Syntax_Print.univ_to_string u1)
in (let _152_846 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _152_847 _152_846)))
in UFailed (_152_848))
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
| _55_1397 -> begin
(let _152_855 = (let _152_854 = (FStar_Syntax_Print.univ_to_string u1)
in (let _152_853 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _152_854 _152_853 msg)))
in UFailed (_152_855))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(let _152_858 = (let _152_857 = (FStar_Syntax_Print.univ_to_string u1)
in (let _152_856 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _152_857 _152_856)))
in (FStar_All.failwith _152_858))
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
(let _152_861 = (let _152_860 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _152_859 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _152_860 _152_859)))
in (try_umax_components u1 u2 _152_861))
end else begin
(let _152_862 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (_152_862))
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

let _55_1498 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_916 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _152_916))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _55_1505 = probs
in {attempting = tl; wl_deferred = _55_1505.wl_deferred; ctr = _55_1505.ctr; defer_ok = _55_1505.defer_ok; smt_ok = _55_1505.smt_ok; tcenv = _55_1505.tcenv})
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
| (None, _55_1520, _55_1522) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1526 -> begin
(

let _55_1535 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1532 -> (match (_55_1532) with
| (c, _55_1529, _55_1531) -> begin
(c < probs.ctr)
end))))
in (match (_55_1535) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _152_919 = (FStar_List.map (fun _55_1541 -> (match (_55_1541) with
| (_55_1538, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (_152_919))
end
| _55_1543 -> begin
(let _152_922 = (

let _55_1544 = probs
in (let _152_921 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1551 -> (match (_55_1551) with
| (_55_1547, _55_1549, y) -> begin
y
end))))
in {attempting = _152_921; wl_deferred = rest; ctr = _55_1544.ctr; defer_ok = _55_1544.defer_ok; smt_ok = _55_1544.smt_ok; tcenv = _55_1544.tcenv}))
in (solve env _152_922))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _152_928 = (solve_prob orig None [] wl)
in (solve env _152_928))
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
| _55_1586 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1594; FStar_Syntax_Syntax.pos = _55_1592; FStar_Syntax_Syntax.vars = _55_1590}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1606; FStar_Syntax_Syntax.pos = _55_1604; FStar_Syntax_Syntax.vars = _55_1602}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _55_1615 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1630 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _55_1635 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_944 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _152_944 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1640 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_948 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _152_948))
end else begin
()
end
in (

let _55_1644 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1644) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _55_1650 = (head_matches_delta env () t1 t2)
in (match (_55_1650) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1652) -> begin
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

let _55_1668 = (match (ts) with
| Some (t1, t2) -> begin
(let _152_954 = (FStar_Syntax_Subst.compress t1)
in (let _152_953 = (FStar_Syntax_Subst.compress t2)
in ((_152_954), (_152_953))))
end
| None -> begin
(let _152_956 = (FStar_Syntax_Subst.compress t1)
in (let _152_955 = (FStar_Syntax_Subst.compress t2)
in ((_152_956), (_152_955))))
end)
in (match (_55_1668) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _152_962 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _152_961 -> FStar_TypeChecker_Common.TProb (_152_961)) _152_962)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _152_969 = (let _152_968 = (let _152_965 = (let _152_964 = (let _152_963 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_152_963)))
in FStar_Syntax_Syntax.Tm_refine (_152_964))
in (FStar_Syntax_Syntax.mk _152_965 None t1.FStar_Syntax_Syntax.pos))
in (let _152_967 = (let _152_966 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_152_966)::[])
in ((_152_968), (_152_967))))
in Some (_152_969))
end
| (_55_1682, FStar_Syntax_Syntax.Tm_refine (x, _55_1685)) -> begin
(let _152_972 = (let _152_971 = (let _152_970 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_152_970)::[])
in ((t1), (_152_971)))
in Some (_152_972))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1691), _55_1695) -> begin
(let _152_975 = (let _152_974 = (let _152_973 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_152_973)::[])
in ((t2), (_152_974)))
in Some (_152_975))
end
| _55_1698 -> begin
(

let _55_1702 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1702) with
| (head1, _55_1701) -> begin
(match ((let _152_976 = (FStar_Syntax_Util.un_uinst head1)
in _152_976.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1708; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = _55_1704}) -> begin
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
| _55_1715 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1719) -> begin
(

let _55_1744 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _55_1730 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1730) with
| (u', _55_1729) -> begin
(match ((let _152_978 = (whnf env u')
in _152_978.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1733) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1737 -> begin
false
end)
end))
end
| _55_1739 -> begin
false
end)
end
| _55_1741 -> begin
false
end))))
in (match (_55_1744) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _55_1748 tps -> (match (_55_1748) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _152_983 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _152_983))) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1761 -> begin
None
end)
end))
in (match ((let _152_985 = (let _152_984 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_152_984), ([])))
in (make_lower_bound _152_985 lower_bounds))) with
| None -> begin
(

let _55_1763 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1773 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1770 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1770.wl_deferred; ctr = _55_1770.ctr; defer_ok = _55_1770.defer_ok; smt_ok = _55_1770.smt_ok; tcenv = _55_1770.tcenv})
in (let _152_986 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _152_986)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1775 = wl
in {attempting = sub_probs; wl_deferred = _55_1775.wl_deferred; ctr = _55_1775.ctr; defer_ok = _55_1775.defer_ok; smt_ok = _55_1775.smt_ok; tcenv = _55_1775.tcenv}))) with
| Success (_55_1778) -> begin
(

let wl = (

let _55_1780 = wl
in {attempting = rest; wl_deferred = _55_1780.wl_deferred; ctr = _55_1780.ctr; defer_ok = _55_1780.defer_ok; smt_ok = _55_1780.smt_ok; tcenv = _55_1780.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1786 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1789 -> begin
None
end)))
end))
end))
end
| _55_1791 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _55_1795 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_992 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _152_992))
end else begin
()
end
in (

let _55_1799 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1799) with
| (u, args) -> begin
(

let _55_1805 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (_55_1805) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _55_1814 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1814) with
| (h1, args1) -> begin
(

let _55_1818 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1818) with
| (h2, _55_1817) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _152_1004 = (let _152_1003 = (let _152_1002 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _152_1001 -> FStar_TypeChecker_Common.TProb (_152_1001)) _152_1002))
in (_152_1003)::[])
in Some (_152_1004))
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
(let _152_1008 = (let _152_1007 = (let _152_1006 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _152_1005 -> FStar_TypeChecker_Common.TProb (_152_1005)) _152_1006))
in (_152_1007)::[])
in Some (_152_1008))
end
end else begin
None
end
end
| _55_1830 -> begin
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
in (let _152_1015 = (let _152_1014 = (let _152_1013 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _152_1013))
in ((_152_1014), (m)))
in Some (_152_1015))))))
end))
end
| (_55_1852, FStar_Syntax_Syntax.Tm_refine (y, _55_1855)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1865), _55_1869) -> begin
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
| _55_1876 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1884) -> begin
(

let _55_1909 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _55_1895 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1895) with
| (u', _55_1894) -> begin
(match ((let _152_1017 = (whnf env u')
in _152_1017.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1898) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1902 -> begin
false
end)
end))
end
| _55_1904 -> begin
false
end)
end
| _55_1906 -> begin
false
end))))
in (match (_55_1909) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _55_1913 tps -> (match (_55_1913) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _152_1022 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _152_1022))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _55_1926 -> begin
None
end)
end))
in (match ((let _152_1024 = (let _152_1023 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_152_1023), ([])))
in (make_upper_bound _152_1024 upper_bounds))) with
| None -> begin
(

let _55_1928 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1938 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _55_1935 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1935.wl_deferred; ctr = _55_1935.ctr; defer_ok = _55_1935.defer_ok; smt_ok = _55_1935.smt_ok; tcenv = _55_1935.tcenv})
in (let _152_1025 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _152_1025)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1940 = wl
in {attempting = sub_probs; wl_deferred = _55_1940.wl_deferred; ctr = _55_1940.ctr; defer_ok = _55_1940.defer_ok; smt_ok = _55_1940.smt_ok; tcenv = _55_1940.tcenv}))) with
| Success (_55_1943) -> begin
(

let wl = (

let _55_1945 = wl
in {attempting = rest; wl_deferred = _55_1945.wl_deferred; ctr = _55_1945.ctr; defer_ok = _55_1945.defer_ok; smt_ok = _55_1945.smt_ok; tcenv = _55_1945.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1951 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1954 -> begin
None
end)))
end))
end))
end
| _55_1956 -> begin
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

let _55_1973 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1053 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _152_1053))
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

let _55_1987 = hd1
in (let _152_1054 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1987.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1987.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_1054}))
in (

let hd2 = (

let _55_1990 = hd2
in (let _152_1055 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1990.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1990.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_1055}))
in (

let prob = (let _152_1058 = (let _152_1057 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _152_1057 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _152_1056 -> FStar_TypeChecker_Common.TProb (_152_1056)) _152_1058))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _152_1059 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_152_1059)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux ((((hd1), (imp)))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _152_1061 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _152_1060 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _152_1061 _152_1060)))
in (

let _55_2002 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1063 = (FStar_Syntax_Print.term_to_string phi)
in (let _152_1062 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _152_1063 _152_1062)))
end else begin
()
end
in FStar_Util.Inl ((((prob)::sub_probs), (phi)))))
end
| fail -> begin
fail
end)))))))
end
| _55_2006 -> begin
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
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _152_1067 = (compress_tprob wl problem)
in (solve_t' env _152_1067 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _55_2034 = (head_matches_delta env wl t1 t2)
in (match (_55_2034) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (_55_2036), _55_2039) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_2052 -> begin
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
in (let _152_1096 = (let _152_1095 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _152_1095 t2))
in (FStar_Syntax_Util.mk_forall x _152_1096)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _152_1097 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _152_1097)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_2062, Some (t1, t2)) -> begin
(solve_t env (

let _55_2068 = problem
in {FStar_TypeChecker_Common.pid = _55_2068.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2068.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2068.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2068.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2068.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2068.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2068.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2068.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2071, None) -> begin
(

let _55_2074 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1101 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1100 = (FStar_Syntax_Print.tag_of_term t1)
in (let _152_1099 = (FStar_Syntax_Print.term_to_string t2)
in (let _152_1098 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _152_1101 _152_1100 _152_1099 _152_1098)))))
end else begin
()
end
in (

let _55_2078 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_2078) with
| (head1, args1) -> begin
(

let _55_2081 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2081) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _152_1106 = (let _152_1105 = (FStar_Syntax_Print.term_to_string head1)
in (let _152_1104 = (args_to_string args1)
in (let _152_1103 = (FStar_Syntax_Print.term_to_string head2)
in (let _152_1102 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _152_1105 _152_1104 _152_1103 _152_1102)))))
in (giveup env _152_1106 orig))
end else begin
if ((nargs = (Prims.parse_int "0")) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _152_1107 = (solve_prob orig None [] wl)
in (solve env _152_1107))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _55_2091 = (base_and_refinement env wl t1)
in (match (_55_2091) with
| (base1, refinement1) -> begin
(

let _55_2094 = (base_and_refinement env wl t2)
in (match (_55_2094) with
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

let subprobs = (FStar_List.map2 (fun _55_2107 _55_2111 -> (match (((_55_2107), (_55_2111))) with
| ((a, _55_2106), (a', _55_2110)) -> begin
(let _152_1111 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _152_1110 -> FStar_TypeChecker_Common.TProb (_152_1110)) _152_1111))
end)) args1 args2)
in (

let formula = (let _152_1113 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _152_1113))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_2117 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _55_2120 = problem
in {FStar_TypeChecker_Common.pid = _55_2120.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_2120.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_2120.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2120.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2120.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2120.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2120.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2120.FStar_TypeChecker_Common.rank}) wl)))
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

let _55_2139 = p
in (match (_55_2139) with
| (((u, k), xs, c), ps, (h, _55_2136, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2145 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2145) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _152_1128 = (h gs_xs)
in (let _152_1127 = (let _152_1126 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _152_1124 -> FStar_Util.Inl (_152_1124)))
in (FStar_All.pipe_right _152_1126 (fun _152_1125 -> Some (_152_1125))))
in (FStar_Syntax_Util.abs xs _152_1128 _152_1127)))
in (

let _55_2147 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1135 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _152_1134 = (FStar_Syntax_Print.comp_to_string c)
in (let _152_1133 = (FStar_Syntax_Print.term_to_string im)
in (let _152_1132 = (FStar_Syntax_Print.tag_of_term im)
in (let _152_1131 = (let _152_1129 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _152_1129 (FStar_String.concat ", ")))
in (let _152_1130 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _152_1135 _152_1134 _152_1133 _152_1132 _152_1131 _152_1130)))))))
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

let _55_2173 = p
in (match (_55_2173) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2178 = (FStar_List.nth ps i)
in (match (_55_2178) with
| (pi, _55_2177) -> begin
(

let _55_2182 = (FStar_List.nth xs i)
in (match (_55_2182) with
| (xi, _55_2181) -> begin
(

let rec gs = (fun k -> (

let _55_2187 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2187) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, _55_2195))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _55_2201 = (new_uvar r xs k_a)
in (match (_55_2201) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let _55_2207 = (aux subst tl)
in (match (_55_2207) with
| (gi_xs', gi_ps') -> begin
(let _152_1165 = (let _152_1162 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_152_1162)::gi_xs')
in (let _152_1164 = (let _152_1163 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_152_1163)::gi_ps')
in ((_152_1165), (_152_1164))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _152_1166 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _152_1166)) then begin
None
end else begin
(

let _55_2211 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2211) with
| (g_xs, _55_2210) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _152_1171 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _152_1170 = (let _152_1169 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _152_1167 -> FStar_Util.Inl (_152_1167)))
in (FStar_All.pipe_right _152_1169 (fun _152_1168 -> Some (_152_1168))))
in (FStar_Syntax_Util.abs xs _152_1171 _152_1170)))
in (

let sub = (let _152_1177 = (let _152_1176 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _152_1175 = (let _152_1174 = (FStar_List.map (fun _55_2219 -> (match (_55_2219) with
| (_55_2215, _55_2217, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _152_1174))
in (mk_problem (p_scope orig) orig _152_1176 (p_rel orig) _152_1175 None "projection")))
in (FStar_All.pipe_left (fun _152_1172 -> FStar_TypeChecker_Common.TProb (_152_1172)) _152_1177))
in (

let _55_2221 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1179 = (FStar_Syntax_Print.term_to_string proj)
in (let _152_1178 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _152_1179 _152_1178)))
end else begin
()
end
in (

let wl = (let _152_1181 = (let _152_1180 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_152_1180))
in (solve_prob orig _152_1181 ((TERM (((u), (proj))))::[]) wl))
in (let _152_1183 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _152_1182 -> Some (_152_1182)) _152_1183)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let _55_2236 = lhs
in (match (_55_2236) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _55_2241 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2241) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _152_1207 = (let _152_1206 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_152_1206)))
in Some (_152_1207))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _152_1213 = (let _152_1212 = (FStar_Syntax_Subst.compress k)
in _152_1212.FStar_Syntax_Syntax.n)
in ((_152_1213), (args)))) with
| (_55_2247, []) -> begin
(let _152_1215 = (let _152_1214 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_152_1214)))
in Some (_152_1215))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _55_2264 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2264) with
| (uv, uv_args) -> begin
(match ((let _152_1216 = (FStar_Syntax_Subst.compress uv)
in _152_1216.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2267) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2273 -> (let _152_1222 = (let _152_1221 = (let _152_1220 = (let _152_1219 = (let _152_1218 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_1218 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _152_1219))
in (Prims.fst _152_1220))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _152_1221))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _152_1222)))))
in (

let c = (let _152_1226 = (let _152_1225 = (let _152_1224 = (let _152_1223 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_1223 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _152_1224))
in (Prims.fst _152_1225))
in (FStar_Syntax_Syntax.mk_Total _152_1226))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _152_1232 = (let _152_1231 = (let _152_1230 = (let _152_1229 = (let _152_1228 = (let _152_1227 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _152_1227 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _152_1228))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _152_1229))
in FStar_Util.Inl (_152_1230))
in Some (_152_1231))
in (FStar_Syntax_Util.abs scope k' _152_1232))
in (

let _55_2279 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some (((xs), (c))))))))
end)
end
| _55_2282 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2288) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _152_1234 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _152_1234 (fun _152_1233 -> Some (_152_1233))))
end else begin
if (n_xs < n_args) then begin
(

let _55_2294 = (FStar_Util.first_N n_xs args)
in (match (_55_2294) with
| (args, rest) -> begin
(

let _55_2297 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2297) with
| (xs, c) -> begin
(let _152_1236 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _152_1236 (fun _55_2300 -> (match (_55_2300) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end else begin
(

let _55_2303 = (FStar_Util.first_N n_args xs)
in (match (_55_2303) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) None k.FStar_Syntax_Syntax.pos)
in (let _152_1239 = (let _152_1237 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _152_1237))
in (FStar_All.pipe_right _152_1239 (fun _152_1238 -> Some (_152_1238)))))
end))
end
end))
end
| _55_2306 -> begin
(let _152_1243 = (let _152_1242 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _152_1241 = (FStar_Syntax_Print.term_to_string k)
in (let _152_1240 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _152_1242 _152_1241 _152_1240))))
in (FStar_All.failwith _152_1243))
end))
in (let _152_1281 = (elim k_uv ps)
in (FStar_Util.bind_opt _152_1281 (fun _55_2309 -> (match (_55_2309) with
| (xs, c) -> begin
(let _152_1280 = (let _152_1279 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_152_1279)))
in Some (_152_1280))
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
| Failed (_55_2317) -> begin
(

let _55_2319 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _55_2327 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _55_2337 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2337) with
| (hd, _55_2336) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2348 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _55_2350 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1292 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _152_1292))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _152_1296 = (let _152_1295 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _152_1295 Prims.fst))
in (FStar_All.pipe_right _152_1296 FStar_Syntax_Free.names))
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

let _55_2363 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (_55_2363) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _152_1298 = (let _152_1297 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _152_1297))
in (giveup_or_defer orig _152_1298))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _152_1299 = (subterms args_lhs)
in (imitate' orig env wl _152_1299))
end else begin
(

let _55_2364 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1302 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1301 = (names_to_string fvs1)
in (let _152_1300 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _152_1302 _152_1301 _152_1300))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2368 -> begin
(let _152_1303 = (sn_binders env vars)
in (u_abs k_uv _152_1303 t2))
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

let _55_2371 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1306 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1305 = (names_to_string fvs1)
in (let _152_1304 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _152_1306 _152_1305 _152_1304))))
end else begin
()
end
in (let _152_1307 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _152_1307 (~- ((Prims.parse_int "1"))))))
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
if (let _152_1308 = (FStar_Syntax_Free.names t1)
in (check_head _152_1308 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _55_2376 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1309 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _152_1309 (if (im_ok < (Prims.parse_int "0")) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _152_1310 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _152_1310 im_ok))))
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

let force_quasi_pattern = (fun xs_opt _55_2388 -> (match (_55_2388) with
| (t, u, k, args) -> begin
(

let _55_2392 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2392) with
| (all_formals, _55_2391) -> begin
(

let _55_2393 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2406 -> (match (_55_2406) with
| (x, imp) -> begin
(let _152_1332 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_152_1332), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _55_2412 = (FStar_Syntax_Util.type_u ())
in (match (_55_2412) with
| (t, _55_2411) -> begin
(let _152_1333 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _152_1333))
end))
in (

let _55_2416 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2416) with
| (t', tm_u1) -> begin
(

let _55_2423 = (destruct_flex_t t')
in (match (_55_2423) with
| (_55_2418, u1, k1, _55_2422) -> begin
(

let sol = (let _152_1335 = (let _152_1334 = (u_abs k all_formals t')
in ((((u), (k))), (_152_1334)))
in TERM (_152_1335))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2442 -> (match (_55_2442) with
| (x, _55_2441) -> begin
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
(let _152_1337 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _152_1337 formals tl))
end)
end)
end)
end
| _55_2446 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _152_1338 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _152_1338 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _55_2453 _55_2458 r -> (match (((_55_2453), (_55_2458))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _152_1347 = (solve_prob orig None [] wl)
in (solve env _152_1347))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _55_2463 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1352 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _152_1351 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _152_1350 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _152_1349 = (FStar_Syntax_Print.term_to_string k1)
in (let _152_1348 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _152_1352 _152_1351 _152_1350 _152_1349 _152_1348))))))
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
(let _152_1362 = (let _152_1361 = (FStar_Syntax_Print.term_to_string k)
in (let _152_1360 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _152_1359 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _152_1361 _152_1360 _152_1359))))
in (FStar_All.failwith _152_1362))
end)))
in (

let _55_2505 = (

let _55_2473 = (let _152_1363 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals _152_1363))
in (match (_55_2473) with
| (bs, k1') -> begin
(

let _55_2476 = (let _152_1364 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals _152_1364))
in (match (_55_2476) with
| (cs, k2') -> begin
(

let k1'_xs = (let _152_1365 = (subst_of_list k1 bs args1)
in (FStar_Syntax_Subst.subst _152_1365 k1'))
in (

let k2'_ys = (let _152_1366 = (subst_of_list k2 cs args2)
in (FStar_Syntax_Subst.subst _152_1366 k2'))
in (

let sub_prob = (let _152_1368 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _152_1367 -> FStar_TypeChecker_Common.TProb (_152_1367)) _152_1368))
in (match ((let _152_1372 = (let _152_1369 = (FStar_Syntax_Subst.compress k1')
in _152_1369.FStar_Syntax_Syntax.n)
in (let _152_1371 = (let _152_1370 = (FStar_Syntax_Subst.compress k2')
in _152_1370.FStar_Syntax_Syntax.n)
in ((_152_1372), (_152_1371))))) with
| (FStar_Syntax_Syntax.Tm_type (_55_2481), _55_2484) -> begin
((k1'), ((sub_prob)::[]))
end
| (_55_2487, FStar_Syntax_Syntax.Tm_type (_55_2489)) -> begin
((k2'), ((sub_prob)::[]))
end
| _55_2493 -> begin
(

let _55_2497 = (FStar_Syntax_Util.type_u ())
in (match (_55_2497) with
| (t, _55_2496) -> begin
(

let _55_2501 = (new_uvar r zs t)
in (match (_55_2501) with
| (k_zs, _55_2500) -> begin
(

let kprob = (let _152_1374 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _152_1373 -> FStar_TypeChecker_Common.TProb (_152_1373)) _152_1374))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end))))
end))
end))
in (match (_55_2505) with
| (k_u', sub_probs) -> begin
(

let _55_2509 = (let _152_1380 = (let _152_1375 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _152_1375))
in (let _152_1379 = (let _152_1376 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _152_1376))
in (let _152_1378 = (let _152_1377 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _152_1377))
in ((_152_1380), (_152_1379), (_152_1378)))))
in (match (_55_2509) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _55_2513 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_55_2513) with
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

let _55_2519 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_55_2519) with
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

let solve_one_pat = (fun _55_2527 _55_2532 -> (match (((_55_2527), (_55_2532))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _55_2533 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1386 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1385 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _152_1386 _152_1385)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _55_2538 _55_2542 -> (match (((_55_2538), (_55_2542))) with
| ((a, _55_2537), (t2, _55_2541)) -> begin
(let _152_1391 = (let _152_1389 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _152_1389 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _152_1391 (fun _152_1390 -> FStar_TypeChecker_Common.TProb (_152_1390))))
end)) xs args2)
in (

let guard = (let _152_1393 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _152_1393))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _55_2552 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_55_2552) with
| (occurs_ok, _55_2551) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _152_1395 = (let _152_1394 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_152_1394)))
in TERM (_152_1395))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _55_2563 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_55_2563) with
| (sol, (_55_2558, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2565 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _152_1396 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _152_1396))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2570 -> begin
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

let _55_2575 = lhs
in (match (_55_2575) with
| (t1, u1, k1, args1) -> begin
(

let _55_2580 = rhs
in (match (_55_2580) with
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
| _55_2598 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _55_2602 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_55_2602) with
| (sol, _55_2601) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _55_2604 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _152_1397 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _152_1397))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2609 -> begin
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
(let _152_1398 = (solve_prob orig None [] wl)
in (solve env _152_1398))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _152_1399 = (solve_prob orig None [] wl)
in (solve env _152_1399))
end else begin
(

let _55_2613 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _152_1400 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _152_1400))
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _55_2618 _55_2621 -> (match (((_55_2618), (_55_2621))) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _55_2628 = (FStar_Util.first_N n bs)
in (match (_55_2628) with
| (bs, rest) -> begin
(let _152_1430 = (mk_cod rest)
in ((bs), (_152_1430)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _152_1434 = (let _152_1431 = (mk_cod1 [])
in ((bs1), (_152_1431)))
in (let _152_1433 = (let _152_1432 = (mk_cod2 [])
in ((bs2), (_152_1432)))
in ((_152_1434), (_152_1433))))
end else begin
if (l1 > l2) then begin
(let _152_1437 = (curry l2 bs1 mk_cod1)
in (let _152_1436 = (let _152_1435 = (mk_cod2 [])
in ((bs2), (_152_1435)))
in ((_152_1437), (_152_1436))))
end else begin
(let _152_1440 = (let _152_1438 = (mk_cod1 [])
in ((bs1), (_152_1438)))
in (let _152_1439 = (curry l1 bs2 mk_cod2)
in ((_152_1440), (_152_1439))))
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
(let _152_1445 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _152_1445))
end))
in (

let _55_2671 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_55_2671) with
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
in (let _152_1452 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _152_1451 -> FStar_TypeChecker_Common.CProb (_152_1451)) _152_1452)))))))
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

let _55_2701 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (_55_2701) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _152_1467 = (let _152_1466 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _152_1465 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _152_1466 problem.FStar_TypeChecker_Common.relation _152_1465 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _152_1464 -> FStar_TypeChecker_Common.TProb (_152_1464)) _152_1467))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2720) -> begin
true
end
| _55_2723 -> begin
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
in (match ((let _152_1473 = (maybe_eta t1)
in (let _152_1472 = (maybe_eta t2)
in ((_152_1473), (_152_1472))))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let _55_2732 = problem
in {FStar_TypeChecker_Common.pid = _55_2732.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2732.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2732.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2732.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2732.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2732.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2732.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2732.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
if ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ)) then begin
(let _152_1474 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _152_1474 t_abs wl))
end else begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end
end
| _55_2743 -> begin
(FStar_All.failwith "Impossible: at least one side is an abstraction")
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2745), FStar_Syntax_Syntax.Tm_refine (_55_2748)) -> begin
(

let _55_2753 = (as_refinement env wl t1)
in (match (_55_2753) with
| (x1, phi1) -> begin
(

let _55_2756 = (as_refinement env wl t2)
in (match (_55_2756) with
| (x2, phi2) -> begin
(

let base_prob = (let _152_1476 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _152_1475 -> FStar_TypeChecker_Common.TProb (_152_1475)) _152_1476))
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

let mk_imp = (fun imp phi1 phi2 -> (let _152_1493 = (imp phi1 phi2)
in (FStar_All.pipe_right _152_1493 (guard_on_element problem x1))))
in (

let fallback = (fun _55_2768 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _152_1496 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _152_1496 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _152_1500 = (let _152_1499 = (let _152_1498 = (FStar_Syntax_Syntax.mk_binder x1)
in (_152_1498)::(p_scope orig))
in (mk_problem _152_1499 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _152_1497 -> FStar_TypeChecker_Common.TProb (_152_1497)) _152_1500))
in (match ((solve env (

let _55_2773 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2773.ctr; defer_ok = false; smt_ok = _55_2773.smt_ok; tcenv = _55_2773.tcenv}))) with
| Failed (_55_2776) -> begin
(fallback ())
end
| Success (_55_2779) -> begin
(

let guard = (let _152_1503 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _152_1502 = (let _152_1501 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _152_1501 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _152_1503 _152_1502)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _55_2783 = wl
in {attempting = _55_2783.attempting; wl_deferred = _55_2783.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _55_2783.defer_ok; smt_ok = _55_2783.smt_ok; tcenv = _55_2783.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _152_1505 = (destruct_flex_t t1)
in (let _152_1504 = (destruct_flex_t t2)
in (flex_flex orig _152_1505 _152_1504)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _152_1506 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _152_1506 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let _55_2954 = problem
in {FStar_TypeChecker_Common.pid = _55_2954.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2954.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2954.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2954.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2954.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2954.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2954.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2954.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2954.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in if (let _152_1507 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _152_1507)) then begin
(let _152_1510 = (FStar_All.pipe_left (fun _152_1508 -> FStar_TypeChecker_Common.TProb (_152_1508)) (

let _55_2980 = problem
in {FStar_TypeChecker_Common.pid = _55_2980.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2980.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2980.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2980.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2980.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2980.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2980.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2980.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2980.FStar_TypeChecker_Common.rank}))
in (let _152_1509 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _152_1510 _152_1509 t2 wl)))
end else begin
(

let _55_2984 = (base_and_refinement env wl t2)
in (match (_55_2984) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _152_1513 = (FStar_All.pipe_left (fun _152_1511 -> FStar_TypeChecker_Common.TProb (_152_1511)) (

let _55_2986 = problem
in {FStar_TypeChecker_Common.pid = _55_2986.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2986.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2986.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2986.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2986.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2986.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2986.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2986.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2986.FStar_TypeChecker_Common.rank}))
in (let _152_1512 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _152_1513 _152_1512 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _55_2992 = y
in {FStar_Syntax_Syntax.ppname = _55_2992.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2992.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _152_1515 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _152_1514 -> FStar_TypeChecker_Common.TProb (_152_1514)) _152_1515))
in (

let guard = (let _152_1516 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _152_1516 impl))
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

let _55_3025 = (base_and_refinement env wl t1)
in (match (_55_3025) with
| (t_base, _55_3024) -> begin
(solve_t env (

let _55_3026 = problem
in {FStar_TypeChecker_Common.pid = _55_3026.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_3026.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3026.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3026.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3026.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3026.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3026.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3026.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_3029), _55_3032) -> begin
(

let t2 = (let _152_1517 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _152_1517))
in (solve_t env (

let _55_3035 = problem
in {FStar_TypeChecker_Common.pid = _55_3035.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3035.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3035.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_3035.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3035.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3035.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3035.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3035.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3035.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_3038, FStar_Syntax_Syntax.Tm_refine (_55_3040)) -> begin
(

let t1 = (let _152_1518 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _152_1518))
in (solve_t env (

let _55_3044 = problem
in {FStar_TypeChecker_Common.pid = _55_3044.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_3044.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3044.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3044.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3044.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3044.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3044.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3044.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3044.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _152_1519 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _152_1519 Prims.fst))
in (

let head2 = (let _152_1520 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _152_1520 Prims.fst))
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
(let _152_1522 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _152_1521 -> Some (_152_1521)) _152_1522))
end
in (let _152_1523 = (solve_prob orig guard [] wl)
in (solve env _152_1523)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_3125, _55_3127), _55_3131) -> begin
(solve_t' env (

let _55_3133 = problem
in {FStar_TypeChecker_Common.pid = _55_3133.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_3133.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3133.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3133.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3133.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3133.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3133.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3133.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3133.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_3136, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_3139, _55_3141)) -> begin
(solve_t' env (

let _55_3145 = problem
in {FStar_TypeChecker_Common.pid = _55_3145.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3145.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3145.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_3145.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3145.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3145.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3145.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3145.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3145.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _152_1526 = (let _152_1525 = (FStar_Syntax_Print.tag_of_term t1)
in (let _152_1524 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _152_1525 _152_1524)))
in (FStar_All.failwith _152_1526))
end
| _55_3184 -> begin
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

let _55_3201 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _55_3206 _55_3210 -> (match (((_55_3206), (_55_3210))) with
| ((a1, _55_3205), (a2, _55_3209)) -> begin
(let _152_1541 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _152_1540 -> FStar_TypeChecker_Common.TProb (_152_1540)) _152_1541))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _152_1543 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _152_1543))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _55_3222))::[] -> begin
wp1
end
| _55_3226 -> begin
(let _152_1551 = (let _152_1550 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _152_1550))
in (FStar_All.failwith _152_1551))
end)
in (

let c1 = (let _152_1554 = (let _152_1553 = (let _152_1552 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _152_1552))
in (_152_1553)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _152_1554; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3234 -> begin
false
end))))
in (

let _55_3255 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, _55_3240))::_55_3237, ((wp2, _55_3247))::_55_3244) -> begin
((wp1), (wp2))
end
| _55_3252 -> begin
(let _152_1558 = (let _152_1557 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _152_1556 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _152_1557 _152_1556)))
in (FStar_All.failwith _152_1558))
end)
in (match (_55_3255) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _152_1559 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _152_1559 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _55_3257 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _152_1569 = (let _152_1568 = (let _152_1567 = (let _152_1561 = (let _152_1560 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_152_1560)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _152_1561 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _152_1566 = (let _152_1565 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _152_1564 = (let _152_1563 = (let _152_1562 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_1562))
in (_152_1563)::[])
in (_152_1565)::_152_1564))
in ((_152_1567), (_152_1566))))
in FStar_Syntax_Syntax.Tm_app (_152_1568))
in (FStar_Syntax_Syntax.mk _152_1569 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _152_1581 = (let _152_1580 = (let _152_1579 = (let _152_1571 = (let _152_1570 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_152_1570)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _152_1571 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _152_1578 = (let _152_1577 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _152_1576 = (let _152_1575 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _152_1574 = (let _152_1573 = (let _152_1572 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_1572))
in (_152_1573)::[])
in (_152_1575)::_152_1574))
in (_152_1577)::_152_1576))
in ((_152_1579), (_152_1578))))
in FStar_Syntax_Syntax.Tm_app (_152_1580))
in (FStar_Syntax_Syntax.mk _152_1581 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _152_1583 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _152_1582 -> FStar_TypeChecker_Common.TProb (_152_1582)) _152_1583))
in (

let wl = (let _152_1587 = (let _152_1586 = (let _152_1585 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _152_1585 g))
in (FStar_All.pipe_left (fun _152_1584 -> Some (_152_1584)) _152_1586))
in (solve_prob orig _152_1587 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _152_1588 = (solve_prob orig None [] wl)
in (solve env _152_1588))
end else begin
(

let _55_3262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1590 = (FStar_Syntax_Print.comp_to_string c1)
in (let _152_1589 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _152_1590 (rel_to_string problem.FStar_TypeChecker_Common.relation) _152_1589)))
end else begin
()
end
in (

let _55_3266 = (let _152_1592 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _152_1591 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_152_1592), (_152_1591))))
in (match (_55_3266) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, _55_3269), FStar_Syntax_Syntax.Total (t2, _55_3274)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _152_1593 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _152_1593 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3279), FStar_Syntax_Syntax.Total (_55_3282)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _152_1594 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _152_1594 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _152_1597 = (

let _55_3328 = problem
in (let _152_1596 = (let _152_1595 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _152_1595))
in {FStar_TypeChecker_Common.pid = _55_3328.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _152_1596; FStar_TypeChecker_Common.relation = _55_3328.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3328.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3328.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3328.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3328.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3328.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3328.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3328.FStar_TypeChecker_Common.rank}))
in (solve_c env _152_1597 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _152_1600 = (

let _55_3344 = problem
in (let _152_1599 = (let _152_1598 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _152_1598))
in {FStar_TypeChecker_Common.pid = _55_3344.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3344.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3344.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _152_1599; FStar_TypeChecker_Common.element = _55_3344.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3344.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3344.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3344.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3344.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3344.FStar_TypeChecker_Common.rank}))
in (solve_c env _152_1600 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3347), FStar_Syntax_Syntax.Comp (_55_3350)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _152_1601 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _152_1601 wl))
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

let _55_3357 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _152_1602 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _152_1602))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _152_1607 = (let _152_1606 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _152_1605 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _152_1606 _152_1605)))
in (giveup env _152_1607 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _152_1611 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3377 -> (match (_55_3377) with
| (_55_3367, _55_3369, u, _55_3372, _55_3374, _55_3376) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _152_1611 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3384 -> begin
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

let carry = (let _152_1617 = (FStar_List.map (fun _55_3392 -> (match (_55_3392) with
| (_55_3390, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _152_1617 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3401; FStar_TypeChecker_Env.implicits = _55_3399} -> begin
true
end
| _55_3406 -> begin
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
| _55_3424 -> begin
(FStar_All.failwith "impossible")
end)
in (let _152_1638 = (

let _55_3426 = g
in (let _152_1637 = (let _152_1636 = (let _152_1635 = (let _152_1629 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_1629)::[])
in (let _152_1634 = (let _152_1633 = (let _152_1632 = (let _152_1630 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _152_1630 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _152_1632 (fun _152_1631 -> FStar_Util.Inl (_152_1631))))
in Some (_152_1633))
in (FStar_Syntax_Util.abs _152_1635 f _152_1634)))
in (FStar_All.pipe_left (fun _152_1628 -> FStar_TypeChecker_Common.NonTrivial (_152_1628)) _152_1636))
in {FStar_TypeChecker_Env.guard_f = _152_1637; FStar_TypeChecker_Env.deferred = _55_3426.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3426.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3426.FStar_TypeChecker_Env.implicits}))
in Some (_152_1638)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3433 = g
in (let _152_1649 = (let _152_1648 = (let _152_1647 = (let _152_1646 = (let _152_1645 = (let _152_1644 = (FStar_Syntax_Syntax.as_arg e)
in (_152_1644)::[])
in ((f), (_152_1645)))
in FStar_Syntax_Syntax.Tm_app (_152_1646))
in (FStar_Syntax_Syntax.mk _152_1647 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _152_1643 -> FStar_TypeChecker_Common.NonTrivial (_152_1643)) _152_1648))
in {FStar_TypeChecker_Env.guard_f = _152_1649; FStar_TypeChecker_Env.deferred = _55_3433.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3433.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3433.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3438) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _152_1656 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_152_1656))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3456 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _152_1679 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _152_1679; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _55_3483 = g
in (let _152_1694 = (let _152_1693 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _152_1693 (fun _152_1692 -> FStar_TypeChecker_Common.NonTrivial (_152_1692))))
in {FStar_TypeChecker_Env.guard_f = _152_1694; FStar_TypeChecker_Env.deferred = _55_3483.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3483.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3483.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _152_1702 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _152_1701 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _152_1702 (rel_to_string rel) _152_1701)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _152_1713 = (let _152_1712 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _152_1711 -> Some (_152_1711)) _152_1712))
in (FStar_Syntax_Syntax.new_bv _152_1713 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _152_1717 = (let _152_1715 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _152_1714 -> Some (_152_1714)) _152_1715))
in (let _152_1716 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _152_1717 _152_1716)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _55_3503 = probs
in {attempting = _55_3503.attempting; wl_deferred = _55_3503.wl_deferred; ctr = _55_3503.ctr; defer_ok = false; smt_ok = _55_3503.smt_ok; tcenv = _55_3503.tcenv})
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

let _55_3510 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _55_3516 = (FStar_Unionfind.rollback tx)
in (

let _55_3518 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _152_1729 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _152_1729))
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

let _55_3525 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _152_1734 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _152_1734))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _55_3528 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _152_1735 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _152_1735))
end else begin
()
end
in (

let f = (match ((let _152_1736 = (FStar_Syntax_Util.unmeta f)
in _152_1736.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3533 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _55_3535 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3535.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3535.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3535.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _152_1748 = (let _152_1747 = (let _152_1746 = (let _152_1745 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _152_1745 (fun _152_1744 -> FStar_TypeChecker_Common.NonTrivial (_152_1744))))
in {FStar_TypeChecker_Env.guard_f = _152_1746; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _152_1747))
in (FStar_All.pipe_left (fun _152_1743 -> Some (_152_1743)) _152_1748))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _55_3546 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1756 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1755 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _152_1756 _152_1755)))
end else begin
()
end
in (

let prob = (let _152_1759 = (let _152_1758 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _152_1758))
in (FStar_All.pipe_left (fun _152_1757 -> FStar_TypeChecker_Common.TProb (_152_1757)) _152_1759))
in (

let g = (let _152_1761 = (solve_and_commit env (singleton env prob) (fun _55_3549 -> None))
in (FStar_All.pipe_left (with_guard env prob) _152_1761))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _152_1771 = (let _152_1770 = (let _152_1769 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _152_1768 = (FStar_TypeChecker_Env.get_range env)
in ((_152_1769), (_152_1768))))
in FStar_Syntax_Syntax.Error (_152_1770))
in (Prims.raise _152_1771))
end
| Some (g) -> begin
(

let _55_3558 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1774 = (FStar_Syntax_Print.term_to_string t1)
in (let _152_1773 = (FStar_Syntax_Print.term_to_string t2)
in (let _152_1772 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _152_1774 _152_1773 _152_1772))))
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

let _55_3564 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1784 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _152_1783 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _152_1784 _152_1783)))
end else begin
()
end
in (

let _55_3569 = (

let rel = FStar_TypeChecker_Common.SUB
in (new_t_prob env t1 rel t2))
in (match (_55_3569) with
| (prob, x) -> begin
(

let g = (let _152_1786 = (solve_and_commit env (singleton' env prob smt_ok) (fun _55_3570 -> None))
in (FStar_All.pipe_left (with_guard env prob) _152_1786))
in (

let _55_3573 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _152_1790 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _152_1789 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _152_1788 = (let _152_1787 = (FStar_Util.must g)
in (guard_to_string env _152_1787))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _152_1790 _152_1789 _152_1788))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (let _152_1806 = (FStar_TypeChecker_Env.get_range env)
in (let _152_1805 = (FStar_TypeChecker_Errors.basic_type_error env (Some (e)) t2 t1)
in (FStar_TypeChecker_Errors.report _152_1806 _152_1805))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _55_3585 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1814 = (FStar_Syntax_Print.comp_to_string c1)
in (let _152_1813 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _152_1814 _152_1813)))
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

let prob = (let _152_1817 = (let _152_1816 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _152_1816 "sub_comp"))
in (FStar_All.pipe_left (fun _152_1815 -> FStar_TypeChecker_Common.CProb (_152_1815)) _152_1817))
in (let _152_1819 = (solve_and_commit env (singleton env prob) (fun _55_3589 -> None))
in (FStar_All.pipe_left (with_guard env prob) _152_1819))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _55_3598 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _152_1837 = (let _152_1836 = (let _152_1835 = (let _152_1833 = (FStar_Syntax_Print.univ_to_string u1)
in (let _152_1832 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _152_1833 _152_1832 msg)))
in (let _152_1834 = (FStar_TypeChecker_Env.get_range env)
in ((_152_1835), (_152_1834))))
in FStar_Syntax_Syntax.Error (_152_1836))
in (Prims.raise _152_1837)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let _55_3614 = hd
in (match (_55_3614) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
(((uv'), ((u1)::lower_bounds)))::tl
end else begin
(let _152_1844 = (insert uv u1 tl)
in (hd)::_152_1844)
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
(let _152_1849 = (insert uv u1 out)
in (group_by _152_1849 rest))
end)
end
| _55_3629 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _55_3631 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3634 -> begin
(

let wl = (

let _55_3635 = (empty_worklist env)
in {attempting = _55_3635.attempting; wl_deferred = _55_3635.wl_deferred; ctr = _55_3635.ctr; defer_ok = true; smt_ok = _55_3635.smt_ok; tcenv = _55_3635.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3640 -> (match (_55_3640) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3645 -> begin
(match ((solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3655 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3660 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _55_3667 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3667) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3671 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3671) with
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
| USolved (_55_3673) -> begin
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

let _55_3677 = (empty_worklist env)
in {attempting = _55_3677.attempting; wl_deferred = _55_3677.wl_deferred; ctr = _55_3677.ctr; defer_ok = false; smt_ok = _55_3677.smt_ok; tcenv = _55_3677.tcenv})
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
| _55_3692 -> begin
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

let _55_3697 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _55_3704 -> (match (_55_3704) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _55_3707 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_1870 = (wl_to_string wl)
in (let _152_1869 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _152_1870 _152_1869)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _55_3711 = g
in {FStar_TypeChecker_Env.guard_f = _55_3711.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3711.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3711.FStar_TypeChecker_Env.implicits})
end
| _55_3714 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _55_3716 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3718 = g
in {FStar_TypeChecker_Env.guard_f = _55_3718.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3718.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3718.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _55_3735 = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _55_3727 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) then begin
(let _152_1887 = (FStar_TypeChecker_Env.get_range env)
in (let _152_1886 = (let _152_1885 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _152_1885))
in (FStar_TypeChecker_Errors.diag _152_1887 _152_1886)))
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

let _55_3733 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _152_1890 = (FStar_TypeChecker_Env.get_range env)
in (let _152_1889 = (let _152_1888 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _152_1888))
in (FStar_TypeChecker_Errors.diag _152_1890 _152_1889)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end)))
end)
end
in (

let _55_3737 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3737.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3737.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3737.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3746 -> begin
false
end))
in (

let rec until_fixpoint = (fun _55_3750 implicits -> (match (_55_3750) with
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

let _55_3763 = hd
in (match (_55_3763) with
| (_55_3757, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint (((hd)::out), (changed)) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _55_3766 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _152_1906 = (FStar_Syntax_Print.uvar_to_string u)
in (let _152_1905 = (FStar_Syntax_Print.term_to_string tm)
in (let _152_1904 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _152_1906 _152_1905 _152_1904))))
end else begin
()
end
in (

let _55_3775 = (env.FStar_TypeChecker_Env.type_of (

let _55_3768 = env
in {FStar_TypeChecker_Env.solver = _55_3768.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3768.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3768.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3768.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3768.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3768.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3768.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3768.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3768.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3768.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3768.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3768.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3768.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3768.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3768.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3768.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3768.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3768.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _55_3768.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _55_3768.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _55_3768.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3768.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _55_3768.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (_55_3775) with
| (_55_3771, _55_3773, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _55_3776 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3776.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3776.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3776.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _55_3779 -> (match (()) with
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

let _55_3781 = g
in (let _152_1910 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3781.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3781.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3781.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _152_1910})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _152_1915 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _152_1915 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _152_1916 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _152_1916))
end
| ((reason, _55_3791, _55_3793, e, t, r))::_55_3788 -> begin
(let _152_1919 = (let _152_1918 = (FStar_Syntax_Print.term_to_string t)
in (let _152_1917 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _152_1918 _152_1917 reason)))
in (FStar_TypeChecker_Errors.report r _152_1919))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _55_3801 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3801.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3801.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = _55_3801.FStar_TypeChecker_Env.implicits}))





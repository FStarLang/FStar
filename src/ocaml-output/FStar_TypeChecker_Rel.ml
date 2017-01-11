
open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((uv), (uv)))
end
| _57_37 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _156_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _156_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (((uv), (k')))) None r)
in (let _156_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((uv), (args)))) (Some (k.FStar_Syntax_Syntax.n)) r)
in ((_156_8), (uv))))))
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
| TERM (_57_43) -> begin
_57_43
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_57_46) -> begin
_57_46
end))


type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}


let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkworklist"))))


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
| Success (_57_56) -> begin
_57_56
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_57_59) -> begin
_57_59
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


let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _57_1 -> (match (_57_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))


let term_to_string = (fun env t -> (match ((let _156_91 = (FStar_Syntax_Subst.compress t)
in _156_91.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (u, t) -> begin
(let _156_93 = (FStar_Syntax_Print.uvar_to_string u)
in (let _156_92 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "(%s:%s)" _156_93 _156_92)))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u, ty); FStar_Syntax_Syntax.tk = _57_77; FStar_Syntax_Syntax.pos = _57_75; FStar_Syntax_Syntax.vars = _57_73}, args) -> begin
(let _156_96 = (FStar_Syntax_Print.uvar_to_string u)
in (let _156_95 = (FStar_Syntax_Print.term_to_string ty)
in (let _156_94 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "(%s:%s) %s" _156_96 _156_95 _156_94))))
end
| _57_87 -> begin
(FStar_Syntax_Print.term_to_string t)
end))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _57_2 -> (match (_57_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _156_115 = (let _156_114 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _156_113 = (let _156_112 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _156_111 = (let _156_110 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _156_109 = (let _156_108 = (let _156_107 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _156_106 = (let _156_105 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _156_104 = (let _156_103 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _156_102 = (let _156_101 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_156_101)::[])
in (_156_103)::_156_102))
in (_156_105)::_156_104))
in (_156_107)::_156_106))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_156_108)
in (_156_110)::_156_109))
in (_156_112)::_156_111))
in (_156_114)::_156_113))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _156_115))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _156_117 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _156_116 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _156_117 (rel_to_string p.FStar_TypeChecker_Common.relation) _156_116)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _57_3 -> (match (_57_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _156_122 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _156_122 FStar_Util.string_of_int))
end
in (let _156_123 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _156_123)))
end
| TERM ((u, _57_103), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _156_124 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _156_124 FStar_Util.string_of_int))
end
in (let _156_125 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _156_125)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _156_130 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _156_130 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _156_134 = (let _156_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _156_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _156_134 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _156_137 = (FStar_All.pipe_right args (FStar_List.map (fun _57_116 -> (match (_57_116) with
| (x, _57_115) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _156_137 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> (let _156_140 = (not ((FStar_Options.eager_inference ())))
in {attempting = []; wl_deferred = []; ctr = (Prims.parse_int "0"); defer_ok = _156_140; smt_ok = true; tcenv = env}))


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _57_121 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _57_121.wl_deferred; ctr = _57_121.ctr; defer_ok = _57_121.defer_ok; smt_ok = smt_ok; tcenv = _57_121.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

let _57_127 = (empty_worklist env)
in (let _156_153 = (FStar_List.map Prims.snd g)
in {attempting = _156_153; wl_deferred = _57_127.wl_deferred; ctr = _57_127.ctr; defer_ok = false; smt_ok = _57_127.smt_ok; tcenv = _57_127.tcenv})))


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _57_132 = wl
in {attempting = _57_132.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; ctr = _57_132.ctr; defer_ok = _57_132.defer_ok; smt_ok = _57_132.smt_ok; tcenv = _57_132.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _57_136 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _57_136.wl_deferred; ctr = _57_136.ctr; defer_ok = _57_136.defer_ok; smt_ok = _57_136.smt_ok; tcenv = _57_136.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

let _57_141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_170 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _156_170))
end else begin
()
end
in Failed (((prob), (reason)))))


let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _57_4 -> (match (_57_4) with
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

let _57_148 = p
in {FStar_TypeChecker_Common.pid = _57_148.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _57_148.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_148.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_148.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_148.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_148.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_148.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _57_5 -> (match (_57_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _156_177 -> FStar_TypeChecker_Common.TProb (_156_177)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _156_178 -> FStar_TypeChecker_Common.CProb (_156_178)))
end))


let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _57_6 -> (match (_57_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _57_7 -> (match (_57_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))


let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _57_8 -> (match (_57_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))


let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _57_9 -> (match (_57_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))


let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _57_10 -> (match (_57_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))


let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _57_11 -> (match (_57_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))


let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _57_12 -> (match (_57_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))


let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _57_13 -> (match (_57_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _156_197 -> FStar_TypeChecker_Common.TProb (_156_197)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _156_198 -> FStar_TypeChecker_Common.CProb (_156_198)) (invert p))
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = (Prims.parse_int "1")))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun _57_198 -> (match (()) with
| () -> begin
(

let _57_199 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _156_211 = (next_pid ())
in (let _156_210 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _156_211; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _156_210; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _156_220 = (next_pid ())
in (let _156_219 = (new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _156_220; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _156_219; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _156_227 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _156_227; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT (((x), (e))))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _156_239 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _156_238 = (prob_to_string env d)
in (let _156_237 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _156_239 _156_238 _156_237 s))))
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
| _57_235 -> begin
(failwith "impossible")
end)
in (

let _57_243 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _156_241 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.lhs)
in (let _156_240 = (FStar_TypeChecker_Normalize.term_to_string env tp.FStar_TypeChecker_Common.rhs)
in ((_156_241), (_156_240))))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _156_243 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.lhs)
in (let _156_242 = (FStar_TypeChecker_Normalize.comp_to_string env cp.FStar_TypeChecker_Common.rhs)
in ((_156_243), (_156_242))))
end)
in (match (_57_243) with
| (lhs, rhs) -> begin
(FStar_Util.format3 "%s is not %s the expected type %s" lhs rel rhs)
end))))
end)


let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _57_14 -> (match (_57_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _57_253 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _57_256), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _57_15 -> (match (_57_15) with
| UNIV (_57_265) -> begin
None
end
| TERM ((u, _57_269), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))


let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _57_16 -> (match (_57_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _57_282 -> begin
None
end))))


let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _156_262 = (let _156_261 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _156_261))
in (FStar_Syntax_Subst.compress _156_262)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _156_267 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _156_267)))


let norm_arg = (fun env t -> (let _156_270 = (sn env (Prims.fst t))
in ((_156_270), ((Prims.snd t)))))


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _57_293 -> (match (_57_293) with
| (x, imp) -> begin
(let _156_277 = (

let _57_294 = x
in (let _156_276 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_294.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_294.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_276}))
in ((_156_277), (imp)))
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _156_284 = (aux u)
in FStar_Syntax_Syntax.U_succ (_156_284))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _156_285 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_156_285))
end
| _57_306 -> begin
u
end)))
in (let _156_286 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _156_286))))


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _57_326; FStar_Syntax_Syntax.pos = _57_324; FStar_Syntax_Syntax.vars = _57_322} -> begin
((x.FStar_Syntax_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(let _156_300 = (let _156_299 = (FStar_Syntax_Print.term_to_string tt)
in (let _156_298 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _156_299 _156_298)))
in (failwith _156_300))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _156_301 = (FStar_Syntax_Subst.compress t1')
in _156_301.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_57_344) -> begin
(aux true t1')
end
| _57_347 -> begin
((t1), (None))
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
((t1), (None))
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _156_304 = (let _156_303 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_302 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _156_303 _156_302)))
in (failwith _156_304))
end))
in (let _156_305 = (whnf env t1)
in (aux false _156_305))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _156_311 = (let _156_310 = (empty_worklist env)
in (base_and_refinement env _156_310 t))
in (FStar_All.pipe_right _156_311 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _156_314 = (FStar_Syntax_Syntax.null_bv t)
in ((_156_314), (FStar_Syntax_Util.t_true))))


let as_refinement = (fun env wl t -> (

let _57_393 = (base_and_refinement env wl t)
in (match (_57_393) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement = (fun _57_401 -> (match (_57_401) with
| (t_base, refopt) -> begin
(

let _57_409 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_57_409) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (((y), (phi)))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _57_17 -> (match (_57_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _156_327 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _156_326 = (let _156_323 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _156_323))
in (let _156_325 = (let _156_324 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _156_324))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _156_327 _156_326 (rel_to_string p.FStar_TypeChecker_Common.relation) _156_325))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _156_330 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _156_329 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _156_328 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _156_330 _156_329 (rel_to_string p.FStar_TypeChecker_Common.relation) _156_328))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _156_336 = (let _156_335 = (let _156_334 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _57_422 -> (match (_57_422) with
| (_57_418, _57_420, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _156_334))
in (FStar_List.map (wl_prob_to_string wl) _156_335))
in (FStar_All.pipe_right _156_336 (FStar_String.concat "\n\t"))))


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

let _57_443 = (match ((let _156_343 = (FStar_Syntax_Subst.compress k)
in _156_343.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _156_344 = (FStar_Syntax_Subst.open_comp bs c)
in ((((ys), (t))), (_156_344)))
end else begin
(

let _57_434 = (FStar_Syntax_Util.abs_formals t)
in (match (_57_434) with
| (ys', t, _57_433) -> begin
(let _156_345 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((((FStar_List.append ys ys')), (t))), (_156_345)))
end))
end
end
| _57_436 -> begin
(let _156_347 = (let _156_346 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_156_346)))
in ((((ys), (t))), (_156_347)))
end)
in (match (_57_443) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ([]))))))
end else begin
(

let c = (let _156_348 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _156_348 c))
in (let _156_352 = (let _156_351 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _156_349 -> FStar_Util.Inl (_156_349)))
in (FStar_All.pipe_right _156_351 (fun _156_350 -> Some (_156_350))))
in (FStar_Syntax_Util.abs ys t _156_352)))
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

let _57_457 = (p_guard prob)
in (match (_57_457) with
| (_57_455, uv) -> begin
(

let _57_468 = (match ((let _156_363 = (FStar_Syntax_Subst.compress uv)
in _156_363.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

let _57_464 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _156_366 = (FStar_Util.string_of_int (p_pid prob))
in (let _156_365 = (FStar_Syntax_Print.term_to_string uv)
in (let _156_364 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _156_366 _156_365 _156_364))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _57_467 -> begin
if (not (resolve_ok)) then begin
(failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _57_470 = (commit uvis)
in (

let _57_472 = wl
in {attempting = _57_472.attempting; wl_deferred = _57_472.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _57_472.defer_ok; smt_ok = _57_472.smt_ok; tcenv = _57_472.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

let _57_477 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_375 = (FStar_Util.string_of_int pid)
in (let _156_374 = (let _156_373 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _156_373 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _156_375 _156_374)))
end else begin
()
end
in (

let _57_479 = (commit sol)
in (

let _57_481 = wl
in {attempting = _57_481.attempting; wl_deferred = _57_481.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _57_481.defer_ok; smt_ok = _57_481.smt_ok; tcenv = _57_481.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match (((t), (g))) with
| (_57_491, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _156_388 = (FStar_Syntax_Util.mk_conj t f)
in Some (_156_388))
end))
in (

let _57_503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_391 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _156_390 = (let _156_389 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _156_389 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _156_391 _156_390)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


let rec occurs = (fun wl uk t -> (let _156_401 = (let _156_399 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _156_399 FStar_Util.set_elements))
in (FStar_All.pipe_right _156_401 (FStar_Util.for_some (fun _57_512 -> (match (_57_512) with
| (uv, _57_511) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _156_408 = (let _156_407 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _156_406 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _156_407 _156_406)))
in Some (_156_408))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _57_527 = (occurs_check env wl uk t)
in (match (_57_527) with
| (occurs_ok, msg) -> begin
(let _156_414 = (FStar_Util.set_is_subset_of fvs_t fvs)
in ((occurs_ok), (_156_414), (((msg), (fvs), (fvs_t)))))
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _57_545 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _57_537 _57_540 -> (match (((_57_537), (_57_540))) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _156_423 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _156_423)) then begin
((isect), (isect_set))
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _156_424 = (FStar_Util.set_add x isect_set)
in (((((x), (imp)))::isect), (_156_424)))
end else begin
((isect), (isect_set))
end)
end
end)) (([]), (FStar_Syntax_Syntax.no_names))))
in (match (_57_545) with
| (isect, _57_544) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _57_551 _57_555 -> (match (((_57_551), (_57_555))) with
| ((a, _57_550), (b, _57_554)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _57_565 -> (match (_57_565) with
| (b, _57_564) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some (((a), ((Prims.snd hd))))
end
end
| _57_567 -> begin
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

let _57_576 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_439 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _156_439))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let is_flex : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (match ((let _156_442 = (FStar_Syntax_Subst.compress t)
in _156_442.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
true
end
| _57_599 -> begin
false
end))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
((t), (uv), (k), ([]))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _57_610; FStar_Syntax_Syntax.pos = _57_608; FStar_Syntax_Syntax.vars = _57_606}, args) -> begin
((t), (uv), (k), (args))
end
| _57_620 -> begin
(failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _57_627 = (destruct_flex_t t)
in (match (_57_627) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| _57_631 -> begin
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
| MisMatch (_57_634) -> begin
_57_634
end))


let head_match : match_result  ->  match_result = (fun _57_18 -> (match (_57_18) with
| MisMatch (i, j) -> begin
MisMatch (((i), (j)))
end
| _57_641 -> begin
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _57_727), FStar_Syntax_Syntax.Tm_uinst (g, _57_732)) -> begin
(let _156_478 = (head_matches env f g)
in (FStar_All.pipe_right _156_478 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _57_743), FStar_Syntax_Syntax.Tm_uvar (uv', _57_748)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch (((None), (None)))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _57_754), FStar_Syntax_Syntax.Tm_refine (y, _57_759)) -> begin
(let _156_479 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _156_479 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _57_765), _57_769) -> begin
(let _156_480 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _156_480 head_match))
end
| (_57_772, FStar_Syntax_Syntax.Tm_refine (x, _57_775)) -> begin
(let _156_481 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _156_481 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _57_795), FStar_Syntax_Syntax.Tm_app (head', _57_800)) -> begin
(let _156_482 = (head_matches env head head')
in (FStar_All.pipe_right _156_482 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _57_806), _57_810) -> begin
(let _156_483 = (head_matches env head t2)
in (FStar_All.pipe_right _156_483 head_match))
end
| (_57_813, FStar_Syntax_Syntax.Tm_app (head, _57_816)) -> begin
(let _156_484 = (head_matches env t1 head)
in (FStar_All.pipe_right _156_484 head_match))
end
| _57_821 -> begin
(let _156_487 = (let _156_486 = (delta_depth_of_term env t1)
in (let _156_485 = (delta_depth_of_term env t2)
in ((_156_486), (_156_485))))
in MisMatch (_156_487))
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let maybe_inline = (fun t -> (

let _57_831 = (FStar_Syntax_Util.head_and_args t)
in (match (_57_831) with
| (head, _57_830) -> begin
(match ((let _156_494 = (FStar_Syntax_Util.un_uinst head)
in _156_494.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
if (let _156_495 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _156_495 FStar_Option.isSome)) then begin
(let _156_497 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::[]) env t)
in (FStar_All.pipe_right _156_497 (fun _156_496 -> Some (_156_496))))
end else begin
None
end
end
| _57_835 -> begin
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
(match ((let _156_517 = (maybe_inline t1)
in (let _156_516 = (maybe_inline t2)
in ((_156_517), (_156_516))))) with
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

let _57_899 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in ((t1'), (t2)))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _156_518 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in ((t1), (_156_518))))
end
in (match (_57_899) with
| (t1, t2) -> begin
(aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
end)))
end
| MisMatch (_57_901) -> begin
(fail r)
end
| _57_904 -> begin
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
| T (_57_907) -> begin
_57_907
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_57_910) -> begin
_57_910
end))


type tcs =
tc Prims.list


let generic_kind : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (

let _57_916 = (FStar_Syntax_Util.type_u ())
in (match (_57_916) with
| (t, _57_915) -> begin
(let _156_589 = (new_uvar r binders t)
in (Prims.fst _156_589))
end)))


let kind_type : FStar_Syntax_Syntax.binders  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.typ = (fun binders r -> (let _156_594 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _156_594 Prims.fst)))


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_57_925) -> begin
false
end
| _57_928 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((_57_938, imp), T (t, _57_943)) -> begin
((t), (imp))
end
| _57_948 -> begin
(failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), (args)))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _57_953 -> (match (_57_953) with
| (t, _57_952) -> begin
((None), (INVARIANT), (T (((t), (generic_kind)))))
end))))
in ((rebuild), (matches), (tcs))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _57_960 -> (match (()) with
| () -> begin
(failwith "Bad reconstruction")
end))
in (

let _57_963 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_57_963) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match (((bs), (tcs))) with
| (((x, imp))::bs, (T (t, _57_978))::tcs) -> begin
(aux (((((

let _57_983 = x
in {FStar_Syntax_Syntax.ppname = _57_983.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_983.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (imp)))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _57_991 -> begin
(failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _57_19 -> (match (_57_19) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (C (c))))::out))
end
| (hd)::rest -> begin
(decompose ((((Some (hd)), (CONTRAVARIANT), (T ((((Prims.fst hd).FStar_Syntax_Syntax.sort), (kind_type))))))::out) rest)
end))
in (let _156_656 = (decompose [] bs)
in ((rebuild), (matches), (_156_656)))))
end)))
end
| _57_1000 -> begin
(

let rebuild = (fun _57_20 -> (match (_57_20) with
| [] -> begin
t
end
| _57_1004 -> begin
(failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _57_21 -> (match (_57_21) with
| T (t, _57_1010) -> begin
t
end
| _57_1014 -> begin
(failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _57_22 -> (match (_57_22) with
| T (t, _57_1018) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _57_1022 -> begin
(failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_57_1035, variance, T (ti, mk_kind)) -> begin
(

let k = (mk_kind scope r)
in (

let _57_1045 = (new_uvar r scope k)
in (match (_57_1045) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _57_1048 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((gi), (args)))) None r)
end)
in (let _156_688 = (let _156_687 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _156_686 -> FStar_TypeChecker_Common.TProb (_156_686)) _156_687))
in ((T (((gi_xs), (mk_kind)))), (_156_688))))
end)))
end
| (_57_1051, _57_1053, C (_57_1055)) -> begin
(failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Syntax_Util.t_true))
end
| (q)::qs -> begin
(

let _57_1143 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti, uopt); FStar_Syntax_Syntax.tk = _57_1073; FStar_Syntax_Syntax.pos = _57_1071; FStar_Syntax_Syntax.vars = _57_1069})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _57_1083), prob) -> begin
(let _156_701 = (let _156_700 = (FStar_Syntax_Syntax.mk_Total' gi_xs uopt)
in (FStar_All.pipe_left (fun _156_699 -> C (_156_699)) _156_700))
in ((_156_701), ((prob)::[])))
end
| _57_1089 -> begin
(failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti, uopt); FStar_Syntax_Syntax.tk = _57_1097; FStar_Syntax_Syntax.pos = _57_1095; FStar_Syntax_Syntax.vars = _57_1093})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (T (((ti), (kind_type))))))) with
| (T (gi_xs, _57_1107), prob) -> begin
(let _156_708 = (let _156_707 = (FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt)
in (FStar_All.pipe_left (fun _156_706 -> C (_156_706)) _156_707))
in ((_156_708), ((prob)::[])))
end
| _57_1113 -> begin
(failwith "impossible")
end)
end
| (_57_1115, _57_1117, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _57_1123; FStar_Syntax_Syntax.pos = _57_1121; FStar_Syntax_Syntax.vars = _57_1119})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> ((None), (INVARIANT), (T ((((Prims.fst t)), (generic_kind))))))))
in (

let components = (((None), (COVARIANT), (T (((c.FStar_Syntax_Syntax.result_typ), (kind_type))))))::components
in (

let _57_1134 = (let _156_714 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _156_714 FStar_List.unzip))
in (match (_57_1134) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _156_719 = (let _156_718 = (let _156_715 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _156_715 un_T))
in (let _156_717 = (let _156_716 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _156_716 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.comp_univs = c.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _156_718; FStar_Syntax_Syntax.effect_args = _156_717; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _156_719))
in ((C (gi_xs)), (sub_probs)))
end))))
end
| _57_1137 -> begin
(

let _57_1140 = (sub_prob scope args q)
in (match (_57_1140) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_57_1143) with
| (tc, probs) -> begin
(

let _57_1156 = (match (q) with
| (Some (b), _57_1147, _57_1149) -> begin
(let _156_721 = (let _156_720 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_156_720)::args)
in ((Some (b)), ((b)::scope), (_156_721)))
end
| _57_1152 -> begin
((None), (scope), (args))
end)
in (match (_57_1156) with
| (bopt, scope, args) -> begin
(

let _57_1160 = (aux scope args qs)
in (match (_57_1160) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _156_724 = (let _156_723 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_156_723)
in (FStar_Syntax_Util.mk_conj_l _156_724))
end
| Some (b) -> begin
(let _156_728 = (let _156_727 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _156_726 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_156_727)::_156_726))
in (FStar_Syntax_Util.mk_conj_l _156_728))
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

let _57_1169 = p
in (let _156_740 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _156_739 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _57_1169.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _156_740; FStar_TypeChecker_Common.relation = _57_1169.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _156_739; FStar_TypeChecker_Common.element = _57_1169.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_1169.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_1169.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_1169.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_1169.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_1169.FStar_TypeChecker_Common.rank}))))


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _156_746 = (compress_tprob wl p)
in (FStar_All.pipe_right _156_746 (fun _156_745 -> FStar_TypeChecker_Common.TProb (_156_745))))
end
| FStar_TypeChecker_Common.CProb (_57_1176) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

let prob = (let _156_751 = (compress_prob wl pr)
in (FStar_All.pipe_right _156_751 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _57_1186 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_57_1186) with
| (lh, _57_1185) -> begin
(

let _57_1190 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_57_1190) with
| (rh, _57_1189) -> begin
(

let _57_1246 = (match (((lh.FStar_Syntax_Syntax.n), (rh.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uvar (_57_1192), FStar_Syntax_Syntax.Tm_uvar (_57_1195)) -> begin
((flex_flex), (tp))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when ((tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) || (FStar_Options.eager_inference ())) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Syntax_Syntax.Tm_uvar (_57_1211), _57_1214) -> begin
(

let _57_1218 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_57_1218) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _57_1221 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _156_753 = (

let _57_1223 = tp
in (let _156_752 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _57_1223.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_1223.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_1223.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _156_752; FStar_TypeChecker_Common.element = _57_1223.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_1223.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_1223.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_1223.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_1223.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_1223.FStar_TypeChecker_Common.rank}))
in ((rank), (_156_753))))
end)
end))
end
| (_57_1226, FStar_Syntax_Syntax.Tm_uvar (_57_1228)) -> begin
(

let _57_1233 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_57_1233) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _57_1236 -> begin
(let _156_755 = (

let _57_1237 = tp
in (let _156_754 = (force_refinement ((b), (ref_opt)))
in {FStar_TypeChecker_Common.pid = _57_1237.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _156_754; FStar_TypeChecker_Common.relation = _57_1237.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_1237.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_1237.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_1237.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_1237.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_1237.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_1237.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_1237.FStar_TypeChecker_Common.rank}))
in ((refine_flex), (_156_755)))
end)
end))
end
| (_57_1240, _57_1242) -> begin
((rigid_rigid), (tp))
end)
in (match (_57_1246) with
| (rank, tp) -> begin
(let _156_757 = (FStar_All.pipe_right (

let _57_1247 = tp
in {FStar_TypeChecker_Common.pid = _57_1247.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_1247.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_1247.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_1247.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_1247.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_1247.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_1247.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_1247.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_1247.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _156_756 -> FStar_TypeChecker_Common.TProb (_156_756)))
in ((rank), (_156_757)))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _156_759 = (FStar_All.pipe_right (

let _57_1251 = cp
in {FStar_TypeChecker_Common.pid = _57_1251.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_1251.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_1251.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_1251.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_1251.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_1251.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_1251.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_1251.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_1251.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _156_758 -> FStar_TypeChecker_Common.CProb (_156_758)))
in ((rigid_rigid), (_156_759)))
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _57_1258 probs -> (match (_57_1258) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _57_1266 = (rank wl hd)
in (match (_57_1266) with
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
| UDeferred (_57_1277) -> begin
_57_1277
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_57_1280) -> begin
_57_1280
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_57_1283) -> begin
_57_1283
end))


let rec really_solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _57_1299 = (FStar_Syntax_Util.univ_kernel u)
in (match (_57_1299) with
| (k, _57_1298) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _57_1303 -> begin
false
end)
end)))))
end
| _57_1305 -> begin
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
| _57_1330 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _156_839 = (let _156_838 = (FStar_Syntax_Print.univ_to_string u1)
in (let _156_837 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _156_838 _156_837)))
in UFailed (_156_839))
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
| _57_1348 -> begin
(let _156_846 = (let _156_845 = (FStar_Syntax_Print.univ_to_string u1)
in (let _156_844 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _156_845 _156_844 msg)))
in UFailed (_156_846))
end))
in (match (((u1), (u2))) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(let _156_849 = (let _156_848 = (FStar_Syntax_Print.univ_to_string u1)
in (let _156_847 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s" _156_848 _156_847)))
in (failwith _156_849))
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
(let _156_852 = (let _156_851 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _156_850 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _156_851 _156_850)))
in (try_umax_components u1 u2 _156_852))
end else begin
(let _156_853 = (extend_solution orig ((UNIV (((v1), (u))))::[]) wl)
in USolved (_156_853))
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


let match_num_binders = (fun bc1 bc2 -> (

let _57_1453 = bc1
in (match (_57_1453) with
| (bs1, mk_cod1) -> begin
(

let _57_1456 = bc2
in (match (_57_1456) with
| (bs2, mk_cod2) -> begin
(

let curry = (fun n bs mk_cod -> (

let _57_1463 = (FStar_Util.first_N n bs)
in (match (_57_1463) with
| (bs, rest) -> begin
(let _156_891 = (mk_cod rest)
in ((bs), (_156_891)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _156_895 = (let _156_892 = (mk_cod1 [])
in ((bs1), (_156_892)))
in (let _156_894 = (let _156_893 = (mk_cod2 [])
in ((bs2), (_156_893)))
in ((_156_895), (_156_894))))
end else begin
if (l1 > l2) then begin
(let _156_898 = (curry l2 bs1 mk_cod1)
in (let _156_897 = (let _156_896 = (mk_cod2 [])
in ((bs2), (_156_896)))
in ((_156_898), (_156_897))))
end else begin
(let _156_901 = (let _156_899 = (mk_cod1 [])
in ((bs1), (_156_899)))
in (let _156_900 = (curry l1 bs2 mk_cod2)
in ((_156_901), (_156_900))))
end
end)))
end))
end)))


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (

let _57_1468 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_947 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _156_947))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _57_1475 = probs
in {attempting = tl; wl_deferred = _57_1475.wl_deferred; ctr = _57_1475.ctr; defer_ok = _57_1475.defer_ok; smt_ok = _57_1475.smt_ok; tcenv = _57_1475.tcenv})
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
| (None, _57_1490, _57_1492) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _57_1496 -> begin
(

let _57_1505 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _57_1502 -> (match (_57_1502) with
| (c, _57_1499, _57_1501) -> begin
(c < probs.ctr)
end))))
in (match (_57_1505) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _156_950 = (FStar_List.map (fun _57_1511 -> (match (_57_1511) with
| (_57_1508, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in Success (_156_950))
end
| _57_1513 -> begin
(let _156_953 = (

let _57_1514 = probs
in (let _156_952 = (FStar_All.pipe_right attempt (FStar_List.map (fun _57_1521 -> (match (_57_1521) with
| (_57_1517, _57_1519, y) -> begin
y
end))))
in {attempting = _156_952; wl_deferred = rest; ctr = _57_1514.ctr; defer_ok = _57_1514.defer_ok; smt_ok = _57_1514.smt_ok; tcenv = _57_1514.tcenv}))
in (solve env _156_953))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _156_959 = (solve_prob orig None [] wl)
in (solve env _156_959))
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
| _57_1556 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _57_1564; FStar_Syntax_Syntax.pos = _57_1562; FStar_Syntax_Syntax.vars = _57_1560}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _57_1576; FStar_Syntax_Syntax.pos = _57_1574; FStar_Syntax_Syntax.vars = _57_1572}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _57_1585 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(failwith "Impossible: expect head symbols to match")
end
| _57_1600 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

let _57_1605 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_975 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _156_975 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _57_1610 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_979 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _156_979))
end else begin
()
end
in (

let _57_1614 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_57_1614) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _57_1620 = (head_matches_delta env () t1 t2)
in (match (_57_1620) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_57_1622) -> begin
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

let _57_1638 = (match (ts) with
| Some (t1, t2) -> begin
(let _156_985 = (FStar_Syntax_Subst.compress t1)
in (let _156_984 = (FStar_Syntax_Subst.compress t2)
in ((_156_985), (_156_984))))
end
| None -> begin
(let _156_987 = (FStar_Syntax_Subst.compress t1)
in (let _156_986 = (FStar_Syntax_Subst.compress t2)
in ((_156_987), (_156_986))))
end)
in (match (_57_1638) with
| (t1, t2) -> begin
(

let eq_prob = (fun t1 t2 -> (let _156_993 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _156_992 -> FStar_TypeChecker_Common.TProb (_156_992)) _156_993)))
in (match (((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _156_1000 = (let _156_999 = (let _156_996 = (let _156_995 = (let _156_994 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in ((x), (_156_994)))
in FStar_Syntax_Syntax.Tm_refine (_156_995))
in (FStar_Syntax_Syntax.mk _156_996 None t1.FStar_Syntax_Syntax.pos))
in (let _156_998 = (let _156_997 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_156_997)::[])
in ((_156_999), (_156_998))))
in Some (_156_1000))
end
| (_57_1652, FStar_Syntax_Syntax.Tm_refine (x, _57_1655)) -> begin
(let _156_1003 = (let _156_1002 = (let _156_1001 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_156_1001)::[])
in ((t1), (_156_1002)))
in Some (_156_1003))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _57_1661), _57_1665) -> begin
(let _156_1006 = (let _156_1005 = (let _156_1004 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_156_1004)::[])
in ((t2), (_156_1005)))
in Some (_156_1006))
end
| _57_1668 -> begin
(

let _57_1672 = (FStar_Syntax_Util.head_and_args t1)
in (match (_57_1672) with
| (head1, _57_1671) -> begin
(match ((let _156_1007 = (FStar_Syntax_Util.un_uinst head1)
in _156_1007.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _57_1678; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_defined_at_level (i); FStar_Syntax_Syntax.fv_qual = _57_1674}) -> begin
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
| _57_1685 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _57_1689) -> begin
(

let _57_1714 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _57_23 -> (match (_57_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

let _57_1700 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_57_1700) with
| (u', _57_1699) -> begin
(match ((let _156_1009 = (whnf env u')
in _156_1009.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _57_1703) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _57_1707 -> begin
false
end)
end))
end
| _57_1709 -> begin
false
end)
end
| _57_1711 -> begin
false
end))))
in (match (_57_1714) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _57_1718 tps -> (match (_57_1718) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _156_1014 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _156_1014))) with
| Some (bound, sub) -> begin
(make_lower_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _57_1731 -> begin
None
end)
end))
in (match ((let _156_1016 = (let _156_1015 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in ((_156_1015), ([])))
in (make_lower_bound _156_1016 lower_bounds))) with
| None -> begin
(

let _57_1733 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _57_1743 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _57_1740 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _57_1740.wl_deferred; ctr = _57_1740.ctr; defer_ok = _57_1740.defer_ok; smt_ok = _57_1740.smt_ok; tcenv = _57_1740.tcenv})
in (let _156_1017 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _156_1017)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _57_1745 = wl
in {attempting = sub_probs; wl_deferred = _57_1745.wl_deferred; ctr = _57_1745.ctr; defer_ok = _57_1745.defer_ok; smt_ok = _57_1745.smt_ok; tcenv = _57_1745.tcenv}))) with
| Success (_57_1748) -> begin
(

let wl = (

let _57_1750 = wl
in {attempting = rest; wl_deferred = _57_1750.wl_deferred; ctr = _57_1750.ctr; defer_ok = _57_1750.defer_ok; smt_ok = _57_1750.smt_ok; tcenv = _57_1750.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _57_1756 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _57_1759 -> begin
None
end)))
end))
end))
end
| _57_1761 -> begin
(failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _57_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_1023 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _156_1023))
end else begin
()
end
in (

let _57_1769 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_57_1769) with
| (u, args) -> begin
(

let _57_1775 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (_57_1775) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _57_1784 = (FStar_Syntax_Util.head_and_args t1)
in (match (_57_1784) with
| (h1, args1) -> begin
(

let _57_1788 = (FStar_Syntax_Util.head_and_args t2)
in (match (_57_1788) with
| (h2, _57_1787) -> begin
(match (((h1.FStar_Syntax_Syntax.n), (h2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _156_1035 = (let _156_1034 = (let _156_1033 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _156_1032 -> FStar_TypeChecker_Common.TProb (_156_1032)) _156_1033))
in (_156_1034)::[])
in Some (_156_1035))
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
(let _156_1039 = (let _156_1038 = (let _156_1037 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _156_1036 -> FStar_TypeChecker_Common.TProb (_156_1036)) _156_1037))
in (_156_1038)::[])
in Some (_156_1039))
end
end else begin
None
end
end
| _57_1800 -> begin
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
in (let _156_1046 = (let _156_1045 = (let _156_1044 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _156_1044))
in ((_156_1045), (m)))
in Some (_156_1046))))))
end))
end
| (_57_1822, FStar_Syntax_Syntax.Tm_refine (y, _57_1825)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, _57_1835), _57_1839) -> begin
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
| _57_1846 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _57_1854) -> begin
(

let _57_1879 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _57_24 -> (match (_57_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _57_1865 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_57_1865) with
| (u', _57_1864) -> begin
(match ((let _156_1048 = (whnf env u')
in _156_1048.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _57_1868) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _57_1872 -> begin
false
end)
end))
end
| _57_1874 -> begin
false
end)
end
| _57_1876 -> begin
false
end))))
in (match (_57_1879) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _57_1883 tps -> (match (_57_1883) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
(match ((let _156_1053 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _156_1053))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _57_1896 -> begin
None
end)
end))
in (match ((let _156_1055 = (let _156_1054 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in ((_156_1054), ([])))
in (make_upper_bound _156_1055 upper_bounds))) with
| None -> begin
(

let _57_1898 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _57_1908 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

let _57_1905 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _57_1905.wl_deferred; ctr = _57_1905.ctr; defer_ok = _57_1905.defer_ok; smt_ok = _57_1905.smt_ok; tcenv = _57_1905.tcenv})
in (let _156_1056 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _156_1056)))
end else begin
()
end
in (match ((solve_t env eq_prob (

let _57_1910 = wl
in {attempting = sub_probs; wl_deferred = _57_1910.wl_deferred; ctr = _57_1910.ctr; defer_ok = _57_1910.defer_ok; smt_ok = _57_1910.smt_ok; tcenv = _57_1910.tcenv}))) with
| Success (_57_1913) -> begin
(

let wl = (

let _57_1915 = wl
in {attempting = rest; wl_deferred = _57_1915.wl_deferred; ctr = _57_1915.ctr; defer_ok = _57_1915.defer_ok; smt_ok = _57_1915.smt_ok; tcenv = _57_1915.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _57_1921 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _57_1924 -> begin
None
end)))
end))
end))
end
| _57_1926 -> begin
(failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (

let _57_1943 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1084 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _156_1084))
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

let _57_1957 = hd1
in (let _156_1085 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_1957.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1957.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_1085}))
in (

let hd2 = (

let _57_1960 = hd2
in (let _156_1086 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _57_1960.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_1960.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_1086}))
in (

let prob = (let _156_1089 = (let _156_1088 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _156_1088 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _156_1087 -> FStar_TypeChecker_Common.TProb (_156_1087)) _156_1089))
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

let subst = (let _156_1090 = (FStar_Syntax_Subst.shift_subst (Prims.parse_int "1") subst)
in (FStar_Syntax_Syntax.DB ((((Prims.parse_int "0")), (hd1))))::_156_1090)
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux ((((hd1), (imp)))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _156_1092 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _156_1091 = (FStar_Syntax_Util.close_forall ((((hd1), (imp)))::[]) phi)
in (FStar_Syntax_Util.mk_conj _156_1092 _156_1091)))
in (

let _57_1972 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1094 = (FStar_Syntax_Print.term_to_string phi)
in (let _156_1093 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _156_1094 _156_1093)))
end else begin
()
end
in FStar_Util.Inl ((((prob)::sub_probs), (phi)))))
end
| fail -> begin
fail
end)))))))
end
| _57_1976 -> begin
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
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _156_1098 = (compress_tprob wl problem)
in (solve_t' env _156_1098 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _57_2004 = (head_matches_delta env wl t1 t2)
in (match (_57_2004) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch (_57_2006), _57_2009) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _57_2022 -> begin
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
in (let _156_1127 = (let _156_1126 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _156_1126 t2))
in (FStar_Syntax_Util.mk_forall x _156_1127)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _156_1128 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _156_1128)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_57_2032, Some (t1, t2)) -> begin
(solve_t env (

let _57_2038 = problem
in {FStar_TypeChecker_Common.pid = _57_2038.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _57_2038.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _57_2038.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2038.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2038.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2038.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2038.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2038.FStar_TypeChecker_Common.rank}) wl)
end
| (_57_2041, None) -> begin
(

let _57_2044 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1132 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1131 = (FStar_Syntax_Print.tag_of_term t1)
in (let _156_1130 = (FStar_Syntax_Print.term_to_string t2)
in (let _156_1129 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _156_1132 _156_1131 _156_1130 _156_1129)))))
end else begin
()
end
in (

let _57_2048 = (FStar_Syntax_Util.head_and_args t1)
in (match (_57_2048) with
| (head1, args1) -> begin
(

let _57_2051 = (FStar_Syntax_Util.head_and_args t2)
in (match (_57_2051) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _156_1137 = (let _156_1136 = (FStar_Syntax_Print.term_to_string head1)
in (let _156_1135 = (args_to_string args1)
in (let _156_1134 = (FStar_Syntax_Print.term_to_string head2)
in (let _156_1133 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _156_1136 _156_1135 _156_1134 _156_1133)))))
in (giveup env _156_1137 orig))
end else begin
if ((nargs = (Prims.parse_int "0")) || ((FStar_Syntax_Util.eq_args args1 args2) = FStar_Syntax_Util.Equal)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _156_1138 = (solve_prob orig None [] wl)
in (solve env _156_1138))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _57_2061 = (base_and_refinement env wl t1)
in (match (_57_2061) with
| (base1, refinement1) -> begin
(

let _57_2064 = (base_and_refinement env wl t2)
in (match (_57_2064) with
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

let subprobs = (FStar_List.map2 (fun _57_2077 _57_2081 -> (match (((_57_2077), (_57_2081))) with
| ((a, _57_2076), (a', _57_2080)) -> begin
(let _156_1142 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _156_1141 -> FStar_TypeChecker_Common.TProb (_156_1141)) _156_1142))
end)) args1 args2)
in (

let formula = (let _156_1144 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _156_1144))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _57_2087 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _57_2090 = problem
in {FStar_TypeChecker_Common.pid = _57_2090.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _57_2090.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _57_2090.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2090.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2090.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2090.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2090.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2090.FStar_TypeChecker_Common.rank}) wl)))
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

let _57_2109 = p
in (match (_57_2109) with
| (((u, k), xs, c), ps, (h, _57_2106, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_2115 = (imitation_sub_probs orig env xs ps qs)
in (match (_57_2115) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _156_1159 = (h gs_xs)
in (let _156_1158 = (let _156_1157 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _156_1155 -> FStar_Util.Inl (_156_1155)))
in (FStar_All.pipe_right _156_1157 (fun _156_1156 -> Some (_156_1156))))
in (FStar_Syntax_Util.abs xs _156_1159 _156_1158)))
in (

let _57_2117 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1166 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _156_1165 = (FStar_Syntax_Print.comp_to_string c)
in (let _156_1164 = (FStar_Syntax_Print.term_to_string im)
in (let _156_1163 = (FStar_Syntax_Print.tag_of_term im)
in (let _156_1162 = (let _156_1160 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _156_1160 (FStar_String.concat ", ")))
in (let _156_1161 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _156_1166 _156_1165 _156_1164 _156_1163 _156_1162 _156_1161)))))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (

let imitate' = (fun orig env wl _57_25 -> (match (_57_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (

let project = (fun orig env wl i p -> (

let _57_2143 = p
in (match (_57_2143) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _57_2148 = (FStar_List.nth ps i)
in (match (_57_2148) with
| (pi, _57_2147) -> begin
(

let _57_2152 = (FStar_List.nth xs i)
in (match (_57_2152) with
| (xi, _57_2151) -> begin
(

let rec gs = (fun k -> (

let _57_2157 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2157) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| ((a, _57_2165))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _57_2171 = (new_uvar r xs k_a)
in (match (_57_2171) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT (((a), (gi_xs))))::subst
in (

let _57_2177 = (aux subst tl)
in (match (_57_2177) with
| (gi_xs', gi_ps') -> begin
(let _156_1196 = (let _156_1193 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_156_1193)::gi_xs')
in (let _156_1195 = (let _156_1194 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_156_1194)::gi_ps')
in ((_156_1196), (_156_1195))))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _156_1197 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _156_1197)) then begin
None
end else begin
(

let _57_2181 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_57_2181) with
| (g_xs, _57_2180) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

let proj = (let _156_1202 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _156_1201 = (let _156_1200 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _156_1198 -> FStar_Util.Inl (_156_1198)))
in (FStar_All.pipe_right _156_1200 (fun _156_1199 -> Some (_156_1199))))
in (FStar_Syntax_Util.abs xs _156_1202 _156_1201)))
in (

let sub = (let _156_1208 = (let _156_1207 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _156_1206 = (let _156_1205 = (FStar_List.map (fun _57_2189 -> (match (_57_2189) with
| (_57_2185, _57_2187, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _156_1205))
in (mk_problem (p_scope orig) orig _156_1207 (p_rel orig) _156_1206 None "projection")))
in (FStar_All.pipe_left (fun _156_1203 -> FStar_TypeChecker_Common.TProb (_156_1203)) _156_1208))
in (

let _57_2191 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1210 = (FStar_Syntax_Print.term_to_string proj)
in (let _156_1209 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _156_1210 _156_1209)))
end else begin
()
end
in (

let wl = (let _156_1212 = (let _156_1211 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_156_1211))
in (solve_prob orig _156_1212 ((TERM (((u), (proj))))::[]) wl))
in (let _156_1214 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _156_1213 -> Some (_156_1213)) _156_1214)))))))
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun patterns_only orig lhs t2 wl -> (

let _57_2206 = lhs
in (match (_57_2206) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _57_2211 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_57_2211) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _156_1238 = (let _156_1237 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_156_1237)))
in Some (_156_1238))
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

let rec elim = (fun k args -> (match ((let _156_1244 = (let _156_1243 = (FStar_Syntax_Subst.compress k)
in _156_1243.FStar_Syntax_Syntax.n)
in ((_156_1244), (args)))) with
| (_57_2217, []) -> begin
(let _156_1246 = (let _156_1245 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_156_1245)))
in Some (_156_1246))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _57_2234 = (FStar_Syntax_Util.head_and_args k)
in (match (_57_2234) with
| (uv, uv_args) -> begin
(match ((let _156_1247 = (FStar_Syntax_Subst.compress uv)
in _156_1247.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _57_2237) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

let xs = (FStar_All.pipe_right args (FStar_List.map (fun _57_2243 -> (let _156_1253 = (let _156_1252 = (let _156_1251 = (let _156_1250 = (let _156_1249 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _156_1249 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _156_1250))
in (Prims.fst _156_1251))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _156_1252))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _156_1253)))))
in (

let c = (let _156_1257 = (let _156_1256 = (let _156_1255 = (let _156_1254 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _156_1254 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _156_1255))
in (Prims.fst _156_1256))
in (FStar_Syntax_Syntax.mk_Total _156_1257))
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

let uv_sol = (let _156_1263 = (let _156_1262 = (let _156_1261 = (let _156_1260 = (let _156_1259 = (let _156_1258 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _156_1258 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _156_1259))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_1260))
in FStar_Util.Inl (_156_1261))
in Some (_156_1262))
in (FStar_Syntax_Util.abs scope k' _156_1263))
in (

let _57_2249 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some (((xs), (c))))))))
end)
end
| _57_2252 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _57_2258) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _156_1265 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _156_1265 (fun _156_1264 -> Some (_156_1264))))
end else begin
if (n_xs < n_args) then begin
(

let _57_2264 = (FStar_Util.first_N n_xs args)
in (match (_57_2264) with
| (args, rest) -> begin
(

let _57_2267 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_57_2267) with
| (xs, c) -> begin
(let _156_1267 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _156_1267 (fun _57_2270 -> (match (_57_2270) with
| (xs', c) -> begin
Some ((((FStar_List.append xs xs')), (c)))
end))))
end))
end))
end else begin
(

let _57_2273 = (FStar_Util.first_N n_args xs)
in (match (_57_2273) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((rest), (c)))) None k.FStar_Syntax_Syntax.pos)
in (let _156_1270 = (let _156_1268 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _156_1268))
in (FStar_All.pipe_right _156_1270 (fun _156_1269 -> Some (_156_1269)))))
end))
end
end))
end
| _57_2276 -> begin
(let _156_1274 = (let _156_1273 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _156_1272 = (FStar_Syntax_Print.term_to_string k)
in (let _156_1271 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _156_1273 _156_1272 _156_1271))))
in (failwith _156_1274))
end))
in (let _156_1312 = (elim k_uv ps)
in (FStar_Util.bind_opt _156_1312 (fun _57_2279 -> (match (_57_2279) with
| (xs, c) -> begin
(let _156_1311 = (let _156_1310 = (decompose env t2)
in ((((((uv), (k_uv))), (xs), (c))), (ps), (_156_1310)))
in Some (_156_1311))
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
| Failed (_57_2287) -> begin
(

let _57_2289 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _57_2297 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + (Prims.parse_int "1"))))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _57_2307 = (FStar_Syntax_Util.head_and_args t2)
in (match (_57_2307) with
| (hd, _57_2306) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _57_2318 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

let _57_2320 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1323 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _156_1323))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _156_1327 = (let _156_1326 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _156_1326 Prims.fst))
in (FStar_All.pipe_right _156_1327 FStar_Syntax_Free.names))
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

let _57_2333 = (occurs_check env wl ((uv), (k_uv)) t2)
in (match (_57_2333) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _156_1329 = (let _156_1328 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _156_1328))
in (giveup_or_defer orig _156_1329))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if (((not (patterns_only)) && (FStar_Syntax_Util.is_function_typ t2)) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _156_1330 = (subterms args_lhs)
in (imitate' orig env wl _156_1330))
end else begin
(

let _57_2334 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1333 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1332 = (names_to_string fvs1)
in (let _156_1331 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _156_1333 _156_1332 _156_1331))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _57_2338 -> begin
(let _156_1334 = (sn_binders env vars)
in (u_abs k_uv _156_1334 t2))
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

let _57_2341 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1337 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1336 = (names_to_string fvs1)
in (let _156_1335 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _156_1337 _156_1336 _156_1335))))
end else begin
()
end
in (let _156_1338 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _156_1338 (~- ((Prims.parse_int "1"))))))
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
if (let _156_1339 = (FStar_Syntax_Free.names t1)
in (check_head _156_1339 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _57_2346 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1340 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _156_1340 (if (im_ok < (Prims.parse_int "0")) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _156_1341 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _156_1341 im_ok))))
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

let force_quasi_pattern = (fun xs_opt _57_2358 -> (match (_57_2358) with
| (t, u, k, args) -> begin
(

let _57_2362 = (FStar_Syntax_Util.arrow_formals k)
in (match (_57_2362) with
| (all_formals, _57_2361) -> begin
(

let _57_2363 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match (((formals), (args))) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _57_2376 -> (match (_57_2376) with
| (x, imp) -> begin
(let _156_1363 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_156_1363), (imp)))
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

let _57_2382 = (FStar_Syntax_Util.type_u ())
in (match (_57_2382) with
| (t, _57_2381) -> begin
(let _156_1364 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _156_1364))
end))
in (

let _57_2386 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_57_2386) with
| (t', tm_u1) -> begin
(

let _57_2393 = (destruct_flex_t t')
in (match (_57_2393) with
| (_57_2388, u1, k1, _57_2392) -> begin
(

let sol = (let _156_1366 = (let _156_1365 = (u_abs k all_formals t')
in ((((u), (k))), (_156_1365)))
in TERM (_156_1366))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _57_2412 -> (match (_57_2412) with
| (x, _57_2411) -> begin
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
(let _156_1368 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _156_1368 formals tl))
end)
end)
end)
end
| _57_2416 -> begin
(failwith "Impossible")
end))
in (let _156_1369 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _156_1369 all_formals args))))
end))
end))
in (

let solve_both_pats = (fun wl _57_2423 _57_2428 r -> (match (((_57_2423), (_57_2428))) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _156_1378 = (solve_prob orig None [] wl)
in (solve env _156_1378))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _57_2433 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1383 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _156_1382 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _156_1381 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _156_1380 = (FStar_Syntax_Print.term_to_string k1)
in (let _156_1379 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _156_1383 _156_1382 _156_1381 _156_1380 _156_1379))))))
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
(let _156_1393 = (let _156_1392 = (FStar_Syntax_Print.term_to_string k)
in (let _156_1391 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _156_1390 = (FStar_Syntax_Print.args_to_string args)
in (FStar_Util.format3 "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution" _156_1392 _156_1391 _156_1390))))
in (failwith _156_1393))
end)))
in (

let _57_2475 = (

let _57_2443 = (let _156_1394 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k1)
in (FStar_Syntax_Util.arrow_formals _156_1394))
in (match (_57_2443) with
| (bs, k1') -> begin
(

let _57_2446 = (let _156_1395 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k2)
in (FStar_Syntax_Util.arrow_formals _156_1395))
in (match (_57_2446) with
| (cs, k2') -> begin
(

let k1'_xs = (let _156_1396 = (subst_of_list k1 bs args1)
in (FStar_Syntax_Subst.subst _156_1396 k1'))
in (

let k2'_ys = (let _156_1397 = (subst_of_list k2 cs args2)
in (FStar_Syntax_Subst.subst _156_1397 k2'))
in (

let sub_prob = (let _156_1399 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k2'_ys None "flex-flex kinding")
in (FStar_All.pipe_left (fun _156_1398 -> FStar_TypeChecker_Common.TProb (_156_1398)) _156_1399))
in (match ((let _156_1403 = (let _156_1400 = (FStar_Syntax_Subst.compress k1')
in _156_1400.FStar_Syntax_Syntax.n)
in (let _156_1402 = (let _156_1401 = (FStar_Syntax_Subst.compress k2')
in _156_1401.FStar_Syntax_Syntax.n)
in ((_156_1403), (_156_1402))))) with
| (FStar_Syntax_Syntax.Tm_type (_57_2451), _57_2454) -> begin
((k1'), ((sub_prob)::[]))
end
| (_57_2457, FStar_Syntax_Syntax.Tm_type (_57_2459)) -> begin
((k2'), ((sub_prob)::[]))
end
| _57_2463 -> begin
(

let _57_2467 = (FStar_Syntax_Util.type_u ())
in (match (_57_2467) with
| (t, _57_2466) -> begin
(

let _57_2471 = (new_uvar r zs t)
in (match (_57_2471) with
| (k_zs, _57_2470) -> begin
(

let kprob = (let _156_1405 = (mk_problem (p_scope orig) orig k1'_xs FStar_TypeChecker_Common.EQ k_zs None "flex-flex kinding")
in (FStar_All.pipe_left (fun _156_1404 -> FStar_TypeChecker_Common.TProb (_156_1404)) _156_1405))
in ((k_zs), ((sub_prob)::(kprob)::[])))
end))
end))
end))))
end))
end))
in (match (_57_2475) with
| (k_u', sub_probs) -> begin
(

let _57_2479 = (let _156_1411 = (let _156_1406 = (new_uvar r zs k_u')
in (FStar_All.pipe_left Prims.fst _156_1406))
in (let _156_1410 = (let _156_1407 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow xs _156_1407))
in (let _156_1409 = (let _156_1408 = (FStar_Syntax_Syntax.mk_Total k_u')
in (FStar_Syntax_Util.arrow ys _156_1408))
in ((_156_1411), (_156_1410), (_156_1409)))))
in (match (_57_2479) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _57_2483 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_57_2483) with
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

let _57_2489 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_57_2489) with
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

let solve_one_pat = (fun _57_2497 _57_2502 -> (match (((_57_2497), (_57_2502))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _57_2503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1417 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1416 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _156_1417 _156_1416)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun _57_2508 _57_2512 -> (match (((_57_2508), (_57_2512))) with
| ((a, _57_2507), (t2, _57_2511)) -> begin
(let _156_1422 = (let _156_1420 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _156_1420 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _156_1422 (fun _156_1421 -> FStar_TypeChecker_Common.TProb (_156_1421))))
end)) xs args2)
in (

let guard = (let _156_1424 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _156_1424))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _57_2522 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_57_2522) with
| (occurs_ok, _57_2521) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

let sol = (let _156_1426 = (let _156_1425 = (u_abs k1 xs t2)
in ((((u1), (k1))), (_156_1425)))
in TERM (_156_1426))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _57_2533 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_57_2533) with
| (sol, (_57_2528, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _57_2535 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _156_1427 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _156_1427))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _57_2540 -> begin
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

let _57_2545 = lhs
in (match (_57_2545) with
| (t1, u1, k1, args1) -> begin
(

let _57_2550 = rhs
in (match (_57_2550) with
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
| _57_2568 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _57_2572 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_57_2572) with
| (sol, _57_2571) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

let _57_2574 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _156_1428 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _156_1428))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _57_2579 -> begin
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
(let _156_1429 = (solve_prob orig None [] wl)
in (solve env _156_1429))
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _156_1430 = (solve_prob orig None [] wl)
in (solve env _156_1430))
end else begin
(

let _57_2583 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _156_1431 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _156_1431))
end else begin
()
end
in (

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

let mk_c = (fun c _57_26 -> (match (_57_26) with
| [] -> begin
c
end
| bs -> begin
(let _156_1436 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _156_1436))
end))
in (

let _57_2623 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_57_2623) with
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
in (let _156_1443 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _156_1442 -> FStar_TypeChecker_Common.CProb (_156_1442)) _156_1443)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _57_27 -> (match (_57_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (l)))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _57_2653 = (match_num_binders ((bs1), ((mk_t tbody1 lopt1))) ((bs2), ((mk_t tbody2 lopt2))))
in (match (_57_2653) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _156_1458 = (let _156_1457 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _156_1456 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _156_1457 problem.FStar_TypeChecker_Common.relation _156_1456 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _156_1455 -> FStar_TypeChecker_Common.TProb (_156_1455)) _156_1458))))
end)))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let is_abs = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_57_2672) -> begin
true
end
| _57_2675 -> begin
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
in (match ((let _156_1464 = (maybe_eta t1)
in (let _156_1463 = (maybe_eta t2)
in ((_156_1464), (_156_1463))))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(solve_t env (

let _57_2684 = problem
in {FStar_TypeChecker_Common.pid = _57_2684.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _57_2684.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _57_2684.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2684.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2684.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2684.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2684.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2684.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Util.Inl (t_abs), FStar_Util.Inr (not_abs))) | ((FStar_Util.Inr (not_abs), FStar_Util.Inl (t_abs))) -> begin
if ((is_flex not_abs) && ((p_rel orig) = FStar_TypeChecker_Common.EQ)) then begin
(let _156_1465 = (destruct_flex_pattern env not_abs)
in (solve_t_flex_rigid true orig _156_1465 t_abs wl))
end else begin
(giveup env "head tag mismatch: RHS is an abstraction" orig)
end
end
| _57_2695 -> begin
(failwith "Impossible: at least one side is an abstraction")
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_57_2697), FStar_Syntax_Syntax.Tm_refine (_57_2700)) -> begin
(

let _57_2705 = (as_refinement env wl t1)
in (match (_57_2705) with
| (x1, phi1) -> begin
(

let _57_2708 = (as_refinement env wl t2)
in (match (_57_2708) with
| (x2, phi2) -> begin
(

let base_prob = (let _156_1467 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _156_1466 -> FStar_TypeChecker_Common.TProb (_156_1466)) _156_1467))
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

let mk_imp = (fun imp phi1 phi2 -> (let _156_1484 = (imp phi1 phi2)
in (FStar_All.pipe_right _156_1484 (guard_on_element problem x1))))
in (

let fallback = (fun _57_2720 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _156_1487 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _156_1487 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let ref_prob = (let _156_1491 = (let _156_1490 = (let _156_1489 = (FStar_Syntax_Syntax.mk_binder x1)
in (_156_1489)::(p_scope orig))
in (mk_problem _156_1490 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _156_1488 -> FStar_TypeChecker_Common.TProb (_156_1488)) _156_1491))
in (match ((solve env (

let _57_2725 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _57_2725.ctr; defer_ok = false; smt_ok = _57_2725.smt_ok; tcenv = _57_2725.tcenv}))) with
| Failed (_57_2728) -> begin
(fallback ())
end
| Success (_57_2731) -> begin
(

let guard = (let _156_1494 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _156_1493 = (let _156_1492 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _156_1492 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _156_1494 _156_1493)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _57_2735 = wl
in {attempting = _57_2735.attempting; wl_deferred = _57_2735.wl_deferred; ctr = (wl.ctr + (Prims.parse_int "1")); defer_ok = _57_2735.defer_ok; smt_ok = _57_2735.smt_ok; tcenv = _57_2735.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _156_1496 = (destruct_flex_t t1)
in (let _156_1495 = (destruct_flex_t t2)
in (flex_flex orig _156_1496 _156_1495)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _156_1497 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false orig _156_1497 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_arrow (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
(solve_t' env (

let _57_2906 = problem
in {FStar_TypeChecker_Common.pid = _57_2906.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_2906.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _57_2906.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_2906.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2906.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2906.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2906.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2906.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2906.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
in if (let _156_1498 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _156_1498)) then begin
(let _156_1501 = (FStar_All.pipe_left (fun _156_1499 -> FStar_TypeChecker_Common.TProb (_156_1499)) (

let _57_2932 = problem
in {FStar_TypeChecker_Common.pid = _57_2932.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_2932.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _57_2932.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_2932.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2932.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2932.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2932.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2932.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2932.FStar_TypeChecker_Common.rank}))
in (let _156_1500 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _156_1501 _156_1500 t2 wl)))
end else begin
(

let _57_2936 = (base_and_refinement env wl t2)
in (match (_57_2936) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _156_1504 = (FStar_All.pipe_left (fun _156_1502 -> FStar_TypeChecker_Common.TProb (_156_1502)) (

let _57_2938 = problem
in {FStar_TypeChecker_Common.pid = _57_2938.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_2938.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _57_2938.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_2938.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2938.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2938.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2938.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2938.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2938.FStar_TypeChecker_Common.rank}))
in (let _156_1503 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid false _156_1504 _156_1503 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _57_2944 = y
in {FStar_Syntax_Syntax.ppname = _57_2944.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _57_2944.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _156_1506 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _156_1505 -> FStar_TypeChecker_Common.TProb (_156_1505)) _156_1506))
in (

let guard = (let _156_1507 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _156_1507 impl))
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

let _57_2977 = (base_and_refinement env wl t1)
in (match (_57_2977) with
| (t_base, _57_2976) -> begin
(solve_t env (

let _57_2978 = problem
in {FStar_TypeChecker_Common.pid = _57_2978.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _57_2978.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_2978.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2978.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2978.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2978.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2978.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2978.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_57_2981), _57_2984) -> begin
(

let t2 = (let _156_1508 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _156_1508))
in (solve_t env (

let _57_2987 = problem
in {FStar_TypeChecker_Common.pid = _57_2987.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_2987.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_2987.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _57_2987.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2987.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2987.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2987.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2987.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2987.FStar_TypeChecker_Common.rank}) wl))
end
| (_57_2990, FStar_Syntax_Syntax.Tm_refine (_57_2992)) -> begin
(

let t1 = (let _156_1509 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _156_1509))
in (solve_t env (

let _57_2996 = problem
in {FStar_TypeChecker_Common.pid = _57_2996.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _57_2996.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_2996.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_2996.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_2996.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_2996.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_2996.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_2996.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_2996.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

let head1 = (let _156_1510 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _156_1510 Prims.fst))
in (

let head2 = (let _156_1511 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _156_1511 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(

let uv1 = (FStar_Syntax_Free.uvars t1)
in (

let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(

let guard = if ((FStar_Syntax_Util.eq_tm t1 t2) = FStar_Syntax_Util.Equal) then begin
None
end else begin
(let _156_1513 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _156_1512 -> Some (_156_1512)) _156_1513))
end
in (let _156_1514 = (solve_prob orig guard [] wl)
in (solve env _156_1514)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _57_3077, _57_3079), _57_3083) -> begin
(solve_t' env (

let _57_3085 = problem
in {FStar_TypeChecker_Common.pid = _57_3085.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _57_3085.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_3085.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_3085.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_3085.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_3085.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_3085.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_3085.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_3085.FStar_TypeChecker_Common.rank}) wl)
end
| (_57_3088, FStar_Syntax_Syntax.Tm_ascribed (t2, _57_3091, _57_3093)) -> begin
(solve_t' env (

let _57_3097 = problem
in {FStar_TypeChecker_Common.pid = _57_3097.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_3097.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_3097.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _57_3097.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_3097.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_3097.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_3097.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_3097.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_3097.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _156_1517 = (let _156_1516 = (FStar_Syntax_Print.tag_of_term t1)
in (let _156_1515 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _156_1516 _156_1515)))
in (failwith _156_1517))
end
| _57_3136 -> begin
(giveup env "head tag mismatch" orig)
end)))
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

let _57_3151 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun _57_3156 _57_3160 -> (match (((_57_3156), (_57_3160))) with
| ((a1, _57_3155), (a2, _57_3159)) -> begin
(let _156_1536 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _156_1535 -> FStar_TypeChecker_Common.TProb (_156_1535)) _156_1536))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _156_1538 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _156_1538))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _57_3172))::[] -> begin
wp1
end
| _57_3176 -> begin
(let _156_1546 = (let _156_1545 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _156_1545))
in (failwith _156_1546))
end)
in (

let c1 = (let _156_1549 = (let _156_1548 = (let _156_1547 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _156_1547))
in (_156_1548)::[])
in {FStar_Syntax_Syntax.comp_univs = c1.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _156_1549; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _57_28 -> (match (_57_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _57_3184 -> begin
false
end))))
in (

let _57_3205 = (match (((c1.FStar_Syntax_Syntax.effect_args), (c2.FStar_Syntax_Syntax.effect_args))) with
| (((wp1, _57_3190))::_57_3187, ((wp2, _57_3197))::_57_3194) -> begin
((wp1), (wp2))
end
| _57_3202 -> begin
(let _156_1553 = (let _156_1552 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _156_1551 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _156_1552 _156_1551)))
in (failwith _156_1553))
end)
in (match (_57_3205) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _156_1554 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _156_1554 wl))
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if env.FStar_TypeChecker_Env.lax then begin
FStar_Syntax_Util.t_true
end else begin
if is_null_wp_2 then begin
(

let _57_3207 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _156_1564 = (let _156_1563 = (let _156_1562 = (let _156_1556 = (let _156_1555 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_156_1555)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _156_1556 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _156_1561 = (let _156_1560 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _156_1559 = (let _156_1558 = (let _156_1557 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_1557))
in (_156_1558)::[])
in (_156_1560)::_156_1559))
in ((_156_1562), (_156_1561))))
in FStar_Syntax_Syntax.Tm_app (_156_1563))
in (FStar_Syntax_Syntax.mk _156_1564 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _156_1576 = (let _156_1575 = (let _156_1574 = (let _156_1566 = (let _156_1565 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_156_1565)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _156_1566 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _156_1573 = (let _156_1572 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _156_1571 = (let _156_1570 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _156_1569 = (let _156_1568 = (let _156_1567 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_1567))
in (_156_1568)::[])
in (_156_1570)::_156_1569))
in (_156_1572)::_156_1571))
in ((_156_1574), (_156_1573))))
in FStar_Syntax_Syntax.Tm_app (_156_1575))
in (FStar_Syntax_Syntax.mk _156_1576 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
end
in (

let base_prob = (let _156_1578 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _156_1577 -> FStar_TypeChecker_Common.TProb (_156_1577)) _156_1578))
in (

let wl = (let _156_1582 = (let _156_1581 = (let _156_1580 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _156_1580 g))
in (FStar_All.pipe_left (fun _156_1579 -> Some (_156_1579)) _156_1581))
in (solve_prob orig _156_1582 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _156_1583 = (solve_prob orig None [] wl)
in (solve env _156_1583))
end else begin
(

let _57_3212 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1585 = (FStar_Syntax_Print.comp_to_string c1)
in (let _156_1584 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _156_1585 (rel_to_string problem.FStar_TypeChecker_Common.relation) _156_1584)))
end else begin
()
end
in (

let _57_3216 = (let _156_1587 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _156_1586 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in ((_156_1587), (_156_1586))))
in (match (_57_3216) with
| (c1, c2) -> begin
(match (((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n))) with
| (FStar_Syntax_Syntax.GTotal (t1, _57_3219), FStar_Syntax_Syntax.Total (t2, _57_3224)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _156_1588 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _156_1588 wl))
end
| (FStar_Syntax_Syntax.GTotal (_57_3229), FStar_Syntax_Syntax.Total (_57_3232)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.Total (t2, _))) | ((FStar_Syntax_Syntax.GTotal (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) | ((FStar_Syntax_Syntax.Total (t1, _), FStar_Syntax_Syntax.GTotal (t2, _))) -> begin
(let _156_1589 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _156_1589 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _156_1592 = (

let _57_3278 = problem
in (let _156_1591 = (let _156_1590 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _156_1590))
in {FStar_TypeChecker_Common.pid = _57_3278.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _156_1591; FStar_TypeChecker_Common.relation = _57_3278.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _57_3278.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _57_3278.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_3278.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_3278.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_3278.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_3278.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_3278.FStar_TypeChecker_Common.rank}))
in (solve_c env _156_1592 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _156_1595 = (

let _57_3294 = problem
in (let _156_1594 = (let _156_1593 = (FStar_TypeChecker_Normalize.comp_to_comp_typ env c2)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _156_1593))
in {FStar_TypeChecker_Common.pid = _57_3294.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _57_3294.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _57_3294.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _156_1594; FStar_TypeChecker_Common.element = _57_3294.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _57_3294.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _57_3294.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _57_3294.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _57_3294.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _57_3294.FStar_TypeChecker_Common.rank}))
in (solve_c env _156_1595 wl))
end
| (FStar_Syntax_Syntax.Comp (_57_3297), FStar_Syntax_Syntax.Comp (_57_3300)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _156_1596 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _156_1596 wl))
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

let _57_3307 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _156_1597 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _156_1597))) then begin
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _156_1602 = (let _156_1601 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _156_1600 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _156_1601 _156_1600)))
in (giveup env _156_1602 orig))
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


let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _156_1606 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _57_3327 -> (match (_57_3327) with
| (_57_3317, _57_3319, u, _57_3322, _57_3324, _57_3326) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _156_1606 (FStar_String.concat ", "))))


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match (((g.FStar_TypeChecker_Env.guard_f), (g.FStar_TypeChecker_Env.deferred))) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _57_3334 -> begin
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

let carry = (let _156_1612 = (FStar_List.map (fun _57_3342 -> (match (_57_3342) with
| (_57_3340, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _156_1612 (FStar_String.concat ",\n")))
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _57_3351; FStar_TypeChecker_Env.implicits = _57_3349} -> begin
true
end
| _57_3356 -> begin
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
| _57_3374 -> begin
(failwith "impossible")
end)
in (let _156_1633 = (

let _57_3376 = g
in (let _156_1632 = (let _156_1631 = (let _156_1630 = (let _156_1624 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_1624)::[])
in (let _156_1629 = (let _156_1628 = (let _156_1627 = (let _156_1625 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _156_1625 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _156_1627 (fun _156_1626 -> FStar_Util.Inl (_156_1626))))
in Some (_156_1628))
in (FStar_Syntax_Util.abs _156_1630 f _156_1629)))
in (FStar_All.pipe_left (fun _156_1623 -> FStar_TypeChecker_Common.NonTrivial (_156_1623)) _156_1631))
in {FStar_TypeChecker_Env.guard_f = _156_1632; FStar_TypeChecker_Env.deferred = _57_3376.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3376.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3376.FStar_TypeChecker_Env.implicits}))
in Some (_156_1633)))
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _57_3383 = g
in (let _156_1644 = (let _156_1643 = (let _156_1642 = (let _156_1641 = (let _156_1640 = (let _156_1639 = (FStar_Syntax_Syntax.as_arg e)
in (_156_1639)::[])
in ((f), (_156_1640)))
in FStar_Syntax_Syntax.Tm_app (_156_1641))
in (FStar_Syntax_Syntax.mk _156_1642 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _156_1638 -> FStar_TypeChecker_Common.NonTrivial (_156_1638)) _156_1643))
in {FStar_TypeChecker_Env.guard_f = _156_1644; FStar_TypeChecker_Env.deferred = _57_3383.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3383.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3383.FStar_TypeChecker_Env.implicits}))
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_57_3388) -> begin
(failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _156_1651 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_156_1651))
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _57_3406 -> begin
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


let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _156_1674 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _156_1674; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let _57_3433 = g
in (let _156_1689 = (let _156_1688 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _156_1688 (fun _156_1687 -> FStar_TypeChecker_Common.NonTrivial (_156_1687))))
in {FStar_TypeChecker_Env.guard_f = _156_1689; FStar_TypeChecker_Env.deferred = _57_3433.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3433.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3433.FStar_TypeChecker_Env.implicits}))
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _156_1697 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _156_1696 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _156_1697 (rel_to_string rel) _156_1696)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

let x = (let _156_1708 = (let _156_1707 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _156_1706 -> Some (_156_1706)) _156_1707))
in (FStar_Syntax_Syntax.new_bv _156_1708 t1))
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

let p = (let _156_1712 = (let _156_1710 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _156_1709 -> Some (_156_1709)) _156_1710))
in (let _156_1711 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _156_1712 _156_1711)))
in ((FStar_TypeChecker_Common.TProb (p)), (x))))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _57_3453 = probs
in {attempting = _57_3453.attempting; wl_deferred = _57_3453.wl_deferred; ctr = _57_3453.ctr; defer_ok = false; smt_ok = _57_3453.smt_ok; tcenv = _57_3453.tcenv})
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

let _57_3460 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _57_3466 = (FStar_Unionfind.rollback tx)
in (

let _57_3468 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _156_1724 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _156_1724))
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

let _57_3475 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _156_1729 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _156_1729))
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

let _57_3478 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _156_1730 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _156_1730))
end else begin
()
end
in (

let f = (match ((let _156_1731 = (FStar_Syntax_Util.unmeta f)
in _156_1731.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _57_3483 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

let _57_3485 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _57_3485.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3485.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3485.FStar_TypeChecker_Env.implicits})))))
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _156_1743 = (let _156_1742 = (let _156_1741 = (let _156_1740 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _156_1740 (fun _156_1739 -> FStar_TypeChecker_Common.NonTrivial (_156_1739))))
in {FStar_TypeChecker_Env.guard_f = _156_1741; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _156_1742))
in (FStar_All.pipe_left (fun _156_1738 -> Some (_156_1738)) _156_1743))
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

let _57_3496 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1751 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1750 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _156_1751 _156_1750)))
end else begin
()
end
in (

let prob = (let _156_1754 = (let _156_1753 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _156_1753))
in (FStar_All.pipe_left (fun _156_1752 -> FStar_TypeChecker_Common.TProb (_156_1752)) _156_1754))
in (

let g = (let _156_1757 = (let _156_1756 = (singleton env prob)
in (solve_and_commit env _156_1756 (fun _57_3499 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _156_1757))
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _156_1767 = (let _156_1766 = (let _156_1765 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _156_1764 = (FStar_TypeChecker_Env.get_range env)
in ((_156_1765), (_156_1764))))
in FStar_Syntax_Syntax.Error (_156_1766))
in (Prims.raise _156_1767))
end
| Some (g) -> begin
(

let _57_3508 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1770 = (FStar_Syntax_Print.term_to_string t1)
in (let _156_1769 = (FStar_Syntax_Print.term_to_string t2)
in (let _156_1768 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _156_1770 _156_1769 _156_1768))))
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

let _57_3514 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1780 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _156_1779 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _156_1780 _156_1779)))
end else begin
()
end
in (

let _57_3518 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_57_3518) with
| (prob, x) -> begin
(

let g = (let _156_1783 = (let _156_1782 = (singleton' env prob smt_ok)
in (solve_and_commit env _156_1782 (fun _57_3519 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _156_1783))
in (

let _57_3522 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _156_1787 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _156_1786 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _156_1785 = (let _156_1784 = (FStar_Util.must g)
in (guard_to_string env _156_1784))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _156_1787 _156_1786 _156_1785))))
end else begin
()
end
in (abstract_guard x g)))
end))))


let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env e t1 t2 -> (let _156_1803 = (FStar_TypeChecker_Env.get_range env)
in (let _156_1802 = (FStar_TypeChecker_Errors.basic_type_error env (Some (e)) t2 t1)
in (FStar_TypeChecker_Errors.report _156_1803 _156_1802))))


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

let _57_3534 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1811 = (FStar_Syntax_Print.comp_to_string c1)
in (let _156_1810 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _156_1811 _156_1810)))
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

let prob = (let _156_1814 = (let _156_1813 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _156_1813 "sub_comp"))
in (FStar_All.pipe_left (fun _156_1812 -> FStar_TypeChecker_Common.CProb (_156_1812)) _156_1814))
in (let _156_1817 = (let _156_1816 = (singleton env prob)
in (solve_and_commit env _156_1816 (fun _57_3538 -> None)))
in (FStar_All.pipe_left (with_guard env prob) _156_1817))))))


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

let _57_3547 = (FStar_Unionfind.rollback tx)
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _156_1835 = (let _156_1834 = (let _156_1833 = (let _156_1831 = (FStar_Syntax_Print.univ_to_string u1)
in (let _156_1830 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _156_1831 _156_1830 msg)))
in (let _156_1832 = (FStar_TypeChecker_Env.get_range env)
in ((_156_1833), (_156_1832))))
in FStar_Syntax_Syntax.Error (_156_1834))
in (Prims.raise _156_1835)))))
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
(((uv), ((u1)::[])))::[]
end
| (hd)::tl -> begin
(

let _57_3563 = hd
in (match (_57_3563) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
(((uv'), ((u1)::lower_bounds)))::tl
end else begin
(let _156_1842 = (insert uv u1 tl)
in (hd)::_156_1842)
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
(let _156_1847 = (insert uv u1 out)
in (group_by _156_1847 rest))
end)
end
| _57_3578 -> begin
None
end))
end))
in (

let ad_hoc_fallback = (fun _57_3580 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _57_3583 -> begin
(

let wl = (

let _57_3584 = (empty_worklist env)
in {attempting = _57_3584.attempting; wl_deferred = _57_3584.wl_deferred; ctr = _57_3584.ctr; defer_ok = true; smt_ok = _57_3584.smt_ok; tcenv = _57_3584.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _57_3589 -> (match (_57_3589) with
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _57_3594 -> begin
(match ((solve_universe_eq (~- ((Prims.parse_int "1"))) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _57_3604 -> begin
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _57_3609 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _57_29 -> (match (_57_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

let _57_3616 = (FStar_Syntax_Util.univ_kernel u)
in (match (_57_3616) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _57_3620 = (FStar_Syntax_Util.univ_kernel u')
in (match (_57_3620) with
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
| USolved (_57_3622) -> begin
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

let _57_3626 = (empty_worklist env)
in {attempting = _57_3626.attempting; wl_deferred = _57_3626.wl_deferred; ctr = _57_3626.ctr; defer_ok = false; smt_ok = _57_3626.smt_ok; tcenv = _57_3626.tcenv})
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
| _57_3641 -> begin
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

let _57_3646 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

let fail = (fun _57_3653 -> (match (_57_3653) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

let _57_3656 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_1868 = (wl_to_string wl)
in (let _156_1867 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _156_1868 _156_1867)))
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

let _57_3660 = g
in {FStar_TypeChecker_Env.guard_f = _57_3660.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _57_3660.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3660.FStar_TypeChecker_Env.implicits})
end
| _57_3663 -> begin
(failwith "impossible: Unexpected deferred constraints remain")
end)
in (

let _57_3665 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _57_3667 = g
in {FStar_TypeChecker_Env.guard_f = _57_3667.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_3667.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _57_3667.FStar_TypeChecker_Env.implicits})))))))


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

let _57_3684 = if (not ((FStar_TypeChecker_Env.should_verify env))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let _57_3676 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Norm"))) then begin
(let _156_1885 = (FStar_TypeChecker_Env.get_range env)
in (let _156_1884 = (let _156_1883 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Before normalization VC=\n%s\n" _156_1883))
in (FStar_TypeChecker_Errors.diag _156_1885 _156_1884)))
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

let _57_3682 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _156_1888 = (FStar_TypeChecker_Env.get_range env)
in (let _156_1887 = (let _156_1886 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _156_1886))
in (FStar_TypeChecker_Errors.diag _156_1888 _156_1887)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end)))
end)
end
in (

let _57_3686 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_3686.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3686.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3686.FStar_TypeChecker_Env.implicits}))))


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _57_3695 -> begin
false
end))
in (

let rec until_fixpoint = (fun acc implicits -> (

let _57_3701 = acc
in (match (_57_3701) with
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

let _57_3713 = hd
in (match (_57_3713) with
| (_57_3707, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint (((hd)::out), (changed)) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

let _57_3716 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _156_1904 = (FStar_Syntax_Print.uvar_to_string u)
in (let _156_1903 = (FStar_Syntax_Print.term_to_string tm)
in (let _156_1902 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _156_1904 _156_1903 _156_1902))))
end else begin
()
end
in (

let _57_3725 = (env.FStar_TypeChecker_Env.type_of (

let _57_3718 = env
in {FStar_TypeChecker_Env.solver = _57_3718.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _57_3718.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _57_3718.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _57_3718.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _57_3718.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _57_3718.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _57_3718.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _57_3718.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _57_3718.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _57_3718.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _57_3718.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _57_3718.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _57_3718.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _57_3718.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _57_3718.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _57_3718.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _57_3718.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _57_3718.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = _57_3718.FStar_TypeChecker_Env.lax; FStar_TypeChecker_Env.lax_universes = _57_3718.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _57_3718.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _57_3718.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _57_3718.FStar_TypeChecker_Env.qname_and_index}) tm)
in (match (_57_3725) with
| (_57_3721, _57_3723, g) -> begin
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

let _57_3726 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _57_3726.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3726.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _57_3726.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (

let g' = (discharge_guard' (Some ((fun _57_3729 -> (match (()) with
| () -> begin
(FStar_Syntax_Print.term_to_string tm)
end)))) env g)
in (until_fixpoint (((FStar_List.append g'.FStar_TypeChecker_Env.implicits out)), (true)) tl)))
end)))))
end
end))
end)
end)))
in (

let _57_3731 = g
in (let _156_1908 = (until_fixpoint (([]), (false)) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _57_3731.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_3731.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _57_3731.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _156_1908})))))


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

let g = (let _156_1913 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _156_1913 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _156_1914 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _156_1914))
end
| ((reason, _57_3741, _57_3743, e, t, r))::_57_3738 -> begin
(let _156_1917 = (let _156_1916 = (FStar_Syntax_Print.term_to_string t)
in (let _156_1915 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _156_1916 _156_1915 reason)))
in (FStar_TypeChecker_Errors.report r _156_1917))
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

let _57_3751 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _57_3751.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _57_3751.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = (((u1), (u2)))::[]; FStar_TypeChecker_Env.implicits = _57_3751.FStar_TypeChecker_Env.implicits}))






open Prims

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (

let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _55_38 -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (

let k' = (let _146_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _146_7))
in (

let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _146_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_146_8, uv)))))
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
| TERM (_55_44) -> begin
_55_44
end))


let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_47) -> begin
_55_47
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
| Success (_55_57) -> begin
_55_57
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_60) -> begin
_55_60
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


let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))


let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _146_109 = (let _146_108 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _146_107 = (let _146_106 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _146_105 = (let _146_104 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _146_103 = (let _146_102 = (let _146_101 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _146_100 = (let _146_99 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _146_98 = (let _146_97 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _146_96 = (let _146_95 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_146_95)::[])
in (_146_97)::_146_96))
in (_146_99)::_146_98))
in (_146_101)::_146_100))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_146_102)
in (_146_104)::_146_103))
in (_146_106)::_146_105))
in (_146_108)::_146_107))
in (FStar_Util.format "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _146_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _146_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _146_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _146_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _146_110)))
end))


let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _146_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _146_116 FStar_Util.string_of_int))
end
in (let _146_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _146_117)))
end
| TERM ((u, _55_84), t) -> begin
(

let x = if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _146_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _146_118 FStar_Util.string_of_int))
end
in (let _146_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _146_119)))
end))


let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _146_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _146_124 (FStar_String.concat ", "))))


let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _146_128 = (let _146_127 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _146_127 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _146_128 (FStar_String.concat ", "))))


let args_to_string = (fun args -> (let _146_131 = (FStar_All.pipe_right args (FStar_List.map (fun _55_97 -> (match (_55_97) with
| (x, _55_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _146_131 (FStar_String.concat " "))))


let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})


let singleton' : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.bool  ->  worklist = (fun env prob smt_ok -> (

let _55_102 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_102.wl_deferred; ctr = _55_102.ctr; defer_ok = _55_102.defer_ok; smt_ok = smt_ok; tcenv = _55_102.tcenv}))


let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (singleton' env prob true))


let wl_of_guard = (fun env g -> (

<<<<<<< HEAD
let _55_108 = (empty_worklist env)
in (let _145_144 = (FStar_List.map Prims.snd g)
in {attempting = _145_144; wl_deferred = _55_108.wl_deferred; ctr = _55_108.ctr; defer_ok = false; smt_ok = _55_108.smt_ok; tcenv = _55_108.tcenv})))
=======
let _55_105 = (empty_worklist env)
in (let _146_140 = (FStar_List.map Prims.snd g)
in {attempting = _146_140; wl_deferred = _55_105.wl_deferred; ctr = _55_105.ctr; defer_ok = false; smt_ok = _55_105.smt_ok; tcenv = _55_105.tcenv})))
>>>>>>> master


let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _55_113 = wl
in {attempting = _55_113.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _55_113.ctr; defer_ok = _55_113.defer_ok; smt_ok = _55_113.smt_ok; tcenv = _55_113.tcenv}))


let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _55_117 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_117.wl_deferred; ctr = _55_117.ctr; defer_ok = _55_117.defer_ok; smt_ok = _55_117.smt_ok; tcenv = _55_117.tcenv}))


let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (

<<<<<<< HEAD
let _55_122 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_161 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _145_161))
=======
let _55_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_157 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _146_157))
>>>>>>> master
end else begin
()
end
in Failed ((prob, reason))))


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

let _55_129 = p
in {FStar_TypeChecker_Common.pid = _55_129.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_129.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_129.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_129.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_129.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_129.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_129.FStar_TypeChecker_Common.rank}))


let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
<<<<<<< HEAD
(FStar_All.pipe_right (maybe_invert p) (fun _145_168 -> FStar_TypeChecker_Common.TProb (_145_168)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _145_169 -> FStar_TypeChecker_Common.CProb (_145_169)))
=======
(FStar_All.pipe_right (maybe_invert p) (fun _146_164 -> FStar_TypeChecker_Common.TProb (_146_164)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _146_165 -> FStar_TypeChecker_Common.CProb (_146_165)))
>>>>>>> master
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
<<<<<<< HEAD
(FStar_All.pipe_left (fun _145_188 -> FStar_TypeChecker_Common.TProb (_145_188)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _145_189 -> FStar_TypeChecker_Common.CProb (_145_189)) (invert p))
=======
(FStar_All.pipe_left (fun _146_184 -> FStar_TypeChecker_Common.TProb (_146_184)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _146_185 -> FStar_TypeChecker_Common.CProb (_146_185)) (invert p))
>>>>>>> master
end))


let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))


let next_pid : Prims.unit  ->  Prims.int = (

let ctr = (FStar_ST.alloc 0)
in (fun _55_179 -> (match (()) with
| () -> begin
(

let _55_180 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))


<<<<<<< HEAD
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _145_202 = (next_pid ())
in (let _145_201 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _145_202; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_201; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))
=======
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _146_198 = (next_pid ())
in (let _146_197 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _146_198; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _146_197; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))
>>>>>>> master


let new_problem = (fun env lhs rel rhs elt loc reason -> (

let scope = (FStar_TypeChecker_Env.all_binders env)
<<<<<<< HEAD
in (let _145_212 = (next_pid ())
in (let _145_211 = (let _145_210 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _145_210 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _145_212; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_211; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _145_219 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _145_219; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))
=======
in (let _146_208 = (next_pid ())
in (let _146_207 = (let _146_206 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _146_206 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _146_208; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _146_207; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _146_215 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _146_215; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))
>>>>>>> master


let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))


let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
<<<<<<< HEAD
(let _145_231 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _145_230 = (prob_to_string env d)
in (let _145_229 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _145_231 _145_230 _145_229 s))))
=======
(let _146_227 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _146_226 = (prob_to_string env d)
in (let _146_225 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _146_227 _146_226 _146_225 s))))
>>>>>>> master
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
| _55_216 -> begin
(FStar_All.failwith "impossible")
end)
in (

let _55_224 = (match (d) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
<<<<<<< HEAD
(let _145_233 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.lhs)
in (let _145_232 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.rhs)
in (_145_233, _145_232)))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _145_235 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.lhs)
in (let _145_234 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.rhs)
in (_145_235, _145_234)))
=======
(let _146_229 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.lhs)
in (let _146_228 = (FStar_Syntax_Print.term_to_string tp.FStar_TypeChecker_Common.rhs)
in (_146_229, _146_228)))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _146_231 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.lhs)
in (let _146_230 = (FStar_Syntax_Print.comp_to_string cp.FStar_TypeChecker_Common.rhs)
in (_146_231, _146_230)))
>>>>>>> master
end)
in (match (_55_224) with
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
| _55_234 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_237), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))


let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_246) -> begin
None
end
| TERM ((u, _55_250), t) -> begin
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
| _55_263 -> begin
None
end))))


<<<<<<< HEAD
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_254 = (let _145_253 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _145_253))
in (FStar_Syntax_Subst.compress _145_254)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_259 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _145_259)))


let norm_arg = (fun env t -> (let _145_262 = (sn env (Prims.fst t))
in (_145_262, (Prims.snd t))))
=======
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_250 = (let _146_249 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _146_249))
in (FStar_Syntax_Subst.compress _146_250)))


let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _146_255 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _146_255)))


let norm_arg = (fun env t -> (let _146_258 = (sn env (Prims.fst t))
in (_146_258, (Prims.snd t))))
>>>>>>> master


let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_274 -> (match (_55_274) with
| (x, imp) -> begin
<<<<<<< HEAD
(let _145_269 = (

let _55_275 = x
in (let _145_268 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_275.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_275.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_268}))
in (_145_269, imp))
=======
(let _146_265 = (

let _55_272 = x
in (let _146_264 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_272.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_272.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_264}))
in (_146_265, imp))
>>>>>>> master
end)))))


let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
<<<<<<< HEAD
(let _145_276 = (aux u)
in FStar_Syntax_Syntax.U_succ (_145_276))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _145_277 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_145_277))
=======
(let _146_272 = (aux u)
in FStar_Syntax_Syntax.U_succ (_146_272))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _146_273 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_146_273))
>>>>>>> master
end
| _55_287 -> begin
u
end)))
<<<<<<< HEAD
in (let _145_278 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _145_278))))
=======
in (let _146_274 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _146_274))))
>>>>>>> master


let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))


let base_and_refinement = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_307; FStar_Syntax_Syntax.pos = _55_305; FStar_Syntax_Syntax.vars = _55_303} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
<<<<<<< HEAD
(let _145_292 = (let _145_291 = (FStar_Syntax_Print.term_to_string tt)
in (let _145_290 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _145_291 _145_290)))
in (FStar_All.failwith _145_292))
=======
(let _146_288 = (let _146_287 = (FStar_Syntax_Print.term_to_string tt)
in (let _146_286 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _146_287 _146_286)))
in (FStar_All.failwith _146_288))
>>>>>>> master
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
<<<<<<< HEAD
in (match ((let _145_293 = (FStar_Syntax_Subst.compress t1')
in _145_293.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_325) -> begin
=======
in (match ((let _146_289 = (FStar_Syntax_Subst.compress t1')
in _146_289.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_322) -> begin
>>>>>>> master
(aux true t1')
end
| _55_328 -> begin
(t1, None)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
<<<<<<< HEAD
(let _145_296 = (let _145_295 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_294 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _145_295 _145_294)))
in (FStar_All.failwith _145_296))
end))
in (let _145_297 = (whnf env t1)
in (aux false _145_297))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _145_302 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _145_302 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _145_305 = (FStar_Syntax_Syntax.null_bv t)
in (_145_305, FStar_Syntax_Util.t_true)))
=======
(let _146_292 = (let _146_291 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_290 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _146_291 _146_290)))
in (FStar_All.failwith _146_292))
end))
in (let _146_293 = (whnf env t1)
in (aux false _146_293))))


let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _146_298 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _146_298 Prims.fst)))


let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _146_301 = (FStar_Syntax_Syntax.null_bv t)
in (_146_301, FStar_Syntax_Util.t_true)))
>>>>>>> master


let as_refinement = (fun env wl t -> (

let _55_374 = (base_and_refinement env wl t)
in (match (_55_374) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))


let force_refinement = (fun _55_382 -> (match (_55_382) with
| (t_base, refopt) -> begin
(

let _55_390 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_390) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))


let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
<<<<<<< HEAD
(let _145_318 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_317 = (let _145_314 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _145_314))
in (let _145_316 = (let _145_315 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _145_315))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_318 _145_317 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_316))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _145_321 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_320 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_319 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_321 _145_320 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_319))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _145_327 = (let _145_326 = (let _145_325 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_403 -> (match (_55_403) with
| (_55_399, _55_401, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _145_325))
in (FStar_List.map (wl_prob_to_string wl) _145_326))
in (FStar_All.pipe_right _145_327 (FStar_String.concat "\n\t"))))
=======
(let _146_314 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _146_313 = (let _146_310 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _146_310))
in (let _146_312 = (let _146_311 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _146_311))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _146_314 _146_313 (rel_to_string p.FStar_TypeChecker_Common.relation) _146_312))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _146_317 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _146_316 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _146_315 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _146_317 _146_316 (rel_to_string p.FStar_TypeChecker_Common.relation) _146_315))))
end))


let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _146_323 = (let _146_322 = (let _146_321 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_400 -> (match (_55_400) with
| (_55_396, _55_398, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _146_321))
in (FStar_List.map (wl_prob_to_string wl) _146_322))
in (FStar_All.pipe_right _146_323 (FStar_String.concat "\n\t"))))
>>>>>>> master


let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (

<<<<<<< HEAD
let _55_422 = (match ((let _145_334 = (FStar_Syntax_Subst.compress k)
in _145_334.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _145_335 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _145_335))
=======
let _55_419 = (match ((let _146_330 = (FStar_Syntax_Subst.compress k)
in _146_330.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _146_331 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _146_331))
>>>>>>> master
end else begin
(

let _55_413 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_413) with
| (ys', t) -> begin
<<<<<<< HEAD
(let _145_336 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _145_336))
end))
end
end
| _55_415 -> begin
(let _145_338 = (let _145_337 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _145_337))
in ((ys, t), _145_338))
=======
(let _146_332 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _146_332))
end))
end
end
| _55_412 -> begin
(let _146_334 = (let _146_333 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _146_333))
in ((ys, t), _146_334))
>>>>>>> master
end)
in (match (_55_422) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(

<<<<<<< HEAD
let c = (let _145_339 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _145_339 c))
in (let _145_343 = (let _145_342 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_340 -> FStar_Util.Inl (_145_340)))
in (FStar_All.pipe_right _145_342 (fun _145_341 -> Some (_145_341))))
in (FStar_Syntax_Util.abs ys t _145_343)))
=======
let c = (let _146_335 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _146_335 c))
in (let _146_339 = (let _146_338 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _146_336 -> FStar_Util.Inl (_146_336)))
in (FStar_All.pipe_right _146_338 (fun _146_337 -> Some (_146_337))))
in (FStar_Syntax_Util.abs ys t _146_339)))
>>>>>>> master
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

let _55_436 = (p_guard prob)
in (match (_55_436) with
| (_55_434, uv) -> begin
(

<<<<<<< HEAD
let _55_447 = (match ((let _145_354 = (FStar_Syntax_Subst.compress uv)
in _145_354.FStar_Syntax_Syntax.n)) with
=======
let _55_444 = (match ((let _146_350 = (FStar_Syntax_Subst.compress uv)
in _146_350.FStar_Syntax_Syntax.n)) with
>>>>>>> master
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(

let bs = (p_scope prob)
in (

let phi = (u_abs k bs phi)
in (

<<<<<<< HEAD
let _55_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _145_357 = (FStar_Util.string_of_int (p_pid prob))
in (let _145_356 = (FStar_Syntax_Print.term_to_string uv)
in (let _145_355 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _145_357 _145_356 _145_355))))
=======
let _55_440 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _146_353 = (FStar_Util.string_of_int (p_pid prob))
in (let _146_352 = (FStar_Syntax_Print.term_to_string uv)
in (let _146_351 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _146_353 _146_352 _146_351))))
>>>>>>> master
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _55_446 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (

let _55_449 = (commit uvis)
in (

let _55_451 = wl
in {attempting = _55_451.attempting; wl_deferred = _55_451.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_451.defer_ok; smt_ok = _55_451.smt_ok; tcenv = _55_451.tcenv})))
end))))


let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (

<<<<<<< HEAD
let _55_456 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_366 = (FStar_Util.string_of_int pid)
in (let _145_365 = (let _145_364 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _145_364 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_366 _145_365)))
=======
let _55_453 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_362 = (FStar_Util.string_of_int pid)
in (let _146_361 = (let _146_360 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _146_360 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _146_362 _146_361)))
>>>>>>> master
end else begin
()
end
in (

let _55_458 = (commit sol)
in (

let _55_460 = wl
in {attempting = _55_460.attempting; wl_deferred = _55_460.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_460.defer_ok; smt_ok = _55_460.smt_ok; tcenv = _55_460.tcenv}))))


let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (

let conj_guard = (fun t g -> (match ((t, g)) with
| (_55_470, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
<<<<<<< HEAD
(let _145_379 = (FStar_Syntax_Util.mk_conj t f)
in Some (_145_379))
end))
in (

let _55_482 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_382 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _145_381 = (let _145_380 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _145_380 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_382 _145_381)))
=======
(let _146_375 = (FStar_Syntax_Util.mk_conj t f)
in Some (_146_375))
end))
in (

let _55_479 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_378 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _146_377 = (let _146_376 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _146_376 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _146_378 _146_377)))
>>>>>>> master
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))


<<<<<<< HEAD
let rec occurs = (fun wl uk t -> (let _145_392 = (let _145_390 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _145_390 FStar_Util.set_elements))
in (FStar_All.pipe_right _145_392 (FStar_Util.for_some (fun _55_491 -> (match (_55_491) with
| (uv, _55_490) -> begin
=======
let rec occurs = (fun wl uk t -> (let _146_388 = (let _146_386 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _146_386 FStar_Util.set_elements))
in (FStar_All.pipe_right _146_388 (FStar_Util.for_some (fun _55_488 -> (match (_55_488) with
| (uv, _55_487) -> begin
>>>>>>> master
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))


let occurs_check = (fun env wl uk t -> (

let occurs_ok = (not ((occurs wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
<<<<<<< HEAD
(let _145_399 = (let _145_398 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _145_397 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _145_398 _145_397)))
in Some (_145_399))
=======
(let _146_395 = (let _146_394 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _146_393 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _146_394 _146_393)))
in Some (_146_395))
>>>>>>> master
end
in (occurs_ok, msg))))


let occurs_and_freevars_check = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Syntax_Free.names t)
in (

let _55_506 = (occurs_check env wl uk t)
in (match (_55_506) with
| (occurs_ok, msg) -> begin
<<<<<<< HEAD
(let _145_405 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _145_405, (msg, fvs, fvs_t)))
=======
(let _146_401 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _146_401, (msg, fvs, fvs_t)))
>>>>>>> master
end))))


let intersect_vars = (fun v1 v2 -> (

let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (

let v1_set = (as_set v1)
in (

let _55_524 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_516 _55_519 -> (match ((_55_516, _55_519)) with
| ((isect, isect_set), (x, imp)) -> begin
<<<<<<< HEAD
if (let _145_414 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _145_414)) then begin
=======
if (let _146_410 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _146_410)) then begin
>>>>>>> master
(isect, isect_set)
end else begin
(

let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
<<<<<<< HEAD
(let _145_415 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _145_415))
=======
(let _146_411 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _146_411))
>>>>>>> master
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_55_524) with
| (isect, _55_523) -> begin
(FStar_List.rev isect)
end)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_530 _55_534 -> (match ((_55_530, _55_534)) with
| ((a, _55_529), (b, _55_533)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_544 -> (match (_55_544) with
| (b, _55_543) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _55_546 -> begin
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

<<<<<<< HEAD
let _55_555 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_430 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _145_430))
=======
let _55_552 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_426 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _146_426))
>>>>>>> master
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))


let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_569; FStar_Syntax_Syntax.pos = _55_567; FStar_Syntax_Syntax.vars = _55_565}, args) -> begin
(t, uv, k, args)
end
| _55_579 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _55_586 = (destruct_flex_t t)
in (match (_55_586) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _55_590 -> begin
((t, uv, k, args), None)
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
| MisMatch (_55_593) -> begin
_55_593
end))


let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _55_600 -> begin
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
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch ((Some ((fv_delta_depth env f)), Some ((fv_delta_depth env g))))
end
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_686), FStar_Syntax_Syntax.Tm_uinst (g, _55_691)) -> begin
(let _145_466 = (head_matches env f g)
in (FStar_All.pipe_right _145_466 head_match))
=======
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_683), FStar_Syntax_Syntax.Tm_uinst (g, _55_688)) -> begin
(let _146_462 = (head_matches env f g)
in (FStar_All.pipe_right _146_462 head_match))
>>>>>>> master
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_702), FStar_Syntax_Syntax.Tm_uvar (uv', _55_707)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.Tm_refine (x, _55_713), FStar_Syntax_Syntax.Tm_refine (y, _55_718)) -> begin
(let _145_467 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_467 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_724), _55_728) -> begin
(let _145_468 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _145_468 head_match))
end
| (_55_731, FStar_Syntax_Syntax.Tm_refine (x, _55_734)) -> begin
(let _145_469 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_469 head_match))
=======
| (FStar_Syntax_Syntax.Tm_refine (x, _55_710), FStar_Syntax_Syntax.Tm_refine (y, _55_715)) -> begin
(let _146_463 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_463 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_721), _55_725) -> begin
(let _146_464 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _146_464 head_match))
end
| (_55_728, FStar_Syntax_Syntax.Tm_refine (x, _55_731)) -> begin
(let _146_465 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _146_465 head_match))
>>>>>>> master
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
<<<<<<< HEAD
| (FStar_Syntax_Syntax.Tm_app (head, _55_754), FStar_Syntax_Syntax.Tm_app (head', _55_759)) -> begin
(let _145_470 = (head_matches env head head')
in (FStar_All.pipe_right _145_470 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_765), _55_769) -> begin
(let _145_471 = (head_matches env head t2)
in (FStar_All.pipe_right _145_471 head_match))
end
| (_55_772, FStar_Syntax_Syntax.Tm_app (head, _55_775)) -> begin
(let _145_472 = (head_matches env t1 head)
in (FStar_All.pipe_right _145_472 head_match))
end
| _55_780 -> begin
(let _145_475 = (let _145_474 = (delta_depth_of_term env t1)
in (let _145_473 = (delta_depth_of_term env t2)
in (_145_474, _145_473)))
in MisMatch (_145_475))
=======
| (FStar_Syntax_Syntax.Tm_app (head, _55_751), FStar_Syntax_Syntax.Tm_app (head', _55_756)) -> begin
(let _146_466 = (head_matches env head head')
in (FStar_All.pipe_right _146_466 head_match))
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_762), _55_766) -> begin
(let _146_467 = (head_matches env head t2)
in (FStar_All.pipe_right _146_467 head_match))
end
| (_55_769, FStar_Syntax_Syntax.Tm_app (head, _55_772)) -> begin
(let _146_468 = (head_matches env t1 head)
in (FStar_All.pipe_right _146_468 head_match))
end
| _55_777 -> begin
(let _146_471 = (let _146_470 = (delta_depth_of_term env t1)
in (let _146_469 = (delta_depth_of_term env t2)
in (_146_470, _146_469)))
in MisMatch (_146_471))
>>>>>>> master
end))))


let head_matches_delta = (fun env wl t1 t2 -> (

let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (

let fail = (fun r -> (r, None))
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
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(

let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (

let _55_831 = if d1_greater_than_d2 then begin
(

let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(

let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
<<<<<<< HEAD
in (let _145_496 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _145_496)))
=======
in (let _146_492 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _146_492)))
>>>>>>> master
end
in (match (_55_831) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_55_833) -> begin
(fail r)
end
| _55_836 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))


type tc =
| T of FStar_Syntax_Syntax.term
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
| T (_55_839) -> begin
_55_839
end))


let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_842) -> begin
_55_842
end))


type tcs =
tc Prims.list


let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (

let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_849) -> begin
false
end
| _55_852 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_55_862, imp), T (t)) -> begin
(t, imp)
end
| _55_869 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (

let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_874 -> (match (_55_874) with
| (t, _55_873) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let fail = (fun _55_881 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let _55_884 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_884) with
| (bs, c) -> begin
(

let rebuild = (fun tcs -> (

let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| (((x, imp))::bs, (T (t))::tcs) -> begin
(aux ((((

let _55_901 = x
in {FStar_Syntax_Syntax.ppname = _55_901.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_901.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], (C (c))::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_909 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (

let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| (hd)::rest -> begin
(decompose (((Some (hd), CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest)
end))
<<<<<<< HEAD
in (let _145_578 = (decompose [] bs)
in (rebuild, matches, _145_578))))
=======
in (let _146_574 = (decompose [] bs)
in (rebuild, matches, _146_574))))
>>>>>>> master
end)))
end
| _55_918 -> begin
(

let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_922 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))


let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t) -> begin
t
end
| _55_929 -> begin
(FStar_All.failwith "Impossible")
end))


let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_934 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_55_947, variance, T (ti)) -> begin
(

let k = (

<<<<<<< HEAD
let _55_955 = (FStar_Syntax_Util.type_u ())
in (match (_55_955) with
| (t, _55_954) -> begin
(let _145_600 = (new_uvar r scope t)
in (Prims.fst _145_600))
=======
let _55_952 = (FStar_Syntax_Util.type_u ())
in (match (_55_952) with
| (t, _55_951) -> begin
(let _146_596 = (new_uvar r scope t)
in (Prims.fst _146_596))
>>>>>>> master
end))
in (

let _55_959 = (new_uvar r scope k)
in (match (_55_959) with
| (gi_xs, gi) -> begin
(

let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_962 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
<<<<<<< HEAD
in (let _145_603 = (let _145_602 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _145_601 -> FStar_TypeChecker_Common.TProb (_145_601)) _145_602))
in (T (gi_xs), _145_603)))
=======
in (let _146_599 = (let _146_598 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _146_597 -> FStar_TypeChecker_Common.TProb (_146_597)) _146_598))
in (T (gi_xs), _146_599)))
>>>>>>> master
end)))
end
| (_55_965, _55_967, C (_55_969)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| (q)::qs -> begin
(

let _55_1047 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _55_987; FStar_Syntax_Syntax.pos = _55_985; FStar_Syntax_Syntax.vars = _55_983})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
<<<<<<< HEAD
(let _145_612 = (let _145_611 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _145_610 -> C (_145_610)) _145_611))
in (_145_612, (prob)::[]))
=======
(let _146_608 = (let _146_607 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _146_606 -> C (_146_606)) _146_607))
in (_146_608, (prob)::[]))
>>>>>>> master
end
| _55_998 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _55_1006; FStar_Syntax_Syntax.pos = _55_1004; FStar_Syntax_Syntax.vars = _55_1002})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
<<<<<<< HEAD
(let _145_615 = (let _145_614 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _145_613 -> C (_145_613)) _145_614))
in (_145_615, (prob)::[]))
=======
(let _146_611 = (let _146_610 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _146_609 -> C (_146_609)) _146_610))
in (_146_611, (prob)::[]))
>>>>>>> master
end
| _55_1017 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1019, _55_1021, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1027; FStar_Syntax_Syntax.pos = _55_1025; FStar_Syntax_Syntax.vars = _55_1023})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (

let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (

<<<<<<< HEAD
let _55_1038 = (let _145_617 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _145_617 FStar_List.unzip))
in (match (_55_1038) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _145_622 = (let _145_621 = (let _145_618 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _145_618 un_T))
in (let _145_620 = (let _145_619 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _145_619 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_621; FStar_Syntax_Syntax.effect_args = _145_620; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _145_622))
=======
let _55_1035 = (let _146_613 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _146_613 FStar_List.unzip))
in (match (_55_1035) with
| (tcs, sub_probs) -> begin
(

let gi_xs = (let _146_618 = (let _146_617 = (let _146_614 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _146_614 un_T))
in (let _146_616 = (let _146_615 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _146_615 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _146_617; FStar_Syntax_Syntax.effect_args = _146_616; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _146_618))
>>>>>>> master
in (C (gi_xs), sub_probs))
end))))
end
| _55_1041 -> begin
(

let _55_1044 = (sub_prob scope args q)
in (match (_55_1044) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_55_1047) with
| (tc, probs) -> begin
(

<<<<<<< HEAD
let _55_1060 = (match (q) with
| (Some (b), _55_1051, _55_1053) -> begin
(let _145_624 = (let _145_623 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_145_623)::args)
in (Some (b), (b)::scope, _145_624))
=======
let _55_1057 = (match (q) with
| (Some (b), _55_1048, _55_1050) -> begin
(let _146_620 = (let _146_619 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_146_619)::args)
in (Some (b), (b)::scope, _146_620))
>>>>>>> master
end
| _55_1056 -> begin
(None, scope, args)
end)
in (match (_55_1060) with
| (bopt, scope, args) -> begin
(

let _55_1064 = (aux scope args qs)
in (match (_55_1064) with
| (sub_probs, tcs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
<<<<<<< HEAD
(let _145_627 = (let _145_626 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_145_626)
in (FStar_Syntax_Util.mk_conj_l _145_627))
end
| Some (b) -> begin
(let _145_631 = (let _145_630 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _145_629 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_145_630)::_145_629))
in (FStar_Syntax_Util.mk_conj_l _145_631))
=======
(let _146_623 = (let _146_622 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_146_622)
in (FStar_Syntax_Util.mk_conj_l _146_623))
end
| Some (b) -> begin
(let _146_627 = (let _146_626 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _146_625 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_146_626)::_146_625))
in (FStar_Syntax_Util.mk_conj_l _146_627))
>>>>>>> master
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))


let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (

let t1 = (FStar_Syntax_Subst.compress t1)
in (

let t2 = (FStar_Syntax_Subst.compress t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(FStar_Syntax_Syntax.fv_eq f g)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(c = d)
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1092), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1097)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1111 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1117 _55_1121 -> (match ((_55_1117, _55_1121)) with
| ((a1, _55_1116), (a2, _55_1120)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))


type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)


type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))


let rigid_rigid : Prims.int = 0


let flex_rigid_eq : Prims.int = 1


let flex_refine_inner : Prims.int = 2


let flex_refine : Prims.int = 3


let flex_rigid : Prims.int = 4


let rigid_flex : Prims.int = 5


let refine_flex : Prims.int = 6


let flex_flex : Prims.int = 7


let compress_tprob = (fun wl p -> (

<<<<<<< HEAD
let _55_1124 = p
in (let _145_653 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_652 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1124.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_653; FStar_TypeChecker_Common.relation = _55_1124.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_652; FStar_TypeChecker_Common.element = _55_1124.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1124.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1124.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1124.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1124.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1124.FStar_TypeChecker_Common.rank}))))
=======
let _55_1121 = p
in (let _146_649 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _146_648 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1121.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _146_649; FStar_TypeChecker_Common.relation = _55_1121.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _146_648; FStar_TypeChecker_Common.element = _55_1121.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1121.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1121.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1121.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1121.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1121.FStar_TypeChecker_Common.rank}))))
>>>>>>> master


let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
<<<<<<< HEAD
(let _145_659 = (compress_tprob wl p)
in (FStar_All.pipe_right _145_659 (fun _145_658 -> FStar_TypeChecker_Common.TProb (_145_658))))
=======
(let _146_655 = (compress_tprob wl p)
in (FStar_All.pipe_right _146_655 (fun _146_654 -> FStar_TypeChecker_Common.TProb (_146_654))))
>>>>>>> master
end
| FStar_TypeChecker_Common.CProb (_55_1131) -> begin
p
end))


let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (

<<<<<<< HEAD
let prob = (let _145_664 = (compress_prob wl pr)
in (FStar_All.pipe_right _145_664 maybe_invert_p))
=======
let prob = (let _146_660 = (compress_prob wl pr)
in (FStar_All.pipe_right _146_660 maybe_invert_p))
>>>>>>> master
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(

let _55_1141 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1141) with
| (lh, _55_1140) -> begin
(

let _55_1145 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1145) with
| (rh, _55_1144) -> begin
(

let _55_1201 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1147), FStar_Syntax_Syntax.Tm_uvar (_55_1150)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1166), _55_1169) -> begin
(

let _55_1173 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1173) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _55_1176 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
<<<<<<< HEAD
in (let _145_666 = (

let _55_1178 = tp
in (let _145_665 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1178.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1178.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1178.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_665; FStar_TypeChecker_Common.element = _55_1178.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1178.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1178.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1178.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1178.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1178.FStar_TypeChecker_Common.rank}))
in (rank, _145_666)))
=======
in (let _146_662 = (

let _55_1175 = tp
in (let _146_661 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1175.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1175.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1175.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _146_661; FStar_TypeChecker_Common.element = _55_1175.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1175.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1175.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1175.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1175.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1175.FStar_TypeChecker_Common.rank}))
in (rank, _146_662)))
>>>>>>> master
end)
end))
end
| (_55_1181, FStar_Syntax_Syntax.Tm_uvar (_55_1183)) -> begin
(

let _55_1188 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1188) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
<<<<<<< HEAD
| _55_1191 -> begin
(let _145_668 = (

let _55_1192 = tp
in (let _145_667 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1192.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_667; FStar_TypeChecker_Common.relation = _55_1192.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1192.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1192.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1192.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1192.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1192.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1192.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1192.FStar_TypeChecker_Common.rank}))
in (refine_flex, _145_668))
=======
| _55_1188 -> begin
(let _146_664 = (

let _55_1189 = tp
in (let _146_663 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1189.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _146_663; FStar_TypeChecker_Common.relation = _55_1189.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1189.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1189.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1189.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1189.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1189.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1189.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1189.FStar_TypeChecker_Common.rank}))
in (refine_flex, _146_664))
>>>>>>> master
end)
end))
end
| (_55_1195, _55_1197) -> begin
(rigid_rigid, tp)
end)
in (match (_55_1201) with
| (rank, tp) -> begin
<<<<<<< HEAD
(let _145_670 = (FStar_All.pipe_right (

let _55_1202 = tp
in {FStar_TypeChecker_Common.pid = _55_1202.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1202.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1202.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1202.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1202.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1202.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1202.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1202.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1202.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _145_669 -> FStar_TypeChecker_Common.TProb (_145_669)))
in (rank, _145_670))
=======
(let _146_666 = (FStar_All.pipe_right (

let _55_1199 = tp
in {FStar_TypeChecker_Common.pid = _55_1199.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1199.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1199.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1199.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1199.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1199.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1199.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1199.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1199.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _146_665 -> FStar_TypeChecker_Common.TProb (_146_665)))
in (rank, _146_666))
>>>>>>> master
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
<<<<<<< HEAD
(let _145_672 = (FStar_All.pipe_right (

let _55_1206 = cp
in {FStar_TypeChecker_Common.pid = _55_1206.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1206.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1206.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1206.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1206.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1206.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1206.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1206.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1206.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _145_671 -> FStar_TypeChecker_Common.CProb (_145_671)))
in (rigid_rigid, _145_672))
=======
(let _146_668 = (FStar_All.pipe_right (

let _55_1203 = cp
in {FStar_TypeChecker_Common.pid = _55_1203.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1203.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1203.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1203.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1203.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1203.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1203.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1203.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1203.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _146_667 -> FStar_TypeChecker_Common.CProb (_146_667)))
in (rigid_rigid, _146_668))
>>>>>>> master
end)))


let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _55_1213 probs -> (match (_55_1213) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| (hd)::tl -> begin
(

let _55_1221 = (rank wl hd)
in (match (_55_1221) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
(Some (hd), (FStar_List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (FStar_List.append out ((m)::tl)), rank)
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end else begin
(aux (min_rank, min, (hd)::out) tl)
end
end
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))


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
| UDeferred (_55_1232) -> begin
_55_1232
end))


let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1235) -> begin
_55_1235
end))


let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1238) -> begin
_55_1238
end))


let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (

let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (

let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (

let _55_1254 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1254) with
| (k, _55_1253) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1258 -> begin
false
end)
end)))))
end
| _55_1260 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (

let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(

let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
| ((u1)::us1, (u2)::us2) -> begin
(match ((solve_universe_eq orig wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end)
end
| _55_1285 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
<<<<<<< HEAD
(let _145_752 = (let _145_751 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_750 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _145_751 _145_750)))
in UFailed (_145_752))
=======
(let _146_748 = (let _146_747 = (FStar_Syntax_Print.univ_to_string u1)
in (let _146_746 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _146_747 _146_746)))
in UFailed (_146_748))
>>>>>>> master
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(

let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| (u)::us -> begin
(match ((solve_universe_eq orig wl u u')) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end)
end))
in (aux wl us))
end
<<<<<<< HEAD
| _55_1303 -> begin
(let _145_759 = (let _145_758 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_757 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _145_758 _145_757 msg)))
in UFailed (_145_759))
=======
| _55_1300 -> begin
(let _146_755 = (let _146_754 = (FStar_Syntax_Print.univ_to_string u1)
in (let _146_753 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _146_754 _146_753 msg)))
in UFailed (_146_755))
>>>>>>> master
end))
in (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: locally nameless")
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
(solve_universe_eq orig wl u1 u2)
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(

let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(

let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
<<<<<<< HEAD
(let _145_762 = (let _145_761 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _145_760 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _145_761 _145_760)))
in (try_umax_components u1 u2 _145_762))
end else begin
(let _145_763 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_145_763))
=======
(let _146_758 = (let _146_757 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _146_756 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _146_757 _146_756)))
in (try_umax_components u1 u2 _146_758))
end else begin
(let _146_759 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_146_759))
>>>>>>> master
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


let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (

<<<<<<< HEAD
let _55_1400 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_809 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _145_809))
=======
let _55_1397 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_805 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _146_805))
>>>>>>> master
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _55_1407 = probs
in {attempting = tl; wl_deferred = _55_1407.wl_deferred; ctr = _55_1407.ctr; defer_ok = _55_1407.defer_ok; smt_ok = _55_1407.smt_ok; tcenv = _55_1407.tcenv})
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
| (None, _55_1422, _55_1424) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1428 -> begin
(

let _55_1437 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1434 -> (match (_55_1434) with
| (c, _55_1431, _55_1433) -> begin
(c < probs.ctr)
end))))
in (match (_55_1437) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
<<<<<<< HEAD
(let _145_812 = (FStar_List.map (fun _55_1443 -> (match (_55_1443) with
| (_55_1440, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_145_812))
end
| _55_1445 -> begin
(let _145_815 = (

let _55_1446 = probs
in (let _145_814 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1453 -> (match (_55_1453) with
| (_55_1449, _55_1451, y) -> begin
y
end))))
in {attempting = _145_814; wl_deferred = rest; ctr = _55_1446.ctr; defer_ok = _55_1446.defer_ok; smt_ok = _55_1446.smt_ok; tcenv = _55_1446.tcenv}))
in (solve env _145_815))
=======
(let _146_808 = (FStar_List.map (fun _55_1440 -> (match (_55_1440) with
| (_55_1437, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_146_808))
end
| _55_1442 -> begin
(let _146_811 = (

let _55_1443 = probs
in (let _146_810 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1450 -> (match (_55_1450) with
| (_55_1446, _55_1448, y) -> begin
y
end))))
in {attempting = _146_810; wl_deferred = rest; ctr = _55_1443.ctr; defer_ok = _55_1443.defer_ok; smt_ok = _55_1443.smt_ok; tcenv = _55_1443.tcenv}))
in (solve env _146_811))
>>>>>>> master
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
<<<<<<< HEAD
(let _145_821 = (solve_prob orig None [] wl)
in (solve env _145_821))
=======
(let _146_817 = (solve_prob orig None [] wl)
in (solve env _146_817))
>>>>>>> master
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (

let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
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
| _55_1488 -> begin
UFailed ("Unequal number of universes")
end))
in (

let t1 = (whnf env t1)
in (

let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1496; FStar_Syntax_Syntax.pos = _55_1494; FStar_Syntax_Syntax.vars = _55_1492}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1508; FStar_Syntax_Syntax.pos = _55_1506; FStar_Syntax_Syntax.vars = _55_1504}, us2)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq f g)
in (

let _55_1517 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1532 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(

<<<<<<< HEAD
let _55_1537 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_837 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _145_837 msg))
=======
let _55_1534 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_833 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _146_833 msg))
>>>>>>> master
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

<<<<<<< HEAD
let _55_1542 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_841 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _145_841))
=======
let _55_1539 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_837 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _146_837))
>>>>>>> master
end else begin
()
end
in (

let _55_1546 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1546) with
| (u, args) -> begin
(

let rec disjoin = (fun t1 t2 -> (

let _55_1552 = (head_matches_delta env () t1 t2)
in (match (_55_1552) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1554) -> begin
None
end
| FullMatch -> begin
(match (ts) with
| None -> begin
Some ((t1, []))
end
| Some (t1, t2) -> begin
Some ((t1, []))
end)
end
| HeadMatch -> begin
(

let _55_1570 = (match (ts) with
| Some (t1, t2) -> begin
<<<<<<< HEAD
(let _145_847 = (FStar_Syntax_Subst.compress t1)
in (let _145_846 = (FStar_Syntax_Subst.compress t2)
in (_145_847, _145_846)))
end
| None -> begin
(let _145_849 = (FStar_Syntax_Subst.compress t1)
in (let _145_848 = (FStar_Syntax_Subst.compress t2)
in (_145_849, _145_848)))
=======
(let _146_843 = (FStar_Syntax_Subst.compress t1)
in (let _146_842 = (FStar_Syntax_Subst.compress t2)
in (_146_843, _146_842)))
end
| None -> begin
(let _146_845 = (FStar_Syntax_Subst.compress t1)
in (let _146_844 = (FStar_Syntax_Subst.compress t2)
in (_146_845, _146_844)))
>>>>>>> master
end)
in (match (_55_1570) with
| (t1, t2) -> begin
(

<<<<<<< HEAD
let eq_prob = (fun t1 t2 -> (let _145_855 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _145_854 -> FStar_TypeChecker_Common.TProb (_145_854)) _145_855)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _145_862 = (let _145_861 = (let _145_858 = (let _145_857 = (let _145_856 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _145_856))
in FStar_Syntax_Syntax.Tm_refine (_145_857))
in (FStar_Syntax_Syntax.mk _145_858 None t1.FStar_Syntax_Syntax.pos))
in (let _145_860 = (let _145_859 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_145_859)::[])
in (_145_861, _145_860)))
in Some (_145_862))
=======
let eq_prob = (fun t1 t2 -> (let _146_851 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _146_850 -> FStar_TypeChecker_Common.TProb (_146_850)) _146_851)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _146_858 = (let _146_857 = (let _146_854 = (let _146_853 = (let _146_852 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _146_852))
in FStar_Syntax_Syntax.Tm_refine (_146_853))
in (FStar_Syntax_Syntax.mk _146_854 None t1.FStar_Syntax_Syntax.pos))
in (let _146_856 = (let _146_855 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_146_855)::[])
in (_146_857, _146_856)))
in Some (_146_858))
end
| (_55_1581, FStar_Syntax_Syntax.Tm_refine (x, _55_1584)) -> begin
(let _146_861 = (let _146_860 = (let _146_859 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_146_859)::[])
in (t1, _146_860))
in Some (_146_861))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1590), _55_1594) -> begin
(let _146_864 = (let _146_863 = (let _146_862 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_146_862)::[])
in (t2, _146_863))
in Some (_146_864))
>>>>>>> master
end
| (_55_1584, FStar_Syntax_Syntax.Tm_refine (x, _55_1587)) -> begin
(let _145_865 = (let _145_864 = (let _145_863 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_145_863)::[])
in (t1, _145_864))
in Some (_145_865))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1593), _55_1597) -> begin
(let _145_868 = (let _145_867 = (let _145_866 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_145_866)::[])
in (t2, _145_867))
in Some (_145_868))
end
| _55_1600 -> begin
(

<<<<<<< HEAD
let _55_1604 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1604) with
| (head1, _55_1603) -> begin
(match ((let _145_869 = (FStar_Syntax_Util.un_uinst head1)
in _145_869.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1610; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (i); FStar_Syntax_Syntax.fv_qual = _55_1606}) -> begin
=======
let _55_1601 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1601) with
| (head1, _55_1600) -> begin
(match ((let _146_865 = (FStar_Syntax_Util.un_uinst head1)
in _146_865.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _55_1607; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_unfoldable (i); FStar_Syntax_Syntax.fv_qual = _55_1603}) -> begin
>>>>>>> master
(

let prev = if (i > 1) then begin
FStar_Syntax_Syntax.Delta_unfoldable ((i - 1))
end else begin
FStar_Syntax_Syntax.Delta_constant
end
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t1)
in (

let t2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (prev))::[]) env t2)
in (disjoin t1 t2))))
end
| _55_1617 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1621) -> begin
(

let _55_1646 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(

<<<<<<< HEAD
let _55_1632 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1632) with
| (u', _55_1631) -> begin
(match ((let _145_871 = (whnf env u')
in _145_871.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1635) -> begin
=======
let _55_1629 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1629) with
| (u', _55_1628) -> begin
(match ((let _146_867 = (whnf env u')
in _146_867.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1632) -> begin
>>>>>>> master
(FStar_Unionfind.equivalent uv uv')
end
| _55_1639 -> begin
false
end)
end))
end
| _55_1641 -> begin
false
end)
end
| _55_1643 -> begin
false
end))))
in (match (_55_1646) with
| (lower_bounds, rest) -> begin
(

let rec make_lower_bound = (fun _55_1650 tps -> (match (_55_1650) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
<<<<<<< HEAD
(match ((let _145_876 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _145_876))) with
=======
(match ((let _146_872 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _146_872))) with
>>>>>>> master
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1663 -> begin
None
end)
end))
<<<<<<< HEAD
in (match ((let _145_878 = (let _145_877 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_145_877, []))
in (make_lower_bound _145_878 lower_bounds))) with
=======
in (match ((let _146_874 = (let _146_873 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_146_873, []))
in (make_lower_bound _146_874 lower_bounds))) with
>>>>>>> master
| None -> begin
(

let _55_1665 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1675 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

<<<<<<< HEAD
let _55_1672 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1672.wl_deferred; ctr = _55_1672.ctr; defer_ok = _55_1672.defer_ok; smt_ok = _55_1672.smt_ok; tcenv = _55_1672.tcenv})
in (let _145_879 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _145_879)))
=======
let _55_1669 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1669.wl_deferred; ctr = _55_1669.ctr; defer_ok = _55_1669.defer_ok; smt_ok = _55_1669.smt_ok; tcenv = _55_1669.tcenv})
in (let _146_875 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _146_875)))
>>>>>>> master
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1677 = wl
in {attempting = sub_probs; wl_deferred = _55_1677.wl_deferred; ctr = _55_1677.ctr; defer_ok = _55_1677.defer_ok; smt_ok = _55_1677.smt_ok; tcenv = _55_1677.tcenv}))) with
| Success (_55_1680) -> begin
(

let wl = (

let _55_1682 = wl
in {attempting = rest; wl_deferred = _55_1682.wl_deferred; ctr = _55_1682.ctr; defer_ok = _55_1682.defer_ok; smt_ok = _55_1682.smt_ok; tcenv = _55_1682.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1688 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1691 -> begin
None
end)))
end))
end))
end
| _55_1693 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

<<<<<<< HEAD
let _55_1697 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_885 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _145_885))
=======
let _55_1694 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_881 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _146_881))
>>>>>>> master
end else begin
()
end
in (

let _55_1701 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1701) with
| (u, args) -> begin
(

let _55_1707 = (0, 1, 2, 3, 4)
in (match (_55_1707) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _55_1716 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1716) with
| (h1, args1) -> begin
(

let _55_1720 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1720) with
| (h2, _55_1719) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
<<<<<<< HEAD
(let _145_897 = (let _145_896 = (let _145_895 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _145_894 -> FStar_TypeChecker_Common.TProb (_145_894)) _145_895))
in (_145_896)::[])
in Some (_145_897))
=======
(let _146_893 = (let _146_892 = (let _146_891 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _146_890 -> FStar_TypeChecker_Common.TProb (_146_890)) _146_891))
in (_146_892)::[])
in Some (_146_893))
>>>>>>> master
end
end else begin
None
end
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
if (FStar_Syntax_Syntax.bv_eq a b) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
<<<<<<< HEAD
(let _145_901 = (let _145_900 = (let _145_899 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _145_898 -> FStar_TypeChecker_Common.TProb (_145_898)) _145_899))
in (_145_900)::[])
in Some (_145_901))
=======
(let _146_897 = (let _146_896 = (let _146_895 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _146_894 -> FStar_TypeChecker_Common.TProb (_146_894)) _146_895))
in (_146_896)::[])
in Some (_146_897))
>>>>>>> master
end
end else begin
None
end
end
| _55_1732 -> begin
None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
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

let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
<<<<<<< HEAD
in (let _145_908 = (let _145_907 = (let _145_906 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _145_906))
in (_145_907, m))
in Some (_145_908))))))
=======
in (let _146_904 = (let _146_903 = (let _146_902 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _146_902))
in (_146_903, m))
in Some (_146_904))))))
>>>>>>> master
end))
end
| (_55_1754, FStar_Syntax_Syntax.Tm_refine (y, _55_1757)) -> begin
(

let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1767), _55_1771) -> begin
(

let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _55_1778 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (

let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1786) -> begin
(

let _55_1811 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

<<<<<<< HEAD
let _55_1797 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1797) with
| (u', _55_1796) -> begin
(match ((let _145_910 = (whnf env u')
in _145_910.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1800) -> begin
=======
let _55_1794 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1794) with
| (u', _55_1793) -> begin
(match ((let _146_906 = (whnf env u')
in _146_906.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1797) -> begin
>>>>>>> master
(FStar_Unionfind.equivalent uv uv')
end
| _55_1804 -> begin
false
end)
end))
end
| _55_1806 -> begin
false
end)
end
| _55_1808 -> begin
false
end))))
in (match (_55_1811) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _55_1815 tps -> (match (_55_1815) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| (FStar_TypeChecker_Common.TProb (hd))::tl -> begin
<<<<<<< HEAD
(match ((let _145_915 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _145_915))) with
=======
(match ((let _146_911 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _146_911))) with
>>>>>>> master
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1828 -> begin
None
end)
end))
<<<<<<< HEAD
in (match ((let _145_917 = (let _145_916 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_145_916, []))
in (make_upper_bound _145_917 upper_bounds))) with
=======
in (match ((let _146_913 = (let _146_912 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_146_912, []))
in (make_upper_bound _146_913 upper_bounds))) with
>>>>>>> master
| None -> begin
(

let _55_1830 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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

let _55_1840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(

let wl' = (

<<<<<<< HEAD
let _55_1837 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1837.wl_deferred; ctr = _55_1837.ctr; defer_ok = _55_1837.defer_ok; smt_ok = _55_1837.smt_ok; tcenv = _55_1837.tcenv})
in (let _145_918 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _145_918)))
=======
let _55_1834 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1834.wl_deferred; ctr = _55_1834.ctr; defer_ok = _55_1834.defer_ok; smt_ok = _55_1834.smt_ok; tcenv = _55_1834.tcenv})
in (let _146_914 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _146_914)))
>>>>>>> master
end else begin
()
end
in (match ((solve_t env eq_prob (

let _55_1842 = wl
in {attempting = sub_probs; wl_deferred = _55_1842.wl_deferred; ctr = _55_1842.ctr; defer_ok = _55_1842.defer_ok; smt_ok = _55_1842.smt_ok; tcenv = _55_1842.tcenv}))) with
| Success (_55_1845) -> begin
(

let wl = (

let _55_1847 = wl
in {attempting = rest; wl_deferred = _55_1847.wl_deferred; ctr = _55_1847.ctr; defer_ok = _55_1847.defer_ok; smt_ok = _55_1847.smt_ok; tcenv = _55_1847.tcenv})
in (

let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (

let _55_1853 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1856 -> begin
None
end)))
end))
end))
end
| _55_1858 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(

let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (

<<<<<<< HEAD
let _55_1875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_946 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _145_946))
=======
let _55_1872 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_942 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _146_942))
>>>>>>> master
end else begin
()
end
in (

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| (((hd1, imp))::xs, ((hd2, imp'))::ys) when (imp = imp') -> begin
(

let hd1 = (

<<<<<<< HEAD
let _55_1889 = hd1
in (let _145_947 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_947}))
=======
let _55_1886 = hd1
in (let _146_943 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1886.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1886.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_943}))
>>>>>>> master
in (

let hd2 = (

<<<<<<< HEAD
let _55_1892 = hd2
in (let _145_948 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1892.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1892.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_948}))
in (

let prob = (let _145_951 = (let _145_950 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _145_950 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _145_949 -> FStar_TypeChecker_Common.TProb (_145_949)) _145_951))
=======
let _55_1889 = hd2
in (let _146_944 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_944}))
in (

let prob = (let _146_947 = (let _146_946 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _146_946 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _146_945 -> FStar_TypeChecker_Common.TProb (_146_945)) _146_947))
>>>>>>> master
in (

let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (

<<<<<<< HEAD
let subst = (let _145_952 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_145_952)
=======
let subst = (let _146_948 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_146_948)
>>>>>>> master
in (

let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(

<<<<<<< HEAD
let phi = (let _145_954 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _145_953 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _145_954 _145_953)))
in (

let _55_1904 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_956 = (FStar_Syntax_Print.term_to_string phi)
in (let _145_955 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _145_956 _145_955)))
=======
let phi = (let _146_950 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _146_949 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _146_950 _146_949)))
in (

let _55_1901 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_952 = (FStar_Syntax_Print.term_to_string phi)
in (let _146_951 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _146_952 _146_951)))
>>>>>>> master
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _55_1908 -> begin
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
<<<<<<< HEAD
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _145_960 = (compress_tprob wl problem)
in (solve_t' env _145_960 wl)))
=======
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _146_956 = (compress_tprob wl problem)
in (solve_t' env _146_956 wl)))
>>>>>>> master
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (

let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (

let _55_1936 = (head_matches_delta env wl t1 t2)
in (match (_55_1936) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_55_1938), _55_1941) -> begin
(

let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_1954 -> begin
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
<<<<<<< HEAD
in (let _145_989 = (let _145_988 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _145_988 t2))
in (FStar_Syntax_Util.mk_forall x _145_989)))
=======
in (let _146_985 = (let _146_984 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _146_984 t2))
in (FStar_Syntax_Util.mk_forall x _146_985)))
>>>>>>> master
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
<<<<<<< HEAD
in (let _145_990 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _145_990)))
=======
in (let _146_986 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _146_986)))
>>>>>>> master
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_1964, Some (t1, t2)) -> begin
(solve_t env (

let _55_1970 = problem
in {FStar_TypeChecker_Common.pid = _55_1970.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_1970.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_1970.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1970.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1970.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1970.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1970.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1970.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_1973, None) -> begin
(

<<<<<<< HEAD
let _55_1976 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_994 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_993 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_992 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_991 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _145_994 _145_993 _145_992 _145_991)))))
=======
let _55_1973 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_990 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_989 = (FStar_Syntax_Print.tag_of_term t1)
in (let _146_988 = (FStar_Syntax_Print.term_to_string t2)
in (let _146_987 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _146_990 _146_989 _146_988 _146_987)))))
>>>>>>> master
end else begin
()
end
in (

let _55_1980 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1980) with
| (head1, args1) -> begin
(

let _55_1983 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1983) with
| (head2, args2) -> begin
(

let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
<<<<<<< HEAD
(let _145_999 = (let _145_998 = (FStar_Syntax_Print.term_to_string head1)
in (let _145_997 = (args_to_string args1)
in (let _145_996 = (FStar_Syntax_Print.term_to_string head2)
in (let _145_995 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _145_998 _145_997 _145_996 _145_995)))))
in (giveup env _145_999 orig))
=======
(let _146_995 = (let _146_994 = (FStar_Syntax_Print.term_to_string head1)
in (let _146_993 = (args_to_string args1)
in (let _146_992 = (FStar_Syntax_Print.term_to_string head2)
in (let _146_991 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _146_994 _146_993 _146_992 _146_991)))))
in (giveup env _146_995 orig))
>>>>>>> master
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
<<<<<<< HEAD
(let _145_1000 = (solve_prob orig None [] wl)
in (solve env _145_1000))
=======
(let _146_996 = (solve_prob orig None [] wl)
in (solve env _146_996))
>>>>>>> master
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(

let _55_1993 = (base_and_refinement env wl t1)
in (match (_55_1993) with
| (base1, refinement1) -> begin
(

let _55_1996 = (base_and_refinement env wl t2)
in (match (_55_1996) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
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

<<<<<<< HEAD
let subprobs = (FStar_List.map2 (fun _55_2009 _55_2013 -> (match ((_55_2009, _55_2013)) with
| ((a, _55_2008), (a', _55_2012)) -> begin
(let _145_1004 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _145_1003 -> FStar_TypeChecker_Common.TProb (_145_1003)) _145_1004))
end)) args1 args2)
in (

let formula = (let _145_1006 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _145_1006))
=======
let subprobs = (FStar_List.map2 (fun _55_2006 _55_2010 -> (match ((_55_2006, _55_2010)) with
| ((a, _55_2005), (a', _55_2009)) -> begin
(let _146_1000 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _146_999 -> FStar_TypeChecker_Common.TProb (_146_999)) _146_1000))
end)) args1 args2)
in (

let formula = (let _146_1002 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _146_1002))
>>>>>>> master
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_2019 -> begin
(

let lhs = (force_refinement (base1, refinement1))
in (

let rhs = (force_refinement (base2, refinement2))
in (solve_t env (

let _55_2022 = problem
in {FStar_TypeChecker_Common.pid = _55_2022.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_2022.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_2022.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2022.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2022.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2022.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2022.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2022.FStar_TypeChecker_Common.rank}) wl)))
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

let _55_2041 = p
in (match (_55_2041) with
| (((u, k), xs, c), ps, (h, _55_2038, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2047 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2047) with
| (sub_probs, gs_xs, formula) -> begin
(

<<<<<<< HEAD
let im = (let _145_1021 = (h gs_xs)
in (let _145_1020 = (let _145_1019 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_1017 -> FStar_Util.Inl (_145_1017)))
in (FStar_All.pipe_right _145_1019 (fun _145_1018 -> Some (_145_1018))))
in (FStar_Syntax_Util.abs xs _145_1021 _145_1020)))
in (

let _55_2049 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1028 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _145_1027 = (FStar_Syntax_Print.comp_to_string c)
in (let _145_1026 = (FStar_Syntax_Print.term_to_string im)
in (let _145_1025 = (FStar_Syntax_Print.tag_of_term im)
in (let _145_1024 = (let _145_1022 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _145_1022 (FStar_String.concat ", ")))
in (let _145_1023 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _145_1028 _145_1027 _145_1026 _145_1025 _145_1024 _145_1023)))))))
=======
let im = (let _146_1017 = (h gs_xs)
in (let _146_1016 = (let _146_1015 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _146_1013 -> FStar_Util.Inl (_146_1013)))
in (FStar_All.pipe_right _146_1015 (fun _146_1014 -> Some (_146_1014))))
in (FStar_Syntax_Util.abs xs _146_1017 _146_1016)))
in (

let _55_2046 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1024 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _146_1023 = (FStar_Syntax_Print.comp_to_string c)
in (let _146_1022 = (FStar_Syntax_Print.term_to_string im)
in (let _146_1021 = (FStar_Syntax_Print.tag_of_term im)
in (let _146_1020 = (let _146_1018 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _146_1018 (FStar_String.concat ", ")))
in (let _146_1019 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _146_1024 _146_1023 _146_1022 _146_1021 _146_1020 _146_1019)))))))
>>>>>>> master
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
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

let _55_2075 = p
in (match (_55_2075) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(

let r = (FStar_TypeChecker_Env.get_range env)
in (

let _55_2080 = (FStar_List.nth ps i)
in (match (_55_2080) with
| (pi, _55_2079) -> begin
(

let _55_2084 = (FStar_List.nth xs i)
in (match (_55_2084) with
| (xi, _55_2083) -> begin
(

let rec gs = (fun k -> (

let _55_2089 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2089) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| ((a, _55_2097))::tl -> begin
(

let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (

let _55_2103 = (new_uvar r xs k_a)
in (match (_55_2103) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (

let subst = (FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
in (

let _55_2109 = (aux subst tl)
in (match (_55_2109) with
| (gi_xs', gi_ps') -> begin
<<<<<<< HEAD
(let _145_1058 = (let _145_1055 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_145_1055)::gi_xs')
in (let _145_1057 = (let _145_1056 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_145_1056)::gi_ps')
in (_145_1058, _145_1057)))
=======
(let _146_1054 = (let _146_1051 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_146_1051)::gi_xs')
in (let _146_1053 = (let _146_1052 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_146_1052)::gi_ps')
in (_146_1054, _146_1053)))
>>>>>>> master
end)))))
end)))
end))
in (aux [] bs))
end)))
<<<<<<< HEAD
in if (let _145_1059 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _145_1059)) then begin
=======
in if (let _146_1055 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _146_1055)) then begin
>>>>>>> master
None
end else begin
(

let _55_2113 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2113) with
| (g_xs, _55_2112) -> begin
(

let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (

<<<<<<< HEAD
let proj = (let _145_1064 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _145_1063 = (let _145_1062 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_1060 -> FStar_Util.Inl (_145_1060)))
in (FStar_All.pipe_right _145_1062 (fun _145_1061 -> Some (_145_1061))))
in (FStar_Syntax_Util.abs xs _145_1064 _145_1063)))
in (

let sub = (let _145_1070 = (let _145_1069 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _145_1068 = (let _145_1067 = (FStar_List.map (fun _55_2121 -> (match (_55_2121) with
| (_55_2117, _55_2119, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _145_1067))
in (mk_problem (p_scope orig) orig _145_1069 (p_rel orig) _145_1068 None "projection")))
in (FStar_All.pipe_left (fun _145_1065 -> FStar_TypeChecker_Common.TProb (_145_1065)) _145_1070))
in (

let _55_2123 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1072 = (FStar_Syntax_Print.term_to_string proj)
in (let _145_1071 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _145_1072 _145_1071)))
=======
let proj = (let _146_1060 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _146_1059 = (let _146_1058 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _146_1056 -> FStar_Util.Inl (_146_1056)))
in (FStar_All.pipe_right _146_1058 (fun _146_1057 -> Some (_146_1057))))
in (FStar_Syntax_Util.abs xs _146_1060 _146_1059)))
in (

let sub = (let _146_1066 = (let _146_1065 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _146_1064 = (let _146_1063 = (FStar_List.map (fun _55_2118 -> (match (_55_2118) with
| (_55_2114, _55_2116, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _146_1063))
in (mk_problem (p_scope orig) orig _146_1065 (p_rel orig) _146_1064 None "projection")))
in (FStar_All.pipe_left (fun _146_1061 -> FStar_TypeChecker_Common.TProb (_146_1061)) _146_1066))
in (

let _55_2120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1068 = (FStar_Syntax_Print.term_to_string proj)
in (let _146_1067 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _146_1068 _146_1067)))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let wl = (let _145_1074 = (let _145_1073 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_145_1073))
in (solve_prob orig _145_1074 ((TERM ((u, proj)))::[]) wl))
in (let _145_1076 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _145_1075 -> Some (_145_1075)) _145_1076)))))))
=======
let wl = (let _146_1070 = (let _146_1069 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_146_1069))
in (solve_prob orig _146_1070 ((TERM ((u, proj)))::[]) wl))
in (let _146_1072 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _146_1071 -> Some (_146_1071)) _146_1072)))))))
>>>>>>> master
end))
end)
end))
end)))
end)))
in (

let solve_t_flex_rigid = (fun orig lhs t2 wl -> (

let _55_2137 = lhs
in (match (_55_2137) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let _55_2142 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2142) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
<<<<<<< HEAD
(let _145_1098 = (let _145_1097 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _145_1097))
in Some (_145_1098))
=======
(let _146_1094 = (let _146_1093 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _146_1093))
in Some (_146_1094))
>>>>>>> master
end else begin
(

let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (

<<<<<<< HEAD
let rec elim = (fun k args -> (match ((let _145_1104 = (let _145_1103 = (FStar_Syntax_Subst.compress k)
in _145_1103.FStar_Syntax_Syntax.n)
in (_145_1104, args))) with
| (_55_2148, []) -> begin
(let _145_1106 = (let _145_1105 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _145_1105))
in Some (_145_1106))
=======
let rec elim = (fun k args -> (match ((let _146_1100 = (let _146_1099 = (FStar_Syntax_Subst.compress k)
in _146_1099.FStar_Syntax_Syntax.n)
in (_146_1100, args))) with
| (_55_2145, []) -> begin
(let _146_1102 = (let _146_1101 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _146_1101))
in Some (_146_1102))
>>>>>>> master
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(

let _55_2165 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2165) with
| (uv, uv_args) -> begin
<<<<<<< HEAD
(match ((let _145_1107 = (FStar_Syntax_Subst.compress uv)
in _145_1107.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2168) -> begin
=======
(match ((let _146_1103 = (FStar_Syntax_Subst.compress uv)
in _146_1103.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2165) -> begin
>>>>>>> master
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(

<<<<<<< HEAD
let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2174 -> (let _145_1113 = (let _145_1112 = (let _145_1111 = (let _145_1110 = (let _145_1109 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1109 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _145_1110))
in (Prims.fst _145_1111))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _145_1112))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _145_1113)))))
in (

let c = (let _145_1117 = (let _145_1116 = (let _145_1115 = (let _145_1114 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1114 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _145_1115))
in (Prims.fst _145_1116))
in (FStar_Syntax_Syntax.mk_Total _145_1117))
=======
let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2171 -> (let _146_1109 = (let _146_1108 = (let _146_1107 = (let _146_1106 = (let _146_1105 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1105 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _146_1106))
in (Prims.fst _146_1107))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _146_1108))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _146_1109)))))
in (

let c = (let _146_1113 = (let _146_1112 = (let _146_1111 = (let _146_1110 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1110 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _146_1111))
in (Prims.fst _146_1112))
in (FStar_Syntax_Syntax.mk_Total _146_1113))
>>>>>>> master
in (

let k' = (FStar_Syntax_Util.arrow xs c)
in (

<<<<<<< HEAD
let uv_sol = (let _145_1123 = (let _145_1122 = (let _145_1121 = (let _145_1120 = (let _145_1119 = (let _145_1118 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _145_1118 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _145_1119))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _145_1120))
in FStar_Util.Inl (_145_1121))
in Some (_145_1122))
in (FStar_Syntax_Util.abs scope k' _145_1123))
=======
let uv_sol = (let _146_1119 = (let _146_1118 = (let _146_1117 = (let _146_1116 = (let _146_1115 = (let _146_1114 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _146_1114 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _146_1115))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _146_1116))
in FStar_Util.Inl (_146_1117))
in Some (_146_1118))
in (FStar_Syntax_Util.abs scope k' _146_1119))
>>>>>>> master
in (

let _55_2180 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some ((xs, c)))))))
end)
end
| _55_2183 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2189) -> begin
(

let n_args = (FStar_List.length args)
in (

let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
<<<<<<< HEAD
(let _145_1125 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _145_1125 (fun _145_1124 -> Some (_145_1124))))
=======
(let _146_1121 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _146_1121 (fun _146_1120 -> Some (_146_1120))))
>>>>>>> master
end else begin
if (n_xs < n_args) then begin
(

let _55_2195 = (FStar_Util.first_N n_xs args)
in (match (_55_2195) with
| (args, rest) -> begin
(

let _55_2198 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2198) with
| (xs, c) -> begin
<<<<<<< HEAD
(let _145_1127 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _145_1127 (fun _55_2201 -> (match (_55_2201) with
=======
(let _146_1123 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _146_1123 (fun _55_2198 -> (match (_55_2198) with
>>>>>>> master
| (xs', c) -> begin
Some (((FStar_List.append xs xs'), c))
end))))
end))
end))
end else begin
(

let _55_2204 = (FStar_Util.first_N n_args xs)
in (match (_55_2204) with
| (xs, rest) -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) None k.FStar_Syntax_Syntax.pos)
<<<<<<< HEAD
in (let _145_1130 = (let _145_1128 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _145_1128))
in (FStar_All.pipe_right _145_1130 (fun _145_1129 -> Some (_145_1129)))))
=======
in (let _146_1126 = (let _146_1124 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _146_1124))
in (FStar_All.pipe_right _146_1126 (fun _146_1125 -> Some (_146_1125)))))
>>>>>>> master
end))
end
end))
end
<<<<<<< HEAD
| _55_2207 -> begin
(let _145_1134 = (let _145_1133 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _145_1132 = (FStar_Syntax_Print.term_to_string k)
in (let _145_1131 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _145_1133 _145_1132 _145_1131))))
in (FStar_All.failwith _145_1134))
end))
in (let _145_1172 = (elim k_uv ps)
in (FStar_Util.bind_opt _145_1172 (fun _55_2210 -> (match (_55_2210) with
| (xs, c) -> begin
(let _145_1171 = (let _145_1170 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _145_1170))
in Some (_145_1171))
=======
| _55_2204 -> begin
(let _146_1130 = (let _146_1129 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _146_1128 = (FStar_Syntax_Print.term_to_string k)
in (let _146_1127 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _146_1129 _146_1128 _146_1127))))
in (FStar_All.failwith _146_1130))
end))
in (let _146_1168 = (elim k_uv ps)
in (FStar_Util.bind_opt _146_1168 (fun _55_2207 -> (match (_55_2207) with
| (xs, c) -> begin
(let _146_1167 = (let _146_1166 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _146_1166))
in Some (_146_1167))
>>>>>>> master
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
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_55_2218) -> begin
(

let _55_2220 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(

let _55_2228 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (

let check_head = (fun fvs1 t2 -> (

let _55_2238 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2238) with
| (hd, _55_2237) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2249 -> begin
(

let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(

<<<<<<< HEAD
let _55_2251 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1183 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _145_1183))
=======
let _55_2248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1179 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _146_1179))
>>>>>>> master
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

<<<<<<< HEAD
let fvs_hd = (let _145_1187 = (let _145_1186 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1186 Prims.fst))
in (FStar_All.pipe_right _145_1187 FStar_Syntax_Free.names))
=======
let fvs_hd = (let _146_1183 = (let _146_1182 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _146_1182 Prims.fst))
in (FStar_All.pipe_right _146_1183 FStar_Syntax_Free.names))
>>>>>>> master
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
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

let _55_2264 = (occurs_check env wl (uv, k_uv) t2)
in (match (_55_2264) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
<<<<<<< HEAD
(let _145_1189 = (let _145_1188 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _145_1188))
in (giveup_or_defer orig _145_1189))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _145_1190 = (subterms args_lhs)
in (imitate' orig env wl _145_1190))
end else begin
(

let _55_2265 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1193 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1192 = (names_to_string fvs1)
in (let _145_1191 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _145_1193 _145_1192 _145_1191))))
=======
(let _146_1185 = (let _146_1184 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _146_1184))
in (giveup_or_defer orig _146_1185))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _146_1186 = (subterms args_lhs)
in (imitate' orig env wl _146_1186))
end else begin
(

let _55_2262 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1189 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_1188 = (names_to_string fvs1)
in (let _146_1187 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _146_1189 _146_1188 _146_1187))))
>>>>>>> master
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
<<<<<<< HEAD
| _55_2269 -> begin
(let _145_1194 = (sn_binders env vars)
in (u_abs k_uv _145_1194 t2))
=======
| _55_2266 -> begin
(let _146_1190 = (sn_binders env vars)
in (u_abs k_uv _146_1190 t2))
>>>>>>> master
end)
in (

let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(

<<<<<<< HEAD
let _55_2272 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1197 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1196 = (names_to_string fvs1)
in (let _145_1195 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _145_1197 _145_1196 _145_1195))))
end else begin
()
end
in (let _145_1198 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1198 (- (1)))))
=======
let _55_2269 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1193 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_1192 = (names_to_string fvs1)
in (let _146_1191 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _146_1193 _146_1192 _146_1191))))
end else begin
()
end
in (let _146_1194 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _146_1194 (- (1)))))
>>>>>>> master
end else begin
(giveup env "free-variable check failed on a non-redex" orig)
end
end
end
end
end))))))
end
| None -> begin
if wl.defer_ok then begin
(solve env (defer "not a pattern" orig wl))
end else begin
<<<<<<< HEAD
if (let _145_1199 = (FStar_Syntax_Free.names t1)
in (check_head _145_1199 t2)) then begin
=======
if (let _146_1195 = (FStar_Syntax_Free.names t1)
in (check_head _146_1195 t2)) then begin
>>>>>>> master
(

let im_ok = (imitate_ok t2)
in (

<<<<<<< HEAD
let _55_2276 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1200 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _145_1200 (if (im_ok < 0) then begin
=======
let _55_2273 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1196 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _146_1196 (if (im_ok < 0) then begin
>>>>>>> master
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
<<<<<<< HEAD
in (let _145_1201 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1201 im_ok))))
=======
in (let _146_1197 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _146_1197 im_ok))))
>>>>>>> master
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

let force_quasi_pattern = (fun xs_opt _55_2288 -> (match (_55_2288) with
| (t, u, k, args) -> begin
(

let _55_2292 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2292) with
| (all_formals, _55_2291) -> begin
(

let _55_2293 = ()
in (

let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(

let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2306 -> (match (_55_2306) with
| (x, imp) -> begin
<<<<<<< HEAD
(let _145_1223 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_1223, imp))
=======
(let _146_1219 = (FStar_Syntax_Syntax.bv_to_name x)
in (_146_1219, imp))
>>>>>>> master
end))))
in (

let pattern_vars = (FStar_List.rev pattern_vars)
in (

let kk = (

<<<<<<< HEAD
let _55_2312 = (FStar_Syntax_Util.type_u ())
in (match (_55_2312) with
| (t, _55_2311) -> begin
(let _145_1224 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _145_1224))
=======
let _55_2309 = (FStar_Syntax_Util.type_u ())
in (match (_55_2309) with
| (t, _55_2308) -> begin
(let _146_1220 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _146_1220))
>>>>>>> master
end))
in (

let _55_2316 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2316) with
| (t', tm_u1) -> begin
(

let _55_2323 = (destruct_flex_t t')
in (match (_55_2323) with
| (_55_2318, u1, k1, _55_2322) -> begin
(

<<<<<<< HEAD
let sol = (let _145_1226 = (let _145_1225 = (u_abs k all_formals t')
in ((u, k), _145_1225))
in TERM (_145_1226))
=======
let sol = (let _146_1222 = (let _146_1221 = (u_abs k all_formals t')
in ((u, k), _146_1221))
in TERM (_146_1222))
>>>>>>> master
in (

let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in (sol, (t_app, u1, k1, pat_args))))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2342 -> (match (_55_2342) with
| (x, _55_2341) -> begin
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
<<<<<<< HEAD
(let _145_1228 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _145_1228 formals tl))
=======
(let _146_1224 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _146_1224 formals tl))
>>>>>>> master
end)
end)
end)
end
| _55_2346 -> begin
(FStar_All.failwith "Impossible")
end))
<<<<<<< HEAD
in (let _145_1229 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _145_1229 all_formals args))))
=======
in (let _146_1225 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _146_1225 all_formals args))))
>>>>>>> master
end))
end))
in (

let solve_both_pats = (fun wl _55_2353 _55_2358 r -> (match ((_55_2353, _55_2358)) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
<<<<<<< HEAD
(let _145_1238 = (solve_prob orig None [] wl)
in (solve env _145_1238))
=======
(let _146_1234 = (solve_prob orig None [] wl)
in (solve env _146_1234))
>>>>>>> master
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

<<<<<<< HEAD
let _55_2363 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1243 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _145_1242 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _145_1241 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _145_1240 = (FStar_Syntax_Print.term_to_string k1)
in (let _145_1239 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _145_1243 _145_1242 _145_1241 _145_1240 _145_1239))))))
=======
let _55_2360 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1239 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _146_1238 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _146_1237 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _146_1236 = (FStar_Syntax_Print.term_to_string k1)
in (let _146_1235 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _146_1239 _146_1238 _146_1237 _146_1236 _146_1235))))))
>>>>>>> master
end else begin
()
end
in (

let _55_2376 = (

let _55_2368 = (FStar_Syntax_Util.type_u ())
in (match (_55_2368) with
| (t, _55_2367) -> begin
(

<<<<<<< HEAD
let _55_2372 = (new_uvar r zs t)
in (match (_55_2372) with
| (k, _55_2371) -> begin
(let _145_1249 = (let _145_1244 = (new_uvar r zs k)
in (FStar_All.pipe_left Prims.fst _145_1244))
in (let _145_1248 = (let _145_1245 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow xs _145_1245))
in (let _145_1247 = (let _145_1246 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow ys _145_1246))
in (_145_1249, _145_1248, _145_1247))))
=======
let _55_2369 = (new_uvar r zs t)
in (match (_55_2369) with
| (k, _55_2368) -> begin
(let _146_1245 = (let _146_1240 = (new_uvar r zs k)
in (FStar_All.pipe_left Prims.fst _146_1240))
in (let _146_1244 = (let _146_1241 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow xs _146_1241))
in (let _146_1243 = (let _146_1242 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow ys _146_1242))
in (_146_1245, _146_1244, _146_1243))))
>>>>>>> master
end))
end))
in (match (_55_2376) with
| (u_zs, knew1, knew2) -> begin
(

let sub1 = (u_abs knew1 xs u_zs)
in (

let _55_2380 = (occurs_check env wl (u1, k1) sub1)
in (match (_55_2380) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(

let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(

let sub2 = (u_abs knew2 ys u_zs)
in (

let _55_2386 = (occurs_check env wl (u2, k2) sub2)
in (match (_55_2386) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(

let sol2 = TERM (((u2, k2), sub2))
in (

let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end))))))
end
end))
in (

let solve_one_pat = (fun _55_2394 _55_2399 -> (match ((_55_2394, _55_2399)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

<<<<<<< HEAD
let _55_2400 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1255 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1254 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _145_1255 _145_1254)))
=======
let _55_2397 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1251 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_1250 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _146_1251 _146_1250)))
>>>>>>> master
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

<<<<<<< HEAD
let sub_probs = (FStar_List.map2 (fun _55_2405 _55_2409 -> (match ((_55_2405, _55_2409)) with
| ((a, _55_2404), (t2, _55_2408)) -> begin
(let _145_1260 = (let _145_1258 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _145_1258 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _145_1260 (fun _145_1259 -> FStar_TypeChecker_Common.TProb (_145_1259))))
end)) xs args2)
in (

let guard = (let _145_1262 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1262))
=======
let sub_probs = (FStar_List.map2 (fun _55_2402 _55_2406 -> (match ((_55_2402, _55_2406)) with
| ((a, _55_2401), (t2, _55_2405)) -> begin
(let _146_1256 = (let _146_1254 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _146_1254 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _146_1256 (fun _146_1255 -> FStar_TypeChecker_Common.TProb (_146_1255))))
end)) xs args2)
in (

let guard = (let _146_1258 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _146_1258))
>>>>>>> master
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Syntax_Free.names t2)
in (

let _55_2419 = (occurs_check env wl (u1, k1) t2)
in (match (_55_2419) with
| (occurs_ok, _55_2418) -> begin
(

let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(

<<<<<<< HEAD
let sol = (let _145_1264 = (let _145_1263 = (u_abs k1 xs t2)
in ((u1, k1), _145_1263))
in TERM (_145_1264))
=======
let sol = (let _146_1260 = (let _146_1259 = (u_abs k1 xs t2)
in ((u1, k1), _146_1259))
in TERM (_146_1260))
>>>>>>> master
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _55_2430 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_55_2430) with
| (sol, (_55_2425, u2, k2, ys)) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

<<<<<<< HEAD
let _55_2432 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1265 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _145_1265))
=======
let _55_2429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _146_1261 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _146_1261))
>>>>>>> master
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2437 -> begin
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

let _55_2442 = lhs
in (match (_55_2442) with
| (t1, u1, k1, args1) -> begin
(

let _55_2447 = rhs
in (match (_55_2447) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Syntax_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl (u1, k1, xs, args1) (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _55_2465 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _55_2469 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_55_2469) with
| (sol, _55_2468) -> begin
(

let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (

<<<<<<< HEAD
let _55_2471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1266 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _145_1266))
=======
let _55_2468 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _146_1262 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _146_1262))
>>>>>>> master
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2476 -> begin
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
<<<<<<< HEAD
(let _145_1267 = (solve_prob orig None [] wl)
in (solve env _145_1267))
=======
(let _146_1263 = (solve_prob orig None [] wl)
in (solve env _146_1263))
>>>>>>> master
end else begin
(

let t1 = problem.FStar_TypeChecker_Common.lhs
in (

let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
<<<<<<< HEAD
(let _145_1268 = (solve_prob orig None [] wl)
in (solve env _145_1268))
end else begin
(

let _55_2480 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1269 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _145_1269))
=======
(let _146_1264 = (solve_prob orig None [] wl)
in (solve env _146_1264))
end else begin
(

let _55_2477 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1265 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _146_1265))
>>>>>>> master
end else begin
()
end
in (

let r = (FStar_TypeChecker_Env.get_range env)
in (

let match_num_binders = (fun _55_2485 _55_2488 -> (match ((_55_2485, _55_2488)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _55_2495 = (FStar_Util.first_N n bs)
in (match (_55_2495) with
| (bs, rest) -> begin
<<<<<<< HEAD
(let _145_1299 = (mk_cod rest)
in (bs, _145_1299))
=======
(let _146_1295 = (mk_cod rest)
in (bs, _146_1295))
>>>>>>> master
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
<<<<<<< HEAD
(let _145_1303 = (let _145_1300 = (mk_cod1 [])
in (bs1, _145_1300))
in (let _145_1302 = (let _145_1301 = (mk_cod2 [])
in (bs2, _145_1301))
in (_145_1303, _145_1302)))
end else begin
if (l1 > l2) then begin
(let _145_1306 = (curry l2 bs1 mk_cod1)
in (let _145_1305 = (let _145_1304 = (mk_cod2 [])
in (bs2, _145_1304))
in (_145_1306, _145_1305)))
end else begin
(let _145_1309 = (let _145_1307 = (mk_cod1 [])
in (bs1, _145_1307))
in (let _145_1308 = (curry l1 bs2 mk_cod2)
in (_145_1309, _145_1308)))
=======
(let _146_1299 = (let _146_1296 = (mk_cod1 [])
in (bs1, _146_1296))
in (let _146_1298 = (let _146_1297 = (mk_cod2 [])
in (bs2, _146_1297))
in (_146_1299, _146_1298)))
end else begin
if (l1 > l2) then begin
(let _146_1302 = (curry l2 bs1 mk_cod1)
in (let _146_1301 = (let _146_1300 = (mk_cod2 [])
in (bs2, _146_1300))
in (_146_1302, _146_1301)))
end else begin
(let _146_1305 = (let _146_1303 = (mk_cod1 [])
in (bs1, _146_1303))
in (let _146_1304 = (curry l1 bs2 mk_cod2)
in (_146_1305, _146_1304)))
>>>>>>> master
end
end)))
end))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
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
<<<<<<< HEAD
(let _145_1314 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _145_1314))
=======
(let _146_1310 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _146_1310))
>>>>>>> master
end))
in (

let _55_2538 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_55_2538) with
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
<<<<<<< HEAD
in (let _145_1321 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _145_1320 -> FStar_TypeChecker_Common.CProb (_145_1320)) _145_1321)))))))
=======
in (let _146_1317 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _146_1316 -> FStar_TypeChecker_Common.CProb (_146_1316)) _146_1317)))))))
>>>>>>> master
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(

let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, l))) None t.FStar_Syntax_Syntax.pos)
end))
in (

let _55_2568 = (match_num_binders (bs1, (mk_t tbody1 lopt1)) (bs2, (mk_t tbody2 lopt2)))
in (match (_55_2568) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
<<<<<<< HEAD
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _145_1336 = (let _145_1335 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _145_1334 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _145_1335 problem.FStar_TypeChecker_Common.relation _145_1334 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _145_1333 -> FStar_TypeChecker_Common.TProb (_145_1333)) _145_1336))))
=======
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _146_1332 = (let _146_1331 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _146_1330 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _146_1331 problem.FStar_TypeChecker_Common.relation _146_1330 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _146_1329 -> FStar_TypeChecker_Common.TProb (_146_1329)) _146_1332))))
>>>>>>> master
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2573), FStar_Syntax_Syntax.Tm_refine (_55_2576)) -> begin
(

let _55_2581 = (as_refinement env wl t1)
in (match (_55_2581) with
| (x1, phi1) -> begin
(

let _55_2584 = (as_refinement env wl t2)
in (match (_55_2584) with
| (x2, phi2) -> begin
(

<<<<<<< HEAD
let base_prob = (let _145_1338 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _145_1337 -> FStar_TypeChecker_Common.TProb (_145_1337)) _145_1338))
=======
let base_prob = (let _146_1334 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _146_1333 -> FStar_TypeChecker_Common.TProb (_146_1333)) _146_1334))
>>>>>>> master
in (

let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (

let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (

let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (

let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (

let env = (FStar_TypeChecker_Env.push_bv env x1)
in (

<<<<<<< HEAD
let mk_imp = (fun imp phi1 phi2 -> (let _145_1355 = (imp phi1 phi2)
in (FStar_All.pipe_right _145_1355 (guard_on_element problem x1))))
=======
let mk_imp = (fun imp phi1 phi2 -> (let _146_1351 = (imp phi1 phi2)
in (FStar_All.pipe_right _146_1351 (guard_on_element problem x1))))
>>>>>>> master
in (

let fallback = (fun _55_2596 -> (match (()) with
| () -> begin
(

let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (

<<<<<<< HEAD
let guard = (let _145_1358 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1358 impl))
=======
let guard = (let _146_1354 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _146_1354 impl))
>>>>>>> master
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

<<<<<<< HEAD
let ref_prob = (let _145_1362 = (let _145_1361 = (let _145_1360 = (FStar_Syntax_Syntax.mk_binder x1)
in (_145_1360)::(p_scope orig))
in (mk_problem _145_1361 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _145_1359 -> FStar_TypeChecker_Common.TProb (_145_1359)) _145_1362))
=======
let ref_prob = (let _146_1358 = (let _146_1357 = (let _146_1356 = (FStar_Syntax_Syntax.mk_binder x1)
in (_146_1356)::(p_scope orig))
in (mk_problem _146_1357 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _146_1355 -> FStar_TypeChecker_Common.TProb (_146_1355)) _146_1358))
>>>>>>> master
in (match ((solve env (

let _55_2601 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2601.ctr; defer_ok = false; smt_ok = _55_2601.smt_ok; tcenv = _55_2601.tcenv}))) with
| Failed (_55_2604) -> begin
(fallback ())
end
| Success (_55_2607) -> begin
(

<<<<<<< HEAD
let guard = (let _145_1365 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _145_1364 = (let _145_1363 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _145_1363 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _145_1365 _145_1364)))
=======
let guard = (let _146_1361 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _146_1360 = (let _146_1359 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _146_1359 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _146_1361 _146_1360)))
>>>>>>> master
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _55_2611 = wl
in {attempting = _55_2611.attempting; wl_deferred = _55_2611.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_2611.defer_ok; smt_ok = _55_2611.smt_ok; tcenv = _55_2611.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
<<<<<<< HEAD
(let _145_1367 = (destruct_flex_t t1)
in (let _145_1366 = (destruct_flex_t t2)
in (flex_flex orig _145_1367 _145_1366)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _145_1368 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _145_1368 t2 wl))
=======
(let _146_1363 = (destruct_flex_t t1)
in (let _146_1362 = (destruct_flex_t t2)
in (flex_flex orig _146_1363 _146_1362)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _146_1364 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _146_1364 t2 wl))
>>>>>>> master
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.FStar_TypeChecker_Common.relation
<<<<<<< HEAD
in if (let _145_1369 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _145_1369)) then begin
(let _145_1372 = (FStar_All.pipe_left (fun _145_1370 -> FStar_TypeChecker_Common.TProb (_145_1370)) (

let _55_2756 = problem
in {FStar_TypeChecker_Common.pid = _55_2756.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2756.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2756.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2756.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2756.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2756.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2756.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2756.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2756.FStar_TypeChecker_Common.rank}))
in (let _145_1371 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1372 _145_1371 t2 wl)))
=======
in if (let _146_1365 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _146_1365)) then begin
(let _146_1368 = (FStar_All.pipe_left (fun _146_1366 -> FStar_TypeChecker_Common.TProb (_146_1366)) (

let _55_2753 = problem
in {FStar_TypeChecker_Common.pid = _55_2753.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2753.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2753.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2753.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2753.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2753.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2753.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2753.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2753.FStar_TypeChecker_Common.rank}))
in (let _146_1367 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _146_1368 _146_1367 t2 wl)))
>>>>>>> master
end else begin
(

let _55_2760 = (base_and_refinement env wl t2)
in (match (_55_2760) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
<<<<<<< HEAD
(let _145_1375 = (FStar_All.pipe_left (fun _145_1373 -> FStar_TypeChecker_Common.TProb (_145_1373)) (

let _55_2762 = problem
in {FStar_TypeChecker_Common.pid = _55_2762.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2762.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2762.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2762.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2762.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2762.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2762.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2762.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2762.FStar_TypeChecker_Common.rank}))
in (let _145_1374 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1375 _145_1374 t_base wl)))
=======
(let _146_1371 = (FStar_All.pipe_left (fun _146_1369 -> FStar_TypeChecker_Common.TProb (_146_1369)) (

let _55_2759 = problem
in {FStar_TypeChecker_Common.pid = _55_2759.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2759.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2759.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2759.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2759.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2759.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2759.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2759.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2759.FStar_TypeChecker_Common.rank}))
in (let _146_1370 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _146_1371 _146_1370 t_base wl)))
>>>>>>> master
end
| Some (y, phi) -> begin
(

let y' = (

let _55_2768 = y
in {FStar_Syntax_Syntax.ppname = _55_2768.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2768.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (

let impl = (guard_on_element problem y' phi)
in (

<<<<<<< HEAD
let base_prob = (let _145_1377 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _145_1376 -> FStar_TypeChecker_Common.TProb (_145_1376)) _145_1377))
in (

let guard = (let _145_1378 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1378 impl))
=======
let base_prob = (let _146_1373 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _146_1372 -> FStar_TypeChecker_Common.TProb (_146_1372)) _146_1373))
in (

let guard = (let _146_1374 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _146_1374 impl))
>>>>>>> master
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

let _55_2801 = (base_and_refinement env wl t1)
in (match (_55_2801) with
| (t_base, _55_2800) -> begin
(solve_t env (

let _55_2802 = problem
in {FStar_TypeChecker_Common.pid = _55_2802.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2802.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2802.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2802.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2802.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2802.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2802.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2802.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2805), _55_2808) -> begin
(

<<<<<<< HEAD
let t2 = (let _145_1379 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _145_1379))
=======
let t2 = (let _146_1375 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _146_1375))
>>>>>>> master
in (solve_t env (

let _55_2811 = problem
in {FStar_TypeChecker_Common.pid = _55_2811.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2811.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2811.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2811.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2811.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2811.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2811.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2811.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2811.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_2814, FStar_Syntax_Syntax.Tm_refine (_55_2816)) -> begin
(

<<<<<<< HEAD
let t1 = (let _145_1380 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _145_1380))
=======
let t1 = (let _146_1376 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _146_1376))
>>>>>>> master
in (solve_t env (

let _55_2820 = problem
in {FStar_TypeChecker_Common.pid = _55_2820.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2820.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2820.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2820.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2820.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2820.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2820.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2820.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2820.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(

let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2837) -> begin
t
end
| _55_2840 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
<<<<<<< HEAD
in (let _145_1385 = (

let _55_2841 = problem
in (let _145_1384 = (maybe_eta t1)
in (let _145_1383 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2841.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1384; FStar_TypeChecker_Common.relation = _55_2841.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1383; FStar_TypeChecker_Common.element = _55_2841.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2841.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2841.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2841.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2841.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2841.FStar_TypeChecker_Common.rank})))
in (solve_t env _145_1385 wl)))
=======
in (let _146_1381 = (

let _55_2838 = problem
in (let _146_1380 = (maybe_eta t1)
in (let _146_1379 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2838.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _146_1380; FStar_TypeChecker_Common.relation = _55_2838.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _146_1379; FStar_TypeChecker_Common.element = _55_2838.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2838.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2838.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2838.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2838.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2838.FStar_TypeChecker_Common.rank})))
in (solve_t env _146_1381 wl)))
>>>>>>> master
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(

<<<<<<< HEAD
let head1 = (let _145_1386 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _145_1386 Prims.fst))
in (

let head2 = (let _145_1387 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1387 Prims.fst))
=======
let head1 = (let _146_1382 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _146_1382 Prims.fst))
in (

let head2 = (let _146_1383 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _146_1383 Prims.fst))
>>>>>>> master
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
<<<<<<< HEAD
(let _145_1389 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _145_1388 -> Some (_145_1388)) _145_1389))
end
in (let _145_1390 = (solve_prob orig guard [] wl)
in (solve env _145_1390)))
=======
(let _146_1385 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _146_1384 -> Some (_146_1384)) _146_1385))
end
in (let _146_1386 = (solve_prob orig guard [] wl)
in (solve env _146_1386)))
>>>>>>> master
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_2922, _55_2924), _55_2928) -> begin
(solve_t' env (

let _55_2930 = problem
in {FStar_TypeChecker_Common.pid = _55_2930.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2930.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2930.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2930.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2930.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2930.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2930.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2930.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2930.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2933, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_2936, _55_2938)) -> begin
(solve_t' env (

let _55_2942 = problem
in {FStar_TypeChecker_Common.pid = _55_2942.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2942.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2942.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2942.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2942.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2942.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2942.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2942.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2942.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
<<<<<<< HEAD
(let _145_1393 = (let _145_1392 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_1391 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _145_1392 _145_1391)))
in (FStar_All.failwith _145_1393))
=======
(let _146_1389 = (let _146_1388 = (FStar_Syntax_Print.tag_of_term t1)
in (let _146_1387 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _146_1388 _146_1387)))
in (FStar_All.failwith _146_1389))
>>>>>>> master
end
| _55_2981 -> begin
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

let _55_2998 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

<<<<<<< HEAD
let sub_probs = (FStar_List.map2 (fun _55_3003 _55_3007 -> (match ((_55_3003, _55_3007)) with
| ((a1, _55_3002), (a2, _55_3006)) -> begin
(let _145_1408 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _145_1407 -> FStar_TypeChecker_Common.TProb (_145_1407)) _145_1408))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _145_1410 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1410))
=======
let sub_probs = (FStar_List.map2 (fun _55_3000 _55_3004 -> (match ((_55_3000, _55_3004)) with
| ((a1, _55_2999), (a2, _55_3003)) -> begin
(let _146_1404 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _146_1403 -> FStar_TypeChecker_Common.TProb (_146_1403)) _146_1404))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (

let guard = (let _146_1406 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _146_1406))
>>>>>>> master
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (

let solve_sub = (fun c1 edge c2 -> (

let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| ((wp1, _55_3019))::[] -> begin
wp1
end
<<<<<<< HEAD
| _55_3023 -> begin
(let _145_1418 = (let _145_1417 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _145_1417))
in (FStar_All.failwith _145_1418))
end)
in (

let c1 = (let _145_1421 = (let _145_1420 = (let _145_1419 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _145_1419))
in (_145_1420)::[])
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _145_1421; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
=======
| _55_3020 -> begin
(let _146_1414 = (let _146_1413 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _146_1413))
in (FStar_All.failwith _146_1414))
end)
in (

let c1 = (let _146_1417 = (let _146_1416 = (let _146_1415 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _146_1415))
in (_146_1416)::[])
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _146_1417; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
>>>>>>> master
in (solve_eq c1 c2)))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3031 -> begin
false
end))))
in (

let _55_3052 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| (((wp1, _55_3037))::_55_3034, ((wp2, _55_3044))::_55_3041) -> begin
(wp1, wp2)
end
<<<<<<< HEAD
| _55_3049 -> begin
(let _145_1425 = (let _145_1424 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1423 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _145_1424 _145_1423)))
in (FStar_All.failwith _145_1425))
=======
| _55_3046 -> begin
(let _146_1421 = (let _146_1420 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _146_1419 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _146_1420 _146_1419)))
in (FStar_All.failwith _146_1421))
>>>>>>> master
end)
in (match (_55_3052) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
<<<<<<< HEAD
(let _145_1426 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _145_1426 wl))
=======
(let _146_1422 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _146_1422 wl))
>>>>>>> master
end else begin
(

let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _55_3054 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
<<<<<<< HEAD
in (let _145_1436 = (let _145_1435 = (let _145_1434 = (let _145_1428 = (let _145_1427 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_145_1427)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1428 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _145_1433 = (let _145_1432 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _145_1431 = (let _145_1430 = (let _145_1429 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1429))
in (_145_1430)::[])
in (_145_1432)::_145_1431))
in (_145_1434, _145_1433)))
in FStar_Syntax_Syntax.Tm_app (_145_1435))
in (FStar_Syntax_Syntax.mk _145_1436 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(

let wp2_imp_wp1 = (let _145_1452 = (let _145_1451 = (let _145_1450 = (let _145_1438 = (let _145_1437 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_145_1437)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1438 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _145_1449 = (let _145_1448 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _145_1447 = (let _145_1446 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _145_1445 = (let _145_1444 = (let _145_1440 = (let _145_1439 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _145_1439 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1440))
in (let _145_1443 = (let _145_1442 = (let _145_1441 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1441))
in (_145_1442)::[])
in (_145_1444)::_145_1443))
in (_145_1446)::_145_1445))
in (_145_1448)::_145_1447))
in (_145_1450, _145_1449)))
in FStar_Syntax_Syntax.Tm_app (_145_1451))
in (FStar_Syntax_Syntax.mk _145_1452 None r))
in (let _145_1461 = (let _145_1460 = (let _145_1459 = (let _145_1454 = (let _145_1453 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_145_1453)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1454 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _145_1458 = (let _145_1457 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _145_1456 = (let _145_1455 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_145_1455)::[])
in (_145_1457)::_145_1456))
in (_145_1459, _145_1458)))
in FStar_Syntax_Syntax.Tm_app (_145_1460))
in (FStar_Syntax_Syntax.mk _145_1461 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (

let base_prob = (let _145_1463 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _145_1462 -> FStar_TypeChecker_Common.TProb (_145_1462)) _145_1463))
in (

let wl = (let _145_1467 = (let _145_1466 = (let _145_1465 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1465 g))
in (FStar_All.pipe_left (fun _145_1464 -> Some (_145_1464)) _145_1466))
in (solve_prob orig _145_1467 [] wl))
=======
in (let _146_1432 = (let _146_1431 = (let _146_1430 = (let _146_1424 = (let _146_1423 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_146_1423)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_1424 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _146_1429 = (let _146_1428 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _146_1427 = (let _146_1426 = (let _146_1425 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_1425))
in (_146_1426)::[])
in (_146_1428)::_146_1427))
in (_146_1430, _146_1429)))
in FStar_Syntax_Syntax.Tm_app (_146_1431))
in (FStar_Syntax_Syntax.mk _146_1432 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let _146_1444 = (let _146_1443 = (let _146_1442 = (let _146_1434 = (let _146_1433 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_146_1433)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _146_1434 env c2_decl c2_decl.FStar_Syntax_Syntax.stronger))
in (let _146_1441 = (let _146_1440 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _146_1439 = (let _146_1438 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _146_1437 = (let _146_1436 = (let _146_1435 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _146_1435))
in (_146_1436)::[])
in (_146_1438)::_146_1437))
in (_146_1440)::_146_1439))
in (_146_1442, _146_1441)))
in FStar_Syntax_Syntax.Tm_app (_146_1443))
in (FStar_Syntax_Syntax.mk _146_1444 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r))
end
in (

let base_prob = (let _146_1446 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _146_1445 -> FStar_TypeChecker_Common.TProb (_146_1445)) _146_1446))
in (

let wl = (let _146_1450 = (let _146_1449 = (let _146_1448 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _146_1448 g))
in (FStar_All.pipe_left (fun _146_1447 -> Some (_146_1447)) _146_1449))
in (solve_prob orig _146_1450 [] wl))
>>>>>>> master
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
<<<<<<< HEAD
(let _145_1468 = (solve_prob orig None [] wl)
in (solve env _145_1468))
end else begin
(

let _55_3060 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1470 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1469 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _145_1470 (rel_to_string problem.FStar_TypeChecker_Common.relation) _145_1469)))
=======
(let _146_1451 = (solve_prob orig None [] wl)
in (solve env _146_1451))
end else begin
(

let _55_3056 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1453 = (FStar_Syntax_Print.comp_to_string c1)
in (let _146_1452 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _146_1453 (rel_to_string problem.FStar_TypeChecker_Common.relation) _146_1452)))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _55_3064 = (let _145_1472 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _145_1471 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in (_145_1472, _145_1471)))
in (match (_55_3064) with
| (c1, c2) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _145_1473 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _145_1473 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3071), FStar_Syntax_Syntax.Total (_55_3074)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _145_1474 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _145_1474 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _145_1476 = (

let _55_3102 = problem
in (let _145_1475 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3102.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1475; FStar_TypeChecker_Common.relation = _55_3102.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3102.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3102.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3102.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3102.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3102.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3102.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3102.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1476 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _145_1478 = (

let _55_3118 = problem
in (let _145_1477 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3118.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3118.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3118.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1477; FStar_TypeChecker_Common.element = _55_3118.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3118.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3118.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3118.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3118.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3118.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1478 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3121), FStar_Syntax_Syntax.Comp (_55_3124)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _145_1479 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _145_1479 wl))
=======
let _55_3060 = (let _146_1455 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _146_1454 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in (_146_1455, _146_1454)))
in (match (_55_3060) with
| (c1, c2) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _146_1456 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _146_1456 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3067), FStar_Syntax_Syntax.Total (_55_3070)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _146_1457 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _146_1457 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _146_1459 = (

let _55_3098 = problem
in (let _146_1458 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3098.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _146_1458; FStar_TypeChecker_Common.relation = _55_3098.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3098.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3098.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3098.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3098.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3098.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3098.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3098.FStar_TypeChecker_Common.rank}))
in (solve_c env _146_1459 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _146_1461 = (

let _55_3114 = problem
in (let _146_1460 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3114.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3114.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3114.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _146_1460; FStar_TypeChecker_Common.element = _55_3114.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3114.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3114.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3114.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3114.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3114.FStar_TypeChecker_Common.rank}))
in (solve_c env _146_1461 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3117), FStar_Syntax_Syntax.Comp (_55_3120)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _146_1462 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _146_1462 wl))
>>>>>>> master
end else begin
(

let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (

let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(

let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (

let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (

<<<<<<< HEAD
let _55_3131 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
=======
let _55_3127 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
>>>>>>> master
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
<<<<<<< HEAD
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _145_1480 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _145_1480))) then begin
=======
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _146_1463 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _146_1463))) then begin
>>>>>>> master
(

let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
<<<<<<< HEAD
(let _145_1485 = (let _145_1484 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1483 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _145_1484 _145_1483)))
in (giveup env _145_1485 orig))
=======
(let _146_1468 = (let _146_1467 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _146_1466 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _146_1467 _146_1466)))
in (giveup env _146_1468 orig))
>>>>>>> master
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


<<<<<<< HEAD
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _145_1489 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3151 -> (match (_55_3151) with
| (_55_3141, _55_3143, u, _55_3146, _55_3148, _55_3150) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _145_1489 (FStar_String.concat ", "))))
=======
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _146_1472 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3147 -> (match (_55_3147) with
| (_55_3137, _55_3139, u, _55_3142, _55_3144, _55_3146) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _146_1472 (FStar_String.concat ", "))))
>>>>>>> master


let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
<<<<<<< HEAD
| _55_3158 -> begin
=======
| _55_3154 -> begin
>>>>>>> master
(

let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) then begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end else begin
"non-trivial"
end
end)
in (

<<<<<<< HEAD
let carry = (let _145_1495 = (FStar_List.map (fun _55_3166 -> (match (_55_3166) with
| (_55_3164, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _145_1495 (FStar_String.concat ",\n")))
=======
let carry = (let _146_1478 = (FStar_List.map (fun _55_3162 -> (match (_55_3162) with
| (_55_3160, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _146_1478 (FStar_String.concat ",\n")))
>>>>>>> master
in (

let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))


let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})


let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)


let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
<<<<<<< HEAD
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3175; FStar_TypeChecker_Env.implicits = _55_3173} -> begin
true
end
| _55_3180 -> begin
=======
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3171; FStar_TypeChecker_Env.implicits = _55_3169} -> begin
true
end
| _55_3176 -> begin
>>>>>>> master
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
<<<<<<< HEAD
| _55_3198 -> begin
(FStar_All.failwith "impossible")
end)
in (let _145_1516 = (

let _55_3200 = g
in (let _145_1515 = (let _145_1514 = (let _145_1513 = (let _145_1507 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_1507)::[])
in (let _145_1512 = (let _145_1511 = (let _145_1510 = (let _145_1508 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _145_1508 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _145_1510 (fun _145_1509 -> FStar_Util.Inl (_145_1509))))
in Some (_145_1511))
in (FStar_Syntax_Util.abs _145_1513 f _145_1512)))
in (FStar_All.pipe_left (fun _145_1506 -> FStar_TypeChecker_Common.NonTrivial (_145_1506)) _145_1514))
in {FStar_TypeChecker_Env.guard_f = _145_1515; FStar_TypeChecker_Env.deferred = _55_3200.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3200.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3200.FStar_TypeChecker_Env.implicits}))
in Some (_145_1516)))
=======
| _55_3194 -> begin
(FStar_All.failwith "impossible")
end)
in (let _146_1499 = (

let _55_3196 = g
in (let _146_1498 = (let _146_1497 = (let _146_1496 = (let _146_1490 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_1490)::[])
in (let _146_1495 = (let _146_1494 = (let _146_1493 = (let _146_1491 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _146_1491 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _146_1493 (fun _146_1492 -> FStar_Util.Inl (_146_1492))))
in Some (_146_1494))
in (FStar_Syntax_Util.abs _146_1496 f _146_1495)))
in (FStar_All.pipe_left (fun _146_1489 -> FStar_TypeChecker_Common.NonTrivial (_146_1489)) _146_1497))
in {FStar_TypeChecker_Env.guard_f = _146_1498; FStar_TypeChecker_Env.deferred = _55_3196.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3196.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3196.FStar_TypeChecker_Env.implicits}))
in Some (_146_1499)))
>>>>>>> master
end))


let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

<<<<<<< HEAD
let _55_3207 = g
in (let _145_1527 = (let _145_1526 = (let _145_1525 = (let _145_1524 = (let _145_1523 = (let _145_1522 = (FStar_Syntax_Syntax.as_arg e)
in (_145_1522)::[])
in (f, _145_1523))
in FStar_Syntax_Syntax.Tm_app (_145_1524))
in (FStar_Syntax_Syntax.mk _145_1525 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _145_1521 -> FStar_TypeChecker_Common.NonTrivial (_145_1521)) _145_1526))
in {FStar_TypeChecker_Env.guard_f = _145_1527; FStar_TypeChecker_Env.deferred = _55_3207.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3207.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3207.FStar_TypeChecker_Env.implicits}))
=======
let _55_3203 = g
in (let _146_1510 = (let _146_1509 = (let _146_1508 = (let _146_1507 = (let _146_1506 = (let _146_1505 = (FStar_Syntax_Syntax.as_arg e)
in (_146_1505)::[])
in (f, _146_1506))
in FStar_Syntax_Syntax.Tm_app (_146_1507))
in (FStar_Syntax_Syntax.mk _146_1508 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _146_1504 -> FStar_TypeChecker_Common.NonTrivial (_146_1504)) _146_1509))
in {FStar_TypeChecker_Env.guard_f = _146_1510; FStar_TypeChecker_Env.deferred = _55_3203.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3203.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3203.FStar_TypeChecker_Env.implicits}))
>>>>>>> master
end))


let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
<<<<<<< HEAD
| FStar_TypeChecker_Common.NonTrivial (_55_3212) -> begin
=======
| FStar_TypeChecker_Common.NonTrivial (_55_3208) -> begin
>>>>>>> master
(FStar_All.failwith "impossible")
end))


let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
<<<<<<< HEAD
(let _145_1534 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_145_1534))
=======
(let _146_1517 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_146_1517))
>>>>>>> master
end))


let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
<<<<<<< HEAD
| _55_3230 -> begin
=======
| _55_3226 -> begin
>>>>>>> master
FStar_TypeChecker_Common.NonTrivial (t)
end))


let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
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


<<<<<<< HEAD
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _145_1557 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _145_1557; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))
=======
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _146_1540 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _146_1540; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))
>>>>>>> master


let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

<<<<<<< HEAD
let _55_3257 = g
in (let _145_1572 = (let _145_1571 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _145_1571 (fun _145_1570 -> FStar_TypeChecker_Common.NonTrivial (_145_1570))))
in {FStar_TypeChecker_Env.guard_f = _145_1572; FStar_TypeChecker_Env.deferred = _55_3257.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3257.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3257.FStar_TypeChecker_Env.implicits}))
=======
let _55_3253 = g
in (let _146_1555 = (let _146_1554 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _146_1554 (fun _146_1553 -> FStar_TypeChecker_Common.NonTrivial (_146_1553))))
in {FStar_TypeChecker_Env.guard_f = _146_1555; FStar_TypeChecker_Env.deferred = _55_3253.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3253.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3253.FStar_TypeChecker_Env.implicits}))
>>>>>>> master
end))


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
<<<<<<< HEAD
(let _145_1580 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _145_1579 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _145_1580 (rel_to_string rel) _145_1579)))
=======
(let _146_1563 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _146_1562 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _146_1563 (rel_to_string rel) _146_1562)))
>>>>>>> master
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (

<<<<<<< HEAD
let x = (let _145_1591 = (let _145_1590 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _145_1589 -> Some (_145_1589)) _145_1590))
in (FStar_Syntax_Syntax.new_bv _145_1591 t1))
=======
let x = (let _146_1574 = (let _146_1573 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _146_1572 -> Some (_146_1572)) _146_1573))
in (FStar_Syntax_Syntax.new_bv _146_1574 t1))
>>>>>>> master
in (

let env = (FStar_TypeChecker_Env.push_bv env x)
in (

<<<<<<< HEAD
let p = (let _145_1595 = (let _145_1593 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _145_1592 -> Some (_145_1592)) _145_1593))
in (let _145_1594 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _145_1595 _145_1594)))
=======
let p = (let _146_1578 = (let _146_1576 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _146_1575 -> Some (_146_1575)) _146_1576))
in (let _146_1577 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _146_1578 _146_1577)))
>>>>>>> master
in (FStar_TypeChecker_Common.TProb (p), x)))))


let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

<<<<<<< HEAD
let _55_3277 = probs
in {attempting = _55_3277.attempting; wl_deferred = _55_3277.wl_deferred; ctr = _55_3277.ctr; defer_ok = false; smt_ok = _55_3277.smt_ok; tcenv = _55_3277.tcenv})
=======
let _55_3273 = probs
in {attempting = _55_3273.attempting; wl_deferred = _55_3273.wl_deferred; ctr = _55_3273.ctr; defer_ok = false; smt_ok = _55_3273.smt_ok; tcenv = _55_3273.tcenv})
>>>>>>> master
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

<<<<<<< HEAD
let _55_3284 = (FStar_Unionfind.commit tx)
=======
let _55_3280 = (FStar_Unionfind.commit tx)
>>>>>>> master
in Some (deferred))
end
| Failed (d, s) -> begin
(

<<<<<<< HEAD
let _55_3290 = (FStar_Unionfind.rollback tx)
in (

let _55_3292 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_1607 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _145_1607))
=======
let _55_3286 = (FStar_Unionfind.rollback tx)
in (

let _55_3288 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _146_1590 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _146_1590))
>>>>>>> master
end else begin
()
end
in (err (d, s))))
end)))))


let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

<<<<<<< HEAD
let _55_3299 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1612 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _145_1612))
=======
let _55_3295 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _146_1595 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _146_1595))
>>>>>>> master
end else begin
()
end
in (

let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (

<<<<<<< HEAD
let _55_3302 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1613 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _145_1613))
=======
let _55_3298 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _146_1596 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _146_1596))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let f = (match ((let _145_1614 = (FStar_Syntax_Util.unmeta f)
in _145_1614.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3307 -> begin
=======
let f = (match ((let _146_1597 = (FStar_Syntax_Util.unmeta f)
in _146_1597.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3303 -> begin
>>>>>>> master
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (

<<<<<<< HEAD
let _55_3309 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3309.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3309.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3309.FStar_TypeChecker_Env.implicits})))))
=======
let _55_3305 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3305.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3305.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3305.FStar_TypeChecker_Env.implicits})))))
>>>>>>> master
end))


let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
<<<<<<< HEAD
(let _145_1626 = (let _145_1625 = (let _145_1624 = (let _145_1623 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _145_1623 (fun _145_1622 -> FStar_TypeChecker_Common.NonTrivial (_145_1622))))
in {FStar_TypeChecker_Env.guard_f = _145_1624; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _145_1625))
in (FStar_All.pipe_left (fun _145_1621 -> Some (_145_1621)) _145_1626))
=======
(let _146_1609 = (let _146_1608 = (let _146_1607 = (let _146_1606 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _146_1606 (fun _146_1605 -> FStar_TypeChecker_Common.NonTrivial (_146_1605))))
in {FStar_TypeChecker_Env.guard_f = _146_1607; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _146_1608))
in (FStar_All.pipe_left (fun _146_1604 -> Some (_146_1604)) _146_1609))
>>>>>>> master
end))


let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (

<<<<<<< HEAD
let _55_3320 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1634 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1633 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _145_1634 _145_1633)))
=======
let _55_3316 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1617 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_1616 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _146_1617 _146_1616)))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let prob = (let _145_1637 = (let _145_1636 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _145_1636))
in (FStar_All.pipe_left (fun _145_1635 -> FStar_TypeChecker_Common.TProb (_145_1635)) _145_1637))
in (

let g = (let _145_1639 = (solve_and_commit env (singleton env prob) (fun _55_3323 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1639))
=======
let prob = (let _146_1620 = (let _146_1619 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _146_1619))
in (FStar_All.pipe_left (fun _146_1618 -> FStar_TypeChecker_Common.TProb (_146_1618)) _146_1620))
in (

let g = (let _146_1622 = (solve_and_commit env (singleton env prob) (fun _55_3319 -> None))
in (FStar_All.pipe_left (with_guard env prob) _146_1622))
>>>>>>> master
in g))))


let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
<<<<<<< HEAD
(let _145_1649 = (let _145_1648 = (let _145_1647 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1646 = (FStar_TypeChecker_Env.get_range env)
in (_145_1647, _145_1646)))
in FStar_Syntax_Syntax.Error (_145_1648))
in (Prims.raise _145_1649))
=======
(let _146_1632 = (let _146_1631 = (let _146_1630 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _146_1629 = (FStar_TypeChecker_Env.get_range env)
in (_146_1630, _146_1629)))
in FStar_Syntax_Syntax.Error (_146_1631))
in (Prims.raise _146_1632))
>>>>>>> master
end
| Some (g) -> begin
(

<<<<<<< HEAD
let _55_3332 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1652 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1651 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_1650 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _145_1652 _145_1651 _145_1650))))
=======
let _55_3328 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1635 = (FStar_Syntax_Print.term_to_string t1)
in (let _146_1634 = (FStar_Syntax_Print.term_to_string t2)
in (let _146_1633 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _146_1635 _146_1634 _146_1633))))
>>>>>>> master
end else begin
()
end
in g)
end))


let try_subtype' : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 smt_ok -> (

<<<<<<< HEAD
let _55_3338 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1662 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1661 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _145_1662 _145_1661)))
=======
let _55_3333 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1643 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_1642 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _146_1643 _146_1642)))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _55_3342 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3342) with
| (prob, x) -> begin
(

let g = (let _145_1664 = (solve_and_commit env (singleton' env prob smt_ok) (fun _55_3343 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1664))
in (

let _55_3346 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _145_1668 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1667 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _145_1666 = (let _145_1665 = (FStar_Util.must g)
in (guard_to_string env _145_1665))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _145_1668 _145_1667 _145_1666))))
=======
let _55_3337 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3337) with
| (prob, x) -> begin
(

let g = (let _146_1645 = (solve_and_commit env (singleton env prob) (fun _55_3338 -> None))
in (FStar_All.pipe_left (with_guard env prob) _146_1645))
in (

let _55_3341 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _146_1649 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _146_1648 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _146_1647 = (let _146_1646 = (FStar_Util.must g)
in (guard_to_string env _146_1646))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _146_1649 _146_1648 _146_1647))))
>>>>>>> master
end else begin
()
end
in (abstract_guard x g)))
end))))


<<<<<<< HEAD
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (try_subtype' env t1 t2 true))


let subtype_fail = (fun env t1 t2 -> (let _145_1681 = (let _145_1680 = (let _145_1679 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1678 = (FStar_TypeChecker_Env.get_range env)
in (_145_1679, _145_1678)))
in FStar_Syntax_Syntax.Error (_145_1680))
in (Prims.raise _145_1681)))
=======
let subtype_fail = (fun env t1 t2 -> (let _146_1656 = (let _146_1655 = (let _146_1654 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _146_1653 = (FStar_TypeChecker_Env.get_range env)
in (_146_1654, _146_1653)))
in FStar_Syntax_Syntax.Error (_146_1655))
in (Prims.raise _146_1656)))
>>>>>>> master


let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (

<<<<<<< HEAD
let _55_3357 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1689 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1688 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _145_1689 _145_1688)))
=======
let _55_3349 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1664 = (FStar_Syntax_Print.comp_to_string c1)
in (let _146_1663 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _146_1664 _146_1663)))
>>>>>>> master
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

<<<<<<< HEAD
let prob = (let _145_1692 = (let _145_1691 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _145_1691 "sub_comp"))
in (FStar_All.pipe_left (fun _145_1690 -> FStar_TypeChecker_Common.CProb (_145_1690)) _145_1692))
in (let _145_1694 = (solve_and_commit env (singleton env prob) (fun _55_3361 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1694))))))
=======
let prob = (let _146_1667 = (let _146_1666 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _146_1666 "sub_comp"))
in (FStar_All.pipe_left (fun _146_1665 -> FStar_TypeChecker_Common.CProb (_146_1665)) _146_1667))
in (let _146_1669 = (solve_and_commit env (singleton env prob) (fun _55_3353 -> None))
in (FStar_All.pipe_left (with_guard env prob) _146_1669))))))
>>>>>>> master


let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (

let fail = (fun msg u1 u2 -> (

<<<<<<< HEAD
let _55_3370 = (FStar_Unionfind.rollback tx)
=======
let _55_3362 = (FStar_Unionfind.rollback tx)
>>>>>>> master
in (

let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
<<<<<<< HEAD
in (let _145_1712 = (let _145_1711 = (let _145_1710 = (let _145_1708 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_1707 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _145_1708 _145_1707 msg)))
in (let _145_1709 = (FStar_TypeChecker_Env.get_range env)
in (_145_1710, _145_1709)))
in FStar_Syntax_Syntax.Error (_145_1711))
in (Prims.raise _145_1712)))))
=======
in (let _146_1687 = (let _146_1686 = (let _146_1685 = (let _146_1683 = (FStar_Syntax_Print.univ_to_string u1)
in (let _146_1682 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _146_1683 _146_1682 msg)))
in (let _146_1684 = (FStar_TypeChecker_Env.get_range env)
in (_146_1685, _146_1684)))
in FStar_Syntax_Syntax.Error (_146_1686))
in (Prims.raise _146_1687)))))
>>>>>>> master
in (

let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| (hd)::tl -> begin
(

<<<<<<< HEAD
let _55_3386 = hd
in (match (_55_3386) with
=======
let _55_3378 = hd
in (match (_55_3378) with
>>>>>>> master
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
<<<<<<< HEAD
(let _145_1719 = (insert uv u1 tl)
in (hd)::_145_1719)
=======
(let _146_1694 = (insert uv u1 tl)
in (hd)::_146_1694)
>>>>>>> master
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
<<<<<<< HEAD
(let _145_1724 = (insert uv u1 out)
in (group_by _145_1724 rest))
end)
end
| _55_3401 -> begin
=======
(let _146_1699 = (insert uv u1 out)
in (group_by _146_1699 rest))
end)
end
| _55_3393 -> begin
>>>>>>> master
None
end))
end))
in (

<<<<<<< HEAD
let ad_hoc_fallback = (fun _55_3403 -> (match (()) with
=======
let ad_hoc_fallback = (fun _55_3395 -> (match (()) with
>>>>>>> master
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
<<<<<<< HEAD
| _55_3406 -> begin
=======
| _55_3398 -> begin
>>>>>>> master
(

let wl = (

<<<<<<< HEAD
let _55_3407 = (empty_worklist env)
in {attempting = _55_3407.attempting; wl_deferred = _55_3407.wl_deferred; ctr = _55_3407.ctr; defer_ok = true; smt_ok = _55_3407.smt_ok; tcenv = _55_3407.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3412 -> (match (_55_3412) with
=======
let _55_3399 = (empty_worklist env)
in {attempting = _55_3399.attempting; wl_deferred = _55_3399.wl_deferred; ctr = _55_3399.ctr; defer_ok = true; smt_ok = _55_3399.smt_ok; tcenv = _55_3399.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3404 -> (match (_55_3404) with
>>>>>>> master
| (u1, u2) -> begin
(

let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (

let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
<<<<<<< HEAD
| _55_3417 -> begin
=======
| _55_3409 -> begin
>>>>>>> master
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(

let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
<<<<<<< HEAD
| _55_3427 -> begin
=======
| _55_3419 -> begin
>>>>>>> master
(u1)::[]
end)
in (

let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
<<<<<<< HEAD
| _55_3432 -> begin
=======
| _55_3424 -> begin
>>>>>>> master
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(

<<<<<<< HEAD
let _55_3439 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3439) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3443 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3443) with
=======
let _55_3431 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3431) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (

let _55_3435 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3435) with
>>>>>>> master
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
<<<<<<< HEAD
| USolved (_55_3445) -> begin
=======
| USolved (_55_3437) -> begin
>>>>>>> master
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

<<<<<<< HEAD
let _55_3449 = (empty_worklist env)
in {attempting = _55_3449.attempting; wl_deferred = _55_3449.wl_deferred; ctr = _55_3449.ctr; defer_ok = false; smt_ok = _55_3449.smt_ok; tcenv = _55_3449.tcenv})
=======
let _55_3441 = (empty_worklist env)
in {attempting = _55_3441.attempting; wl_deferred = _55_3441.wl_deferred; ctr = _55_3441.ctr; defer_ok = false; smt_ok = _55_3441.smt_ok; tcenv = _55_3441.tcenv})
>>>>>>> master
in (

let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| ((u, lower_bounds))::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
<<<<<<< HEAD
| _55_3464 -> begin
=======
| _55_3456 -> begin
>>>>>>> master
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

<<<<<<< HEAD
let _55_3469 = (solve_universe_inequalities' tx env ineqs)
=======
let _55_3461 = (solve_universe_inequalities' tx env ineqs)
>>>>>>> master
in (FStar_Unionfind.commit tx))))


let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (

<<<<<<< HEAD
let fail = (fun _55_3476 -> (match (_55_3476) with
=======
let fail = (fun _55_3468 -> (match (_55_3468) with
>>>>>>> master
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (

let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (

<<<<<<< HEAD
let _55_3479 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1745 = (wl_to_string wl)
in (let _145_1744 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _145_1745 _145_1744)))
=======
let _55_3471 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1720 = (wl_to_string wl)
in (let _146_1719 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _146_1720 _146_1719)))
>>>>>>> master
end else begin
()
end
in (

let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(

<<<<<<< HEAD
let _55_3483 = g
in {FStar_TypeChecker_Env.guard_f = _55_3483.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3483.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3483.FStar_TypeChecker_Env.implicits})
end
| _55_3486 -> begin
=======
let _55_3475 = g
in {FStar_TypeChecker_Env.guard_f = _55_3475.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3475.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3475.FStar_TypeChecker_Env.implicits})
end
| _55_3478 -> begin
>>>>>>> master
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (

<<<<<<< HEAD
let _55_3488 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3490 = g
in {FStar_TypeChecker_Env.guard_f = _55_3490.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3490.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3490.FStar_TypeChecker_Env.implicits})))))))
=======
let _55_3480 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (

let _55_3482 = g
in {FStar_TypeChecker_Env.guard_f = _55_3482.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3482.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3482.FStar_TypeChecker_Env.implicits})))))))
>>>>>>> master


let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (

let g = (solve_deferred_constraints env g)
in (

<<<<<<< HEAD
let _55_3505 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
=======
let _55_3497 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
>>>>>>> master
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(

<<<<<<< HEAD
let _55_3503 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1762 = (FStar_TypeChecker_Env.get_range env)
in (let _145_1761 = (let _145_1760 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _145_1760))
in (FStar_TypeChecker_Errors.diag _145_1762 _145_1761)))
=======
let _55_3495 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _146_1737 = (FStar_TypeChecker_Env.get_range env)
in (let _146_1736 = (let _146_1735 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _146_1735))
in (FStar_TypeChecker_Errors.diag _146_1737 _146_1736)))
>>>>>>> master
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (

<<<<<<< HEAD
let _55_3507 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3507.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3507.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3507.FStar_TypeChecker_Env.implicits}))))
=======
let _55_3499 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3499.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3499.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3499.FStar_TypeChecker_Env.implicits}))))
>>>>>>> master


let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))


let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (

let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
<<<<<<< HEAD
| _55_3516 -> begin
=======
| _55_3508 -> begin
>>>>>>> master
false
end))
in (

<<<<<<< HEAD
let rec until_fixpoint = (fun _55_3520 implicits -> (match (_55_3520) with
=======
let rec until_fixpoint = (fun _55_3512 implicits -> (match (_55_3512) with
>>>>>>> master
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint ([], false) out)
end
end
| (hd)::tl -> begin
(

<<<<<<< HEAD
let _55_3533 = hd
in (match (_55_3533) with
| (_55_3527, env, u, tm, k, r) -> begin
=======
let _55_3525 = hd
in (match (_55_3525) with
| (_55_3519, env, u, tm, k, r) -> begin
>>>>>>> master
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(

let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (

let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (

<<<<<<< HEAD
let _55_3536 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1778 = (FStar_Syntax_Print.uvar_to_string u)
in (let _145_1777 = (FStar_Syntax_Print.term_to_string tm)
in (let _145_1776 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _145_1778 _145_1777 _145_1776))))
=======
let _55_3528 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _146_1753 = (FStar_Syntax_Print.uvar_to_string u)
in (let _146_1752 = (FStar_Syntax_Print.term_to_string tm)
in (let _146_1751 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _146_1753 _146_1752 _146_1751))))
>>>>>>> master
end else begin
()
end
in (

<<<<<<< HEAD
let _55_3545 = (env.FStar_TypeChecker_Env.type_of (

let _55_3538 = env
in {FStar_TypeChecker_Env.solver = _55_3538.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3538.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3538.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3538.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3538.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3538.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3538.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3538.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3538.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3538.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3538.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3538.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3538.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3538.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3538.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3538.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3538.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3538.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _55_3538.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3538.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3545) with
| (_55_3541, _55_3543, g) -> begin
=======
let _55_3537 = (env.FStar_TypeChecker_Env.type_of (

let _55_3530 = env
in {FStar_TypeChecker_Env.solver = _55_3530.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3530.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3530.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3530.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3530.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3530.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3530.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3530.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3530.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3530.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3530.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3530.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3530.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3530.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3530.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3530.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3530.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3530.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _55_3530.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3530.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3537) with
| (_55_3533, _55_3535, g) -> begin
>>>>>>> master
(

let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(

<<<<<<< HEAD
let _55_3546 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3546.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3546.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3546.FStar_TypeChecker_Env.implicits})
=======
let _55_3538 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3538.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3538.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3538.FStar_TypeChecker_Env.implicits})
>>>>>>> master
end else begin
g
end
in (

<<<<<<< HEAD
let g' = (discharge_guard' (Some ((fun _55_3549 -> (match (()) with
=======
let g' = (discharge_guard' (Some ((fun _55_3541 -> (match (()) with
>>>>>>> master
| () -> begin
(FStar_Syntax_Print.term_to_string tm)
end)))) env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl)))
end)))))
end
end))
end)
end))
in (

<<<<<<< HEAD
let _55_3551 = g
in (let _145_1782 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3551.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3551.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3551.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _145_1782})))))
=======
let _55_3543 = g
in (let _146_1757 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3543.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3543.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3543.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _146_1757})))))
>>>>>>> master


let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (

<<<<<<< HEAD
let g = (let _145_1787 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _145_1787 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _145_1788 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _145_1788))
end
| ((reason, _55_3561, _55_3563, e, t, r))::_55_3558 -> begin
(let _145_1793 = (let _145_1792 = (let _145_1791 = (let _145_1790 = (FStar_Syntax_Print.term_to_string t)
in (let _145_1789 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _145_1790 _145_1789 reason)))
in (_145_1791, r))
in FStar_Syntax_Syntax.Error (_145_1792))
in (Prims.raise _145_1793))
=======
let g = (let _146_1762 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _146_1762 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _146_1763 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _146_1763))
end
| ((reason, _55_3553, _55_3555, e, t, r))::_55_3550 -> begin
(let _146_1768 = (let _146_1767 = (let _146_1766 = (let _146_1765 = (FStar_Syntax_Print.term_to_string t)
in (let _146_1764 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _146_1765 _146_1764 reason)))
in (_146_1766, r))
in (_146_1767)::[])
in (FStar_TypeChecker_Errors.add_errors env _146_1768))
>>>>>>> master
end)))


let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (

<<<<<<< HEAD
let _55_3571 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3571.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3571.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _55_3571.FStar_TypeChecker_Env.implicits}))
=======
let _55_3563 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3563.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3563.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _55_3563.FStar_TypeChecker_Env.implicits}))
>>>>>>> master





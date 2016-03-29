
open Prims
# 65 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _135_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _135_8 Prims.op_Negation)))))
in (
# 67 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(
# 70 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _56_39 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _135_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _135_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _135_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_135_10, uv)))))
end))))

# 82 "FStar.TypeChecker.Rel.fst"
type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)

# 83 "FStar.TypeChecker.Rel.fst"
let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.TypeChecker.Rel.fst"
let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.TypeChecker.Rel.fst"
let ___TERM____0 = (fun projectee -> (match (projectee) with
| TERM (_56_45) -> begin
_56_45
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_56_48) -> begin
_56_48
end))

# 87 "FStar.TypeChecker.Rel.fst"
type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

# 87 "FStar.TypeChecker.Rel.fst"
let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

# 97 "FStar.TypeChecker.Rel.fst"
type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)

# 98 "FStar.TypeChecker.Rel.fst"
let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.TypeChecker.Rel.fst"
let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.TypeChecker.Rel.fst"
let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_56_58) -> begin
_56_58
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_56_61) -> begin
_56_61
end))

# 101 "FStar.TypeChecker.Rel.fst"
type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

# 102 "FStar.TypeChecker.Rel.fst"
let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.TypeChecker.Rel.fst"
let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 104 "FStar.TypeChecker.Rel.fst"
let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 106 "FStar.TypeChecker.Rel.fst"
type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

# 107 "FStar.TypeChecker.Rel.fst"
type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

# 108 "FStar.TypeChecker.Rel.fst"
type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

# 117 "FStar.TypeChecker.Rel.fst"
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

# 122 "FStar.TypeChecker.Rel.fst"
let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

# 124 "FStar.TypeChecker.Rel.fst"
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _56_2 -> (match (_56_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _135_109 = (let _135_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _135_107 = (let _135_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _135_105 = (let _135_104 = (let _135_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _135_102 = (let _135_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _135_100 = (let _135_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _135_98 = (let _135_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_135_97)::[])
in (_135_99)::_135_98))
in (_135_101)::_135_100))
in (_135_103)::_135_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_135_104)
in (_135_106)::_135_105))
in (_135_108)::_135_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _135_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _135_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _135_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _135_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _135_110)))
end))

# 140 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _56_3 -> (match (_56_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _135_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _135_116 FStar_Util.string_of_int))
end
in (let _135_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _135_117)))
end
| TERM ((u, _56_85), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _135_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _135_118 FStar_Util.string_of_int))
end
in (let _135_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _135_119)))
end))

# 148 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _135_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _135_124 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _135_128 = (let _135_127 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _135_127 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _135_128 (FStar_String.concat ", "))))

# 150 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _135_131 = (FStar_All.pipe_right args (FStar_List.map (fun _56_98 -> (match (_56_98) with
| (x, _56_97) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _135_131 (FStar_String.concat " "))))

# 159 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 167 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _56_102 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _56_102.wl_deferred; ctr = _56_102.ctr; defer_ok = _56_102.defer_ok; smt_ok = _56_102.smt_ok; tcenv = _56_102.tcenv}))

# 168 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _56_106 = (empty_worklist env)
in (let _135_140 = (FStar_List.map Prims.snd g)
in {attempting = _135_140; wl_deferred = _56_106.wl_deferred; ctr = _56_106.ctr; defer_ok = false; smt_ok = _56_106.smt_ok; tcenv = _56_106.tcenv})))

# 169 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _56_111 = wl
in {attempting = _56_111.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _56_111.ctr; defer_ok = _56_111.defer_ok; smt_ok = _56_111.smt_ok; tcenv = _56_111.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _56_115 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _56_115.wl_deferred; ctr = _56_115.ctr; defer_ok = _56_115.defer_ok; smt_ok = _56_115.smt_ok; tcenv = _56_115.tcenv}))

# 172 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _56_120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_157 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _135_157))
end else begin
()
end
in Failed ((prob, reason))))

# 183 "FStar.TypeChecker.Rel.fst"
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

# 187 "FStar.TypeChecker.Rel.fst"
let invert = (fun p -> (
# 187 "FStar.TypeChecker.Rel.fst"
let _56_127 = p
in {FStar_TypeChecker_Common.pid = _56_127.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _56_127.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_127.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_127.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_127.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_127.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_127.FStar_TypeChecker_Common.rank}))

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 189 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _56_5 -> (match (_56_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _135_164 -> FStar_TypeChecker_Common.TProb (_135_164)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _135_165 -> FStar_TypeChecker_Common.CProb (_135_165)))
end))

# 192 "FStar.TypeChecker.Rel.fst"
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

# 196 "FStar.TypeChecker.Rel.fst"
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _56_7 -> (match (_56_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 199 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _56_8 -> (match (_56_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 202 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _56_9 -> (match (_56_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 205 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _56_10 -> (match (_56_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 208 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _56_11 -> (match (_56_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 211 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _56_12 -> (match (_56_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 214 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _56_13 -> (match (_56_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _135_184 -> FStar_TypeChecker_Common.TProb (_135_184)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _135_185 -> FStar_TypeChecker_Common.CProb (_135_185)) (invert p))
end))

# 217 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 218 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _56_177 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _56_178 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 222 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _135_198 = (next_pid ())
in (let _135_197 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _135_198; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _135_197; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 234 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _135_208 = (next_pid ())
in (let _135_207 = (let _135_206 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _135_206 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _135_208; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _135_207; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 248 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _135_215 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _135_215; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 260 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 264 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _135_227 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _135_226 = (prob_to_string env d)
in (let _135_225 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _135_227 _135_226 _135_225 s)))))

# 278 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _56_14 -> (match (_56_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _56_219 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _56_222), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 286 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _56_15 -> (match (_56_15) with
| UNIV (_56_231) -> begin
None
end
| TERM ((u, _56_235), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 290 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _56_16 -> (match (_56_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _56_248 -> begin
None
end))))

# 302 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _135_246 = (let _135_245 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _135_245))
in (FStar_Syntax_Subst.compress _135_246)))

# 303 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _135_251 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _135_251)))

# 304 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _135_254 = (sn env (Prims.fst t))
in (_135_254, (Prims.snd t))))

# 305 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _56_259 -> (match (_56_259) with
| (x, imp) -> begin
(let _135_261 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _56_260 = x
in (let _135_260 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_260}))
in (_135_261, imp))
end)))))

# 312 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _135_268 = (aux u)
in FStar_Syntax_Syntax.U_succ (_135_268))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _135_269 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_135_269))
end
| _56_272 -> begin
u
end)))
in (let _135_270 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _135_270))))

# 325 "FStar.TypeChecker.Rel.fst"
let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))

# 327 "FStar.TypeChecker.Rel.fst"
let base_and_refinement = (fun env wl t1 -> (
# 328 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _56_292; FStar_Syntax_Syntax.pos = _56_290; FStar_Syntax_Syntax.vars = _56_288} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _135_284 = (let _135_283 = (FStar_Syntax_Print.term_to_string tt)
in (let _135_282 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _135_283 _135_282)))
in (FStar_All.failwith _135_284))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(
# 343 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _135_285 = (FStar_Syntax_Subst.compress t1')
in _135_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_56_310) -> begin
(aux true t1')
end
| _56_313 -> begin
(t1, None)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(FStar_All.failwith "Unhandled cases!")
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _135_288 = (let _135_287 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_286 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _135_287 _135_286)))
in (FStar_All.failwith _135_288))
end))
in (let _135_289 = (whnf env t1)
in (aux false _135_289))))

# 367 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _135_294 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _135_294 Prims.fst)))

# 369 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _135_297 = (FStar_Syntax_Syntax.null_bv t)
in (_135_297, FStar_Syntax_Util.t_true)))

# 371 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _56_359 = (base_and_refinement env wl t)
in (match (_56_359) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

# 377 "FStar.TypeChecker.Rel.fst"
let force_refinement = (fun _56_367 -> (match (_56_367) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _56_375 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_56_375) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 391 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _56_17 -> (match (_56_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _135_310 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _135_309 = (let _135_306 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _135_306))
in (let _135_308 = (let _135_307 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _135_307))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _135_310 _135_309 (rel_to_string p.FStar_TypeChecker_Common.relation) _135_308))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _135_313 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _135_312 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _135_311 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _135_313 _135_312 (rel_to_string p.FStar_TypeChecker_Common.relation) _135_311))))
end))

# 406 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _135_319 = (let _135_318 = (let _135_317 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _56_388 -> (match (_56_388) with
| (_56_384, _56_386, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _135_317))
in (FStar_List.map (wl_prob_to_string wl) _135_318))
in (FStar_All.pipe_right _135_319 (FStar_String.concat "\n\t"))))

# 416 "FStar.TypeChecker.Rel.fst"
let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (
# 417 "FStar.TypeChecker.Rel.fst"
let _56_407 = (match ((let _135_326 = (FStar_Syntax_Subst.compress k)
in _135_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _135_327 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _135_327))
end else begin
(
# 421 "FStar.TypeChecker.Rel.fst"
let _56_398 = (FStar_Syntax_Util.abs_formals t)
in (match (_56_398) with
| (ys', t) -> begin
(let _135_328 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _135_328))
end))
end
end
| _56_400 -> begin
(let _135_330 = (let _135_329 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _135_329))
in ((ys, t), _135_330))
end)
in (match (_56_407) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t None)
end else begin
(
# 426 "FStar.TypeChecker.Rel.fst"
let c = (let _135_331 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _135_331 c))
in (let _135_333 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _135_332 -> Some (_135_332)))
in (FStar_Syntax_Util.abs ys t _135_333)))
end
end)))

# 429 "FStar.TypeChecker.Rel.fst"
let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (
# 430 "FStar.TypeChecker.Rel.fst"
let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (
# 433 "FStar.TypeChecker.Rel.fst"
let _56_421 = (p_guard prob)
in (match (_56_421) with
| (_56_419, uv) -> begin
(
# 434 "FStar.TypeChecker.Rel.fst"
let _56_434 = (match ((let _135_344 = (FStar_Syntax_Subst.compress uv)
in _135_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 436 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 437 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _135_346 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _135_346 Prims.op_Negation)))))
in (
# 438 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs k bs phi)
in (
# 439 "FStar.TypeChecker.Rel.fst"
let _56_430 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _135_349 = (FStar_Util.string_of_int (p_pid prob))
in (let _135_348 = (FStar_Syntax_Print.term_to_string uv)
in (let _135_347 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _135_349 _135_348 _135_347))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _56_433 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 446 "FStar.TypeChecker.Rel.fst"
let _56_436 = (commit uvis)
in (
# 447 "FStar.TypeChecker.Rel.fst"
let _56_438 = wl
in {attempting = _56_438.attempting; wl_deferred = _56_438.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _56_438.defer_ok; smt_ok = _56_438.smt_ok; tcenv = _56_438.tcenv})))
end))))

# 449 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 450 "FStar.TypeChecker.Rel.fst"
let _56_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_358 = (FStar_Util.string_of_int pid)
in (let _135_357 = (let _135_356 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _135_356 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _135_358 _135_357)))
end else begin
()
end
in (
# 452 "FStar.TypeChecker.Rel.fst"
let _56_445 = (commit sol)
in (
# 453 "FStar.TypeChecker.Rel.fst"
let _56_447 = wl
in {attempting = _56_447.attempting; wl_deferred = _56_447.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _56_447.defer_ok; smt_ok = _56_447.smt_ok; tcenv = _56_447.tcenv}))))

# 455 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 456 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_56_457, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _135_371 = (FStar_Syntax_Util.mk_conj t f)
in Some (_135_371))
end))
in (
# 460 "FStar.TypeChecker.Rel.fst"
let _56_469 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_374 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _135_373 = (let _135_372 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _135_372 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _135_374 _135_373)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 472 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _135_384 = (let _135_382 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _135_382 FStar_Util.set_elements))
in (FStar_All.pipe_right _135_384 (FStar_Util.for_some (fun _56_478 -> (match (_56_478) with
| (uv, _56_477) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 478 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 479 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 480 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _135_391 = (let _135_390 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _135_389 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _135_390 _135_389)))
in Some (_135_391))
end
in (occurs_ok, msg))))

# 487 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 488 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 489 "FStar.TypeChecker.Rel.fst"
let _56_493 = (occurs_check env wl uk t)
in (match (_56_493) with
| (occurs_ok, msg) -> begin
(let _135_397 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _135_397, (msg, fvs, fvs_t)))
end))))

# 492 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 493 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 495 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 496 "FStar.TypeChecker.Rel.fst"
let _56_511 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _56_503 _56_506 -> (match ((_56_503, _56_506)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _135_406 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _135_406)) then begin
(isect, isect_set)
end else begin
(
# 502 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _135_407 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _135_407))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_56_511) with
| (isect, _56_510) -> begin
(FStar_List.rev isect)
end)))))

# 509 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _56_517 _56_521 -> (match ((_56_517, _56_521)) with
| ((a, _56_516), (b, _56_520)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 513 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 514 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _56_531 -> (match (_56_531) with
| (b, _56_530) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _56_533 -> begin
None
end)))

# 523 "FStar.TypeChecker.Rel.fst"
let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 527 "FStar.TypeChecker.Rel.fst"
let _56_542 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_422 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _135_422))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 531 "FStar.TypeChecker.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _56_556; FStar_Syntax_Syntax.pos = _56_554; FStar_Syntax_Syntax.vars = _56_552}, args) -> begin
(t, uv, k, args)
end
| _56_566 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 536 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 537 "FStar.TypeChecker.Rel.fst"
let _56_573 = (destruct_flex_t t)
in (match (_56_573) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _56_577 -> begin
((t, uv, k, args), None)
end)
end)))

# 611 "FStar.TypeChecker.Rel.fst"
type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch

# 612 "FStar.TypeChecker.Rel.fst"
let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 613 "FStar.TypeChecker.Rel.fst"
let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 614 "FStar.TypeChecker.Rel.fst"
let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 612 "FStar.TypeChecker.Rel.fst"
let ___MisMatch____0 = (fun projectee -> (match (projectee) with
| MisMatch (_56_580) -> begin
_56_580
end))

# 616 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _56_18 -> (match (_56_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _56_587 -> begin
HeadMatch
end))

# 620 "FStar.TypeChecker.Rel.fst"
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

# 627 "FStar.TypeChecker.Rel.fst"
let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (
# 628 "FStar.TypeChecker.Rel.fst"
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

# 649 "FStar.TypeChecker.Rel.fst"
let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (
# 650 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Util.unmeta t1)
in (
# 651 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _56_673), FStar_Syntax_Syntax.Tm_uinst (g, _56_678)) -> begin
(let _135_458 = (head_matches env f g)
in (FStar_All.pipe_right _135_458 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _56_689), FStar_Syntax_Syntax.Tm_uvar (uv', _56_694)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_700), FStar_Syntax_Syntax.Tm_refine (y, _56_705)) -> begin
(let _135_459 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _135_459 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_711), _56_715) -> begin
(let _135_460 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _135_460 head_match))
end
| (_56_718, FStar_Syntax_Syntax.Tm_refine (x, _56_721)) -> begin
(let _135_461 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _135_461 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _56_741), FStar_Syntax_Syntax.Tm_app (head', _56_746)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _56_752), _56_756) -> begin
(head_matches env head t2)
end
| (_56_759, FStar_Syntax_Syntax.Tm_app (head, _56_762)) -> begin
(head_matches env t1 head)
end
| _56_767 -> begin
(let _135_464 = (let _135_463 = (delta_depth_of_term env t1)
in (let _135_462 = (delta_depth_of_term env t2)
in (_135_463, _135_462)))
in MisMatch (_135_464))
end))))

# 674 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 675 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 676 "FStar.TypeChecker.Rel.fst"
let fail = (fun r -> (r, None))
in (
# 677 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun n_delta t1 t2 -> (
# 678 "FStar.TypeChecker.Rel.fst"
let r = (head_matches env t1 t2)
in (match (r) with
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(
# 686 "FStar.TypeChecker.Rel.fst"
let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (
# 687 "FStar.TypeChecker.Rel.fst"
let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(
# 696 "FStar.TypeChecker.Rel.fst"
let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (
# 697 "FStar.TypeChecker.Rel.fst"
let _56_818 = if d1_greater_than_d2 then begin
(
# 698 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 700 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _135_485 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _135_485)))
end
in (match (_56_818) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_56_820) -> begin
(fail r)
end
| _56_823 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 709 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 710 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 711 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 710 "FStar.TypeChecker.Rel.fst"
let ___T____0 = (fun projectee -> (match (projectee) with
| T (_56_826) -> begin
_56_826
end))

# 711 "FStar.TypeChecker.Rel.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_56_829) -> begin
_56_829
end))

# 712 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 714 "FStar.TypeChecker.Rel.fst"
let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (
# 715 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 716 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_56_836) -> begin
false
end
| _56_839 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 721 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 722 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_56_849, imp), T (t)) -> begin
(t, imp)
end
| _56_856 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 727 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _56_861 -> (match (_56_861) with
| (t, _56_860) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 733 "FStar.TypeChecker.Rel.fst"
let fail = (fun _56_868 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 734 "FStar.TypeChecker.Rel.fst"
let _56_871 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_871) with
| (bs, c) -> begin
(
# 736 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 737 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 738 "FStar.TypeChecker.Rel.fst"
let _56_888 = x
in {FStar_Syntax_Syntax.ppname = _56_888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _56_896 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 743 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _56_19 -> (match (_56_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 746 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _135_567 = (decompose [] bs)
in (rebuild, matches, _135_567))))
end)))
end
| _56_906 -> begin
(
# 754 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _56_20 -> (match (_56_20) with
| [] -> begin
t
end
| _56_910 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 760 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _56_21 -> (match (_56_21) with
| T (t) -> begin
t
end
| _56_917 -> begin
(FStar_All.failwith "Impossible")
end))

# 764 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _56_22 -> (match (_56_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _56_922 -> begin
(FStar_All.failwith "Impossible")
end))

# 768 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 773 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 774 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 775 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_56_935, variance, T (ti)) -> begin
(
# 778 "FStar.TypeChecker.Rel.fst"
let k = (
# 779 "FStar.TypeChecker.Rel.fst"
let _56_943 = (FStar_Syntax_Util.type_u ())
in (match (_56_943) with
| (t, _56_942) -> begin
(let _135_589 = (new_uvar r scope t)
in (Prims.fst _135_589))
end))
in (
# 781 "FStar.TypeChecker.Rel.fst"
let _56_947 = (new_uvar r scope k)
in (match (_56_947) with
| (gi_xs, gi) -> begin
(
# 782 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _56_950 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _135_592 = (let _135_591 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _135_590 -> FStar_TypeChecker_Common.TProb (_135_590)) _135_591))
in (T (gi_xs), _135_592)))
end)))
end
| (_56_953, _56_955, C (_56_957)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 790 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 794 "FStar.TypeChecker.Rel.fst"
let _56_1035 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _56_975; FStar_Syntax_Syntax.pos = _56_973; FStar_Syntax_Syntax.vars = _56_971})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _135_601 = (let _135_600 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _135_599 -> C (_135_599)) _135_600))
in (_135_601, (prob)::[]))
end
| _56_986 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _56_994; FStar_Syntax_Syntax.pos = _56_992; FStar_Syntax_Syntax.vars = _56_990})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _135_604 = (let _135_603 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _135_602 -> C (_135_602)) _135_603))
in (_135_604, (prob)::[]))
end
| _56_1005 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_56_1007, _56_1009, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _56_1015; FStar_Syntax_Syntax.pos = _56_1013; FStar_Syntax_Syntax.vars = _56_1011})) -> begin
(
# 808 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 809 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 810 "FStar.TypeChecker.Rel.fst"
let _56_1026 = (let _135_606 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _135_606 FStar_List.unzip))
in (match (_56_1026) with
| (tcs, sub_probs) -> begin
(
# 811 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _135_611 = (let _135_610 = (let _135_607 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _135_607 un_T))
in (let _135_609 = (let _135_608 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _135_608 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _135_610; FStar_Syntax_Syntax.effect_args = _135_609; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _135_611))
in (C (gi_xs), sub_probs))
end))))
end
| _56_1029 -> begin
(
# 820 "FStar.TypeChecker.Rel.fst"
let _56_1032 = (sub_prob scope args q)
in (match (_56_1032) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_56_1035) with
| (tc, probs) -> begin
(
# 823 "FStar.TypeChecker.Rel.fst"
let _56_1048 = (match (q) with
| (Some (b), _56_1039, _56_1041) -> begin
(let _135_613 = (let _135_612 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_135_612)::args)
in (Some (b), (b)::scope, _135_613))
end
| _56_1044 -> begin
(None, scope, args)
end)
in (match (_56_1048) with
| (bopt, scope, args) -> begin
(
# 827 "FStar.TypeChecker.Rel.fst"
let _56_1052 = (aux scope args qs)
in (match (_56_1052) with
| (sub_probs, tcs, f) -> begin
(
# 828 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _135_616 = (let _135_615 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_135_615)
in (FStar_Syntax_Util.mk_conj_l _135_616))
end
| Some (b) -> begin
(let _135_620 = (let _135_619 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _135_618 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_135_619)::_135_618))
in (FStar_Syntax_Util.mk_conj_l _135_620))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 843 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 844 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 845 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _56_1080), FStar_Syntax_Syntax.Tm_uvar (u2, _56_1085)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _56_1099 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _56_1105 _56_1109 -> (match ((_56_1105, _56_1109)) with
| ((a1, _56_1104), (a2, _56_1108)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 862 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 863 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 865 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 866 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 867 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 868 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 869 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 870 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 871 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 872 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 873 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 873 "FStar.TypeChecker.Rel.fst"
let _56_1112 = p
in (let _135_642 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _135_641 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _56_1112.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _135_642; FStar_TypeChecker_Common.relation = _56_1112.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _135_641; FStar_TypeChecker_Common.element = _56_1112.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1112.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1112.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1112.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1112.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1112.FStar_TypeChecker_Common.rank}))))

# 875 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _135_648 = (compress_tprob wl p)
in (FStar_All.pipe_right _135_648 (fun _135_647 -> FStar_TypeChecker_Common.TProb (_135_647))))
end
| FStar_TypeChecker_Common.CProb (_56_1119) -> begin
p
end))

# 880 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 883 "FStar.TypeChecker.Rel.fst"
let prob = (let _135_653 = (compress_prob wl pr)
in (FStar_All.pipe_right _135_653 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 886 "FStar.TypeChecker.Rel.fst"
let _56_1129 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1129) with
| (lh, _56_1128) -> begin
(
# 887 "FStar.TypeChecker.Rel.fst"
let _56_1133 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1133) with
| (rh, _56_1132) -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let _56_1189 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_56_1135), FStar_Syntax_Syntax.Tm_uvar (_56_1138)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_56_1154), _56_1157) -> begin
(
# 895 "FStar.TypeChecker.Rel.fst"
let _56_1161 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1161) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _56_1164 -> begin
(
# 899 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _135_655 = (
# 903 "FStar.TypeChecker.Rel.fst"
let _56_1166 = tp
in (let _135_654 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _56_1166.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1166.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1166.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _135_654; FStar_TypeChecker_Common.element = _56_1166.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1166.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1166.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1166.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1166.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1166.FStar_TypeChecker_Common.rank}))
in (rank, _135_655)))
end)
end))
end
| (_56_1169, FStar_Syntax_Syntax.Tm_uvar (_56_1171)) -> begin
(
# 907 "FStar.TypeChecker.Rel.fst"
let _56_1176 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1176) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _56_1179 -> begin
(let _135_657 = (
# 910 "FStar.TypeChecker.Rel.fst"
let _56_1180 = tp
in (let _135_656 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _56_1180.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _135_656; FStar_TypeChecker_Common.relation = _56_1180.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1180.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1180.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1180.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1180.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1180.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1180.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1180.FStar_TypeChecker_Common.rank}))
in (refine_flex, _135_657))
end)
end))
end
| (_56_1183, _56_1185) -> begin
(rigid_rigid, tp)
end)
in (match (_56_1189) with
| (rank, tp) -> begin
(let _135_659 = (FStar_All.pipe_right (
# 915 "FStar.TypeChecker.Rel.fst"
let _56_1190 = tp
in {FStar_TypeChecker_Common.pid = _56_1190.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1190.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1190.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1190.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1190.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1190.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1190.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1190.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1190.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _135_658 -> FStar_TypeChecker_Common.TProb (_135_658)))
in (rank, _135_659))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _135_661 = (FStar_All.pipe_right (
# 917 "FStar.TypeChecker.Rel.fst"
let _56_1194 = cp
in {FStar_TypeChecker_Common.pid = _56_1194.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_1194.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_1194.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_1194.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_1194.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1194.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1194.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1194.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1194.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _135_660 -> FStar_TypeChecker_Common.CProb (_135_660)))
in (rigid_rigid, _135_661))
end)))

# 919 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 923 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _56_1201 probs -> (match (_56_1201) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 926 "FStar.TypeChecker.Rel.fst"
let _56_1209 = (rank wl hd)
in (match (_56_1209) with
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

# 939 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 940 "FStar.TypeChecker.Rel.fst"
let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

# 945 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 946 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 947 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 948 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 946 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_56_1220) -> begin
_56_1220
end))

# 947 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_56_1223) -> begin
_56_1223
end))

# 948 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_56_1226) -> begin
_56_1226
end))

# 950 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 951 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 952 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 953 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 956 "FStar.TypeChecker.Rel.fst"
let _56_1242 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_1242) with
| (k, _56_1241) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _56_1246 -> begin
false
end)
end)))))
end
| _56_1248 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 962 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(
# 966 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
| (u1::us1, u2::us2) -> begin
(match ((solve_universe_eq orig wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed -> begin
failed
end)
end
| _56_1273 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _135_741 = (let _135_740 = (FStar_Syntax_Print.univ_to_string u1)
in (let _135_739 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _135_740 _135_739)))
in UFailed (_135_741))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 979 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| u::us -> begin
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
| _56_1291 -> begin
(let _135_748 = (let _135_747 = (FStar_Syntax_Print.univ_to_string u1)
in (let _135_746 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _135_747 _135_746 msg)))
in UFailed (_135_748))
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
# 1011 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 1016 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _135_751 = (let _135_750 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _135_749 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _135_750 _135_749)))
in (try_umax_components u1 u2 _135_751))
end else begin
(let _135_752 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_135_752))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(
# 1026 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1027 "FStar.TypeChecker.Rel.fst"
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

# 1043 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1045 "FStar.TypeChecker.Rel.fst"
let _56_1388 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_798 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _135_798))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1049 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1049 "FStar.TypeChecker.Rel.fst"
let _56_1395 = probs
in {attempting = tl; wl_deferred = _56_1395.wl_deferred; ctr = _56_1395.ctr; defer_ok = _56_1395.defer_ok; smt_ok = _56_1395.smt_ok; tcenv = _56_1395.tcenv})
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
| (None, _56_1410, _56_1412) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _56_1416 -> begin
(
# 1076 "FStar.TypeChecker.Rel.fst"
let _56_1425 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _56_1422 -> (match (_56_1422) with
| (c, _56_1419, _56_1421) -> begin
(c < probs.ctr)
end))))
in (match (_56_1425) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _135_801 = (FStar_List.map (fun _56_1431 -> (match (_56_1431) with
| (_56_1428, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_135_801))
end
| _56_1433 -> begin
(let _135_804 = (
# 1082 "FStar.TypeChecker.Rel.fst"
let _56_1434 = probs
in (let _135_803 = (FStar_All.pipe_right attempt (FStar_List.map (fun _56_1441 -> (match (_56_1441) with
| (_56_1437, _56_1439, y) -> begin
y
end))))
in {attempting = _135_803; wl_deferred = rest; ctr = _56_1434.ctr; defer_ok = _56_1434.defer_ok; smt_ok = _56_1434.smt_ok; tcenv = _56_1434.tcenv}))
in (solve env _135_804))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _135_810 = (solve_prob orig None [] wl)
in (solve env _135_810))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1096 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
| ([], []) -> begin
USolved (wl)
end
| (u1::us1, u2::us2) -> begin
(match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end)
end
| _56_1476 -> begin
UFailed ("Unequal number of universes")
end))
in (
# 1109 "FStar.TypeChecker.Rel.fst"
let t1 = (whnf env t1)
in (
# 1110 "FStar.TypeChecker.Rel.fst"
let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _56_1484; FStar_Syntax_Syntax.pos = _56_1482; FStar_Syntax_Syntax.vars = _56_1480}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _56_1496; FStar_Syntax_Syntax.pos = _56_1494; FStar_Syntax_Syntax.vars = _56_1492}, us2)) -> begin
(
# 1113 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1114 "FStar.TypeChecker.Rel.fst"
let _56_1505 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _56_1520 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1127 "FStar.TypeChecker.Rel.fst"
let _56_1525 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_826 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _135_826 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1137 "FStar.TypeChecker.Rel.fst"
let _56_1530 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_830 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _135_830))
end else begin
()
end
in (
# 1139 "FStar.TypeChecker.Rel.fst"
let _56_1534 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1534) with
| (u, args) -> begin
(
# 1141 "FStar.TypeChecker.Rel.fst"
let disjoin = (fun t1 t2 -> (
# 1142 "FStar.TypeChecker.Rel.fst"
let _56_1540 = (head_matches_delta env () t1 t2)
in (match (_56_1540) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_56_1542) -> begin
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
# 1155 "FStar.TypeChecker.Rel.fst"
let _56_1558 = (match (ts) with
| Some (t1, t2) -> begin
(let _135_836 = (FStar_Syntax_Subst.compress t1)
in (let _135_835 = (FStar_Syntax_Subst.compress t2)
in (_135_836, _135_835)))
end
| None -> begin
(let _135_838 = (FStar_Syntax_Subst.compress t1)
in (let _135_837 = (FStar_Syntax_Subst.compress t2)
in (_135_838, _135_837)))
end)
in (match (_56_1558) with
| (t1, t2) -> begin
(
# 1158 "FStar.TypeChecker.Rel.fst"
let eq_prob = (fun t1 t2 -> (let _135_844 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _135_843 -> FStar_TypeChecker_Common.TProb (_135_843)) _135_844)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _135_851 = (let _135_850 = (let _135_847 = (let _135_846 = (let _135_845 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _135_845))
in FStar_Syntax_Syntax.Tm_refine (_135_846))
in (FStar_Syntax_Syntax.mk _135_847 None t1.FStar_Syntax_Syntax.pos))
in (let _135_849 = (let _135_848 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_135_848)::[])
in (_135_850, _135_849)))
in Some (_135_851))
end
| (_56_1572, FStar_Syntax_Syntax.Tm_refine (x, _56_1575)) -> begin
(let _135_854 = (let _135_853 = (let _135_852 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_135_852)::[])
in (t1, _135_853))
in Some (_135_854))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_1581), _56_1585) -> begin
(let _135_857 = (let _135_856 = (let _135_855 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_135_855)::[])
in (t2, _135_856))
in Some (_135_857))
end
| _56_1588 -> begin
None
end))
end))
end)
end)))
in (
# 1174 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _56_1592) -> begin
(
# 1178 "FStar.TypeChecker.Rel.fst"
let _56_1617 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _56_23 -> (match (_56_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(
# 1182 "FStar.TypeChecker.Rel.fst"
let _56_1603 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_56_1603) with
| (u', _56_1602) -> begin
(match ((let _135_859 = (whnf env u')
in _135_859.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _56_1606) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _56_1610 -> begin
false
end)
end))
end
| _56_1612 -> begin
false
end)
end
| _56_1614 -> begin
false
end))))
in (match (_56_1617) with
| (lower_bounds, rest) -> begin
(
# 1191 "FStar.TypeChecker.Rel.fst"
let rec make_lower_bound = (fun _56_1621 tps -> (match (_56_1621) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _135_864 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _135_864))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _56_1634 -> begin
None
end)
end))
in (match ((let _135_866 = (let _135_865 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_135_865, []))
in (make_lower_bound _135_866 lower_bounds))) with
| None -> begin
(
# 1202 "FStar.TypeChecker.Rel.fst"
let _56_1636 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(
# 1207 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (
# 1208 "FStar.TypeChecker.Rel.fst"
let _56_1646 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1209 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1209 "FStar.TypeChecker.Rel.fst"
let _56_1643 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _56_1643.wl_deferred; ctr = _56_1643.ctr; defer_ok = _56_1643.defer_ok; smt_ok = _56_1643.smt_ok; tcenv = _56_1643.tcenv})
in (let _135_867 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _135_867)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1211 "FStar.TypeChecker.Rel.fst"
let _56_1648 = wl
in {attempting = sub_probs; wl_deferred = _56_1648.wl_deferred; ctr = _56_1648.ctr; defer_ok = _56_1648.defer_ok; smt_ok = _56_1648.smt_ok; tcenv = _56_1648.tcenv}))) with
| Success (_56_1651) -> begin
(
# 1213 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1213 "FStar.TypeChecker.Rel.fst"
let _56_1653 = wl
in {attempting = rest; wl_deferred = _56_1653.wl_deferred; ctr = _56_1653.ctr; defer_ok = _56_1653.defer_ok; smt_ok = _56_1653.smt_ok; tcenv = _56_1653.tcenv})
in (
# 1214 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1215 "FStar.TypeChecker.Rel.fst"
let _56_1659 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _56_1662 -> begin
None
end)))
end))
end))
end
| _56_1664 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1226 "FStar.TypeChecker.Rel.fst"
let _56_1668 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_873 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _135_873))
end else begin
()
end
in (
# 1228 "FStar.TypeChecker.Rel.fst"
let _56_1672 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1672) with
| (u, args) -> begin
(
# 1229 "FStar.TypeChecker.Rel.fst"
let _56_1678 = (0, 1, 2, 3, 4)
in (match (_56_1678) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1230 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1232 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1233 "FStar.TypeChecker.Rel.fst"
let _56_1687 = (FStar_Syntax_Util.head_and_args t1)
in (match (_56_1687) with
| (h1, args1) -> begin
(
# 1234 "FStar.TypeChecker.Rel.fst"
let _56_1691 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_1691) with
| (h2, _56_1690) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _135_885 = (let _135_884 = (let _135_883 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _135_882 -> FStar_TypeChecker_Common.TProb (_135_882)) _135_883))
in (_135_884)::[])
in Some (_135_885))
end
end else begin
None
end
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
if (FStar_Syntax_Syntax.bv_eq a b) then begin
Some ([])
end else begin
None
end
end
| _56_1703 -> begin
None
end)
end))
end)))
in (
# 1250 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1252 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1256 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1257 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1258 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1259 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _135_892 = (let _135_891 = (let _135_890 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _135_890))
in (_135_891, m))
in Some (_135_892))))))
end))
end
| (_56_1725, FStar_Syntax_Syntax.Tm_refine (y, _56_1728)) -> begin
(
# 1264 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _56_1738), _56_1742) -> begin
(
# 1271 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _56_1749 -> begin
(
# 1278 "FStar.TypeChecker.Rel.fst"
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
# 1284 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _56_1757) -> begin
(
# 1288 "FStar.TypeChecker.Rel.fst"
let _56_1782 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _56_24 -> (match (_56_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1292 "FStar.TypeChecker.Rel.fst"
let _56_1768 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_56_1768) with
| (u', _56_1767) -> begin
(match ((let _135_894 = (whnf env u')
in _135_894.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _56_1771) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _56_1775 -> begin
false
end)
end))
end
| _56_1777 -> begin
false
end)
end
| _56_1779 -> begin
false
end))))
in (match (_56_1782) with
| (upper_bounds, rest) -> begin
(
# 1301 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _56_1786 tps -> (match (_56_1786) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _135_899 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _135_899))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _56_1799 -> begin
None
end)
end))
in (match ((let _135_901 = (let _135_900 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_135_900, []))
in (make_upper_bound _135_901 upper_bounds))) with
| None -> begin
(
# 1312 "FStar.TypeChecker.Rel.fst"
let _56_1801 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1325 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1326 "FStar.TypeChecker.Rel.fst"
let _56_1811 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1327 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1327 "FStar.TypeChecker.Rel.fst"
let _56_1808 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _56_1808.wl_deferred; ctr = _56_1808.ctr; defer_ok = _56_1808.defer_ok; smt_ok = _56_1808.smt_ok; tcenv = _56_1808.tcenv})
in (let _135_902 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _135_902)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1329 "FStar.TypeChecker.Rel.fst"
let _56_1813 = wl
in {attempting = sub_probs; wl_deferred = _56_1813.wl_deferred; ctr = _56_1813.ctr; defer_ok = _56_1813.defer_ok; smt_ok = _56_1813.smt_ok; tcenv = _56_1813.tcenv}))) with
| Success (_56_1816) -> begin
(
# 1331 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1331 "FStar.TypeChecker.Rel.fst"
let _56_1818 = wl
in {attempting = rest; wl_deferred = _56_1818.wl_deferred; ctr = _56_1818.ctr; defer_ok = _56_1818.defer_ok; smt_ok = _56_1818.smt_ok; tcenv = _56_1818.tcenv})
in (
# 1332 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1333 "FStar.TypeChecker.Rel.fst"
let _56_1824 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _56_1827 -> begin
None
end)))
end))
end))
end
| _56_1829 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1343 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1346 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1347 "FStar.TypeChecker.Rel.fst"
let _56_1846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_930 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _135_930))
end else begin
()
end
in (
# 1349 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1353 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1353 "FStar.TypeChecker.Rel.fst"
let _56_1860 = hd1
in (let _135_931 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_1860.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1860.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_931}))
in (
# 1354 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1354 "FStar.TypeChecker.Rel.fst"
let _56_1863 = hd2
in (let _135_932 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_1863.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1863.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_932}))
in (
# 1355 "FStar.TypeChecker.Rel.fst"
let prob = (let _135_935 = (let _135_934 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _135_934 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _135_933 -> FStar_TypeChecker_Common.TProb (_135_933)) _135_935))
in (
# 1356 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1357 "FStar.TypeChecker.Rel.fst"
let subst = (let _135_936 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_135_936)
in (
# 1358 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1361 "FStar.TypeChecker.Rel.fst"
let phi = (let _135_938 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _135_937 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _135_938 _135_937)))
in (
# 1362 "FStar.TypeChecker.Rel.fst"
let _56_1875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_940 = (FStar_Syntax_Print.term_to_string phi)
in (let _135_939 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _135_940 _135_939)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _56_1879 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1371 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1375 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _135_944 = (compress_tprob wl problem)
in (solve_t' env _135_944 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1382 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1385 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1386 "FStar.TypeChecker.Rel.fst"
let _56_1907 = (head_matches_delta env wl t1 t2)
in (match (_56_1907) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_56_1909), _56_1912) -> begin
(
# 1389 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _56_1925 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1395 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1398 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1402 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _135_973 = (let _135_972 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _135_972 t2))
in (FStar_Syntax_Util.mk_forall x _135_973)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _135_974 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _135_974)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_56_1935, Some (t1, t2)) -> begin
(solve_t env (
# 1411 "FStar.TypeChecker.Rel.fst"
let _56_1941 = problem
in {FStar_TypeChecker_Common.pid = _56_1941.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_1941.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_1941.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1941.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1941.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1941.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1941.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1941.FStar_TypeChecker_Common.rank}) wl)
end
| (_56_1944, None) -> begin
(
# 1414 "FStar.TypeChecker.Rel.fst"
let _56_1947 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_978 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_977 = (FStar_Syntax_Print.tag_of_term t1)
in (let _135_976 = (FStar_Syntax_Print.term_to_string t2)
in (let _135_975 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _135_978 _135_977 _135_976 _135_975)))))
end else begin
()
end
in (
# 1418 "FStar.TypeChecker.Rel.fst"
let _56_1951 = (FStar_Syntax_Util.head_and_args t1)
in (match (_56_1951) with
| (head1, args1) -> begin
(
# 1419 "FStar.TypeChecker.Rel.fst"
let _56_1954 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_1954) with
| (head2, args2) -> begin
(
# 1420 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _135_983 = (let _135_982 = (FStar_Syntax_Print.term_to_string head1)
in (let _135_981 = (args_to_string args1)
in (let _135_980 = (FStar_Syntax_Print.term_to_string head2)
in (let _135_979 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _135_982 _135_981 _135_980 _135_979)))))
in (giveup env _135_983 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _135_984 = (solve_prob orig None [] wl)
in (solve env _135_984))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1441 "FStar.TypeChecker.Rel.fst"
let _56_1964 = (base_and_refinement env wl t1)
in (match (_56_1964) with
| (base1, refinement1) -> begin
(
# 1442 "FStar.TypeChecker.Rel.fst"
let _56_1967 = (base_and_refinement env wl t2)
in (match (_56_1967) with
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
# 1449 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _56_1980 _56_1984 -> (match ((_56_1980, _56_1984)) with
| ((a, _56_1979), (a', _56_1983)) -> begin
(let _135_988 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _135_987 -> FStar_TypeChecker_Common.TProb (_135_987)) _135_988))
end)) args1 args2)
in (
# 1450 "FStar.TypeChecker.Rel.fst"
let formula = (let _135_990 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _135_990))
in (
# 1451 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _56_1990 -> begin
(
# 1456 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1457 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1458 "FStar.TypeChecker.Rel.fst"
let _56_1993 = problem
in {FStar_TypeChecker_Common.pid = _56_1993.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _56_1993.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _56_1993.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_1993.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_1993.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_1993.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_1993.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_1993.FStar_TypeChecker_Common.rank}) wl)))
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
# 1464 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1465 "FStar.TypeChecker.Rel.fst"
let _56_2012 = p
in (match (_56_2012) with
| (((u, k), xs, c), ps, (h, _56_2009, qs)) -> begin
(
# 1466 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1471 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1472 "FStar.TypeChecker.Rel.fst"
let _56_2018 = (imitation_sub_probs orig env xs ps qs)
in (match (_56_2018) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1473 "FStar.TypeChecker.Rel.fst"
let im = (let _135_1003 = (h gs_xs)
in (let _135_1002 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _135_1001 -> Some (_135_1001)))
in (FStar_Syntax_Util.abs xs _135_1003 _135_1002)))
in (
# 1474 "FStar.TypeChecker.Rel.fst"
let _56_2020 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1008 = (FStar_Syntax_Print.term_to_string im)
in (let _135_1007 = (FStar_Syntax_Print.tag_of_term im)
in (let _135_1006 = (let _135_1004 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _135_1004 (FStar_String.concat ", ")))
in (let _135_1005 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _135_1008 _135_1007 _135_1006 _135_1005)))))
end else begin
()
end
in (
# 1479 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1484 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1485 "FStar.TypeChecker.Rel.fst"
let _56_2038 = p
in (match (_56_2038) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(
# 1489 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1490 "FStar.TypeChecker.Rel.fst"
let _56_2043 = (FStar_List.nth ps i)
in (match (_56_2043) with
| (pi, _56_2042) -> begin
(
# 1491 "FStar.TypeChecker.Rel.fst"
let _56_2047 = (FStar_List.nth xs i)
in (match (_56_2047) with
| (xi, _56_2046) -> begin
(
# 1493 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1494 "FStar.TypeChecker.Rel.fst"
let _56_2052 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_2052) with
| (bs, k) -> begin
(
# 1495 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _56_2060)::tl -> begin
(
# 1498 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1499 "FStar.TypeChecker.Rel.fst"
let _56_2066 = (new_uvar r xs k_a)
in (match (_56_2066) with
| (gi_xs, gi) -> begin
(
# 1500 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1501 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1502 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1503 "FStar.TypeChecker.Rel.fst"
let _56_2072 = (aux subst tl)
in (match (_56_2072) with
| (gi_xs', gi_ps') -> begin
(let _135_1030 = (let _135_1027 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_135_1027)::gi_xs')
in (let _135_1029 = (let _135_1028 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_135_1028)::gi_ps')
in (_135_1030, _135_1029)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _135_1031 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _135_1031)) then begin
None
end else begin
(
# 1509 "FStar.TypeChecker.Rel.fst"
let _56_2076 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_56_2076) with
| (g_xs, _56_2075) -> begin
(
# 1510 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1511 "FStar.TypeChecker.Rel.fst"
let proj = (let _135_1034 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _135_1033 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _135_1032 -> Some (_135_1032)))
in (FStar_Syntax_Util.abs xs _135_1034 _135_1033)))
in (
# 1512 "FStar.TypeChecker.Rel.fst"
let sub = (let _135_1040 = (let _135_1039 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _135_1038 = (let _135_1037 = (FStar_List.map (fun _56_2084 -> (match (_56_2084) with
| (_56_2080, _56_2082, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _135_1037))
in (mk_problem (p_scope orig) orig _135_1039 (p_rel orig) _135_1038 None "projection")))
in (FStar_All.pipe_left (fun _135_1035 -> FStar_TypeChecker_Common.TProb (_135_1035)) _135_1040))
in (
# 1513 "FStar.TypeChecker.Rel.fst"
let _56_2086 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1042 = (FStar_Syntax_Print.term_to_string proj)
in (let _135_1041 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _135_1042 _135_1041)))
end else begin
()
end
in (
# 1514 "FStar.TypeChecker.Rel.fst"
let wl = (let _135_1044 = (let _135_1043 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_135_1043))
in (solve_prob orig _135_1044 ((TERM ((u, proj)))::[]) wl))
in (let _135_1046 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _135_1045 -> Some (_135_1045)) _135_1046)))))))
end))
end)
end))
end)))
end)))
in (
# 1519 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1520 "FStar.TypeChecker.Rel.fst"
let _56_2100 = lhs
in (match (_56_2100) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(
# 1521 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1522 "FStar.TypeChecker.Rel.fst"
let _56_2105 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_56_2105) with
| (xs, c) -> begin
(let _135_1061 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _135_1061))
end)))
in (
# 1525 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1528 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_56_2112) -> begin
(
# 1532 "FStar.TypeChecker.Rel.fst"
let _56_2114 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1539 "FStar.TypeChecker.Rel.fst"
let _56_2122 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1543 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1544 "FStar.TypeChecker.Rel.fst"
let _56_2132 = (FStar_Syntax_Util.head_and_args t2)
in (match (_56_2132) with
| (hd, _56_2131) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _56_2143 -> begin
(
# 1550 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1553 "FStar.TypeChecker.Rel.fst"
let _56_2145 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1072 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _135_1072))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1556 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1557 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _135_1076 = (let _135_1075 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _135_1075 Prims.fst))
in (FStar_All.pipe_right _135_1076 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1564 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1565 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1566 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1567 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1568 "FStar.TypeChecker.Rel.fst"
let _56_2158 = (occurs_check env wl (uv, k_uv) t2)
in (match (_56_2158) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _135_1078 = (let _135_1077 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _135_1077))
in (giveup_or_defer orig _135_1078))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _135_1079 = (subterms args_lhs)
in (imitate orig env wl _135_1079))
end else begin
(
# 1575 "FStar.TypeChecker.Rel.fst"
let _56_2159 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1082 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_1081 = (names_to_string fvs1)
in (let _135_1080 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _135_1082 _135_1081 _135_1080))))
end else begin
()
end
in (
# 1580 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _56_2163 -> begin
(let _135_1083 = (sn_binders env vars)
in (u_abs k_uv _135_1083 t2))
end)
in (
# 1583 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1588 "FStar.TypeChecker.Rel.fst"
let _56_2166 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1086 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_1085 = (names_to_string fvs1)
in (let _135_1084 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _135_1086 _135_1085 _135_1084))))
end else begin
()
end
in (let _135_1087 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _135_1087 (- (1)))))
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
if (let _135_1088 = (FStar_Syntax_Free.names t1)
in (check_head _135_1088 t2)) then begin
(
# 1600 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1601 "FStar.TypeChecker.Rel.fst"
let _56_2170 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1089 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _135_1089 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _135_1090 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _135_1090 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1626 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1629 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _56_2182 -> (match (_56_2182) with
| (t, u, k, args) -> begin
(
# 1632 "FStar.TypeChecker.Rel.fst"
let _56_2186 = (FStar_Syntax_Util.arrow_formals k)
in (match (_56_2186) with
| (all_formals, _56_2185) -> begin
(
# 1633 "FStar.TypeChecker.Rel.fst"
let _56_2187 = ()
in (
# 1635 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1643 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _56_2200 -> (match (_56_2200) with
| (x, imp) -> begin
(let _135_1112 = (FStar_Syntax_Syntax.bv_to_name x)
in (_135_1112, imp))
end))))
in (
# 1644 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1645 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1646 "FStar.TypeChecker.Rel.fst"
let _56_2206 = (FStar_Syntax_Util.type_u ())
in (match (_56_2206) with
| (t, _56_2205) -> begin
(let _135_1113 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _135_1113))
end))
in (
# 1648 "FStar.TypeChecker.Rel.fst"
let _56_2210 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_56_2210) with
| (t', tm_u1) -> begin
(
# 1649 "FStar.TypeChecker.Rel.fst"
let _56_2217 = (destruct_flex_t t')
in (match (_56_2217) with
| (_56_2212, u1, k1, _56_2216) -> begin
(
# 1650 "FStar.TypeChecker.Rel.fst"
let sol = (let _135_1115 = (let _135_1114 = (u_abs k all_formals t')
in ((u, k), _135_1114))
in TERM (_135_1115))
in (
# 1651 "FStar.TypeChecker.Rel.fst"
let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in (sol, (t_app, u1, k1, pat_args))))
end))
end)))))
end
| (formal::formals, hd::tl) -> begin
(match ((pat_var_opt env pat_args hd)) with
| None -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| Some (y) -> begin
(
# 1660 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _56_2236 -> (match (_56_2236) with
| (x, _56_2235) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1667 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _135_1117 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _135_1117 formals tl))
end)
end)
end)
end
| _56_2240 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _135_1118 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _135_1118 all_formals args))))
end))
end))
in (
# 1679 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _56_2246 _56_2250 r -> (match ((_56_2246, _56_2250)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _135_1127 = (solve_prob orig None [] wl)
in (solve env _135_1127))
end else begin
(
# 1687 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1688 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1689 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1690 "FStar.TypeChecker.Rel.fst"
let _56_2255 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1130 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _135_1129 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _135_1128 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _135_1130 _135_1129 _135_1128))))
end else begin
()
end
in (
# 1693 "FStar.TypeChecker.Rel.fst"
let _56_2268 = (
# 1694 "FStar.TypeChecker.Rel.fst"
let _56_2260 = (FStar_Syntax_Util.type_u ())
in (match (_56_2260) with
| (t, _56_2259) -> begin
(
# 1695 "FStar.TypeChecker.Rel.fst"
let _56_2264 = (new_uvar r zs t)
in (match (_56_2264) with
| (k, _56_2263) -> begin
(new_uvar r zs k)
end))
end))
in (match (_56_2268) with
| (u_zs, _56_2267) -> begin
(
# 1697 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs k1 xs u_zs)
in (
# 1698 "FStar.TypeChecker.Rel.fst"
let _56_2272 = (occurs_check env wl (u1, k1) sub1)
in (match (_56_2272) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1701 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1703 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1705 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs k2 ys u_zs)
in (
# 1706 "FStar.TypeChecker.Rel.fst"
let _56_2278 = (occurs_check env wl (u2, k2) sub2)
in (match (_56_2278) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1709 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1710 "FStar.TypeChecker.Rel.fst"
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
# 1713 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _56_2286 _56_2291 -> (match ((_56_2286, _56_2291)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1715 "FStar.TypeChecker.Rel.fst"
let _56_2292 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1136 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_1135 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _135_1136 _135_1135)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1718 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _56_2297 _56_2301 -> (match ((_56_2297, _56_2301)) with
| ((a, _56_2296), (t2, _56_2300)) -> begin
(let _135_1141 = (let _135_1139 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _135_1139 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _135_1141 (fun _135_1140 -> FStar_TypeChecker_Common.TProb (_135_1140))))
end)) xs args2)
in (
# 1721 "FStar.TypeChecker.Rel.fst"
let guard = (let _135_1143 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _135_1143))
in (
# 1722 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1725 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1726 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1727 "FStar.TypeChecker.Rel.fst"
let _56_2311 = (occurs_check env wl (u1, k1) t2)
in (match (_56_2311) with
| (occurs_ok, _56_2310) -> begin
(
# 1728 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1731 "FStar.TypeChecker.Rel.fst"
let sol = (let _135_1145 = (let _135_1144 = (u_abs k1 xs t2)
in ((u1, k1), _135_1144))
in TERM (_135_1145))
in (
# 1732 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1735 "FStar.TypeChecker.Rel.fst"
let _56_2322 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_56_2322) with
| (sol, (_56_2317, u2, k2, ys)) -> begin
(
# 1736 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1737 "FStar.TypeChecker.Rel.fst"
let _56_2324 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _135_1146 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _135_1146))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _56_2329 -> begin
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
# 1745 "FStar.TypeChecker.Rel.fst"
let _56_2334 = lhs
in (match (_56_2334) with
| (t1, u1, k1, args1) -> begin
(
# 1746 "FStar.TypeChecker.Rel.fst"
let _56_2339 = rhs
in (match (_56_2339) with
| (t2, u2, k2, args2) -> begin
(
# 1747 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1748 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1749 "FStar.TypeChecker.Rel.fst"
let r = t2.FStar_Syntax_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl (u1, k1, xs) (u2, k2, ys) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _56_2357 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1758 "FStar.TypeChecker.Rel.fst"
let _56_2361 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_56_2361) with
| (sol, _56_2360) -> begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1760 "FStar.TypeChecker.Rel.fst"
let _56_2363 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _135_1147 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _135_1147))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _56_2368 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1767 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _135_1148 = (solve_prob orig None [] wl)
in (solve env _135_1148))
end else begin
(
# 1769 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1770 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _135_1149 = (solve_prob orig None [] wl)
in (solve env _135_1149))
end else begin
(
# 1772 "FStar.TypeChecker.Rel.fst"
let _56_2372 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _135_1150 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _135_1150))
end else begin
()
end
in (
# 1775 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1777 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _56_2377 _56_2380 -> (match ((_56_2377, _56_2380)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1779 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1780 "FStar.TypeChecker.Rel.fst"
let _56_2387 = (FStar_Util.first_N n bs)
in (match (_56_2387) with
| (bs, rest) -> begin
(let _135_1180 = (mk_cod rest)
in (bs, _135_1180))
end)))
in (
# 1783 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1784 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _135_1184 = (let _135_1181 = (mk_cod1 [])
in (bs1, _135_1181))
in (let _135_1183 = (let _135_1182 = (mk_cod2 [])
in (bs2, _135_1182))
in (_135_1184, _135_1183)))
end else begin
if (l1 > l2) then begin
(let _135_1187 = (curry l2 bs1 mk_cod1)
in (let _135_1186 = (let _135_1185 = (mk_cod2 [])
in (bs2, _135_1185))
in (_135_1187, _135_1186)))
end else begin
(let _135_1190 = (let _135_1188 = (mk_cod1 [])
in (bs1, _135_1188))
in (let _135_1189 = (curry l1 bs2 mk_cod2)
in (_135_1190, _135_1189)))
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
# 1802 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _56_25 -> (match (_56_25) with
| [] -> begin
c
end
| bs -> begin
(let _135_1195 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _135_1195))
end))
in (
# 1806 "FStar.TypeChecker.Rel.fst"
let _56_2430 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_56_2430) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1811 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1812 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1813 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _135_1202 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _135_1201 -> FStar_TypeChecker_Common.CProb (_135_1201)) _135_1202)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _56_2440), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _56_2446)) -> begin
(
# 1817 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _56_26 -> (match (_56_26) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1820 "FStar.TypeChecker.Rel.fst"
let _56_2461 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_56_2461) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _135_1215 = (let _135_1214 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _135_1213 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _135_1214 problem.FStar_TypeChecker_Common.relation _135_1213 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _135_1212 -> FStar_TypeChecker_Common.TProb (_135_1212)) _135_1215))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_56_2466), FStar_Syntax_Syntax.Tm_refine (_56_2469)) -> begin
(
# 1829 "FStar.TypeChecker.Rel.fst"
let _56_2474 = (as_refinement env wl t1)
in (match (_56_2474) with
| (x1, phi1) -> begin
(
# 1830 "FStar.TypeChecker.Rel.fst"
let _56_2477 = (as_refinement env wl t2)
in (match (_56_2477) with
| (x2, phi2) -> begin
(
# 1831 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _135_1217 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _135_1216 -> FStar_TypeChecker_Common.TProb (_135_1216)) _135_1217))
in (
# 1832 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1833 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1834 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1835 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1836 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1837 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _135_1234 = (imp phi1 phi2)
in (FStar_All.pipe_right _135_1234 (guard_on_element problem x1))))
in (
# 1838 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _56_2489 -> (match (()) with
| () -> begin
(
# 1839 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1843 "FStar.TypeChecker.Rel.fst"
let guard = (let _135_1237 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _135_1237 impl))
in (
# 1844 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1847 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _135_1241 = (let _135_1240 = (let _135_1239 = (FStar_Syntax_Syntax.mk_binder x1)
in (_135_1239)::(p_scope orig))
in (mk_problem _135_1240 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _135_1238 -> FStar_TypeChecker_Common.TProb (_135_1238)) _135_1241))
in (match ((solve env (
# 1848 "FStar.TypeChecker.Rel.fst"
let _56_2494 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _56_2494.ctr; defer_ok = false; smt_ok = _56_2494.smt_ok; tcenv = _56_2494.tcenv}))) with
| Failed (_56_2497) -> begin
(fallback ())
end
| Success (_56_2500) -> begin
(
# 1851 "FStar.TypeChecker.Rel.fst"
let guard = (let _135_1244 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _135_1243 = (let _135_1242 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _135_1242 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _135_1244 _135_1243)))
in (
# 1852 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1853 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1853 "FStar.TypeChecker.Rel.fst"
let _56_2504 = wl
in {attempting = _56_2504.attempting; wl_deferred = _56_2504.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _56_2504.defer_ok; smt_ok = _56_2504.smt_ok; tcenv = _56_2504.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _135_1246 = (destruct_flex_t t1)
in (let _135_1245 = (destruct_flex_t t2)
in (flex_flex orig _135_1246 _135_1245)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _135_1247 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _135_1247 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1881 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _135_1248 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _135_1248)) then begin
(let _135_1251 = (FStar_All.pipe_left (fun _135_1249 -> FStar_TypeChecker_Common.TProb (_135_1249)) (
# 1883 "FStar.TypeChecker.Rel.fst"
let _56_2649 = problem
in {FStar_TypeChecker_Common.pid = _56_2649.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2649.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _56_2649.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2649.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2649.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2649.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2649.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2649.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2649.FStar_TypeChecker_Common.rank}))
in (let _135_1250 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _135_1251 _135_1250 t2 wl)))
end else begin
(
# 1884 "FStar.TypeChecker.Rel.fst"
let _56_2653 = (base_and_refinement env wl t2)
in (match (_56_2653) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _135_1254 = (FStar_All.pipe_left (fun _135_1252 -> FStar_TypeChecker_Common.TProb (_135_1252)) (
# 1887 "FStar.TypeChecker.Rel.fst"
let _56_2655 = problem
in {FStar_TypeChecker_Common.pid = _56_2655.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2655.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _56_2655.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2655.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2655.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2655.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2655.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2655.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2655.FStar_TypeChecker_Common.rank}))
in (let _135_1253 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _135_1254 _135_1253 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1890 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1890 "FStar.TypeChecker.Rel.fst"
let _56_2661 = y
in {FStar_Syntax_Syntax.ppname = _56_2661.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2661.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1891 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1892 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _135_1256 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _135_1255 -> FStar_TypeChecker_Common.TProb (_135_1255)) _135_1256))
in (
# 1894 "FStar.TypeChecker.Rel.fst"
let guard = (let _135_1257 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _135_1257 impl))
in (
# 1895 "FStar.TypeChecker.Rel.fst"
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
# 1904 "FStar.TypeChecker.Rel.fst"
let _56_2694 = (base_and_refinement env wl t1)
in (match (_56_2694) with
| (t_base, _56_2693) -> begin
(solve_t env (
# 1905 "FStar.TypeChecker.Rel.fst"
let _56_2695 = problem
in {FStar_TypeChecker_Common.pid = _56_2695.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _56_2695.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2695.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2695.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2695.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2695.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2695.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2695.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_56_2698), _56_2701) -> begin
(
# 1908 "FStar.TypeChecker.Rel.fst"
let t2 = (let _135_1258 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _135_1258))
in (solve_t env (
# 1909 "FStar.TypeChecker.Rel.fst"
let _56_2704 = problem
in {FStar_TypeChecker_Common.pid = _56_2704.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2704.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_2704.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_2704.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2704.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2704.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2704.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2704.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2704.FStar_TypeChecker_Common.rank}) wl))
end
| (_56_2707, FStar_Syntax_Syntax.Tm_refine (_56_2709)) -> begin
(
# 1912 "FStar.TypeChecker.Rel.fst"
let t1 = (let _135_1259 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _135_1259))
in (solve_t env (
# 1913 "FStar.TypeChecker.Rel.fst"
let _56_2713 = problem
in {FStar_TypeChecker_Common.pid = _56_2713.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_2713.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_2713.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2713.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2713.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2713.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2713.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2713.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2713.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1917 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_56_2730) -> begin
t
end
| _56_2733 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _135_1264 = (
# 1920 "FStar.TypeChecker.Rel.fst"
let _56_2734 = problem
in (let _135_1263 = (maybe_eta t1)
in (let _135_1262 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _56_2734.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _135_1263; FStar_TypeChecker_Common.relation = _56_2734.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _135_1262; FStar_TypeChecker_Common.element = _56_2734.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2734.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2734.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2734.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2734.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2734.FStar_TypeChecker_Common.rank})))
in (solve_t env _135_1264 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1934 "FStar.TypeChecker.Rel.fst"
let head1 = (let _135_1265 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _135_1265 Prims.fst))
in (
# 1935 "FStar.TypeChecker.Rel.fst"
let head2 = (let _135_1266 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _135_1266 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1940 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1941 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1943 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _135_1268 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _135_1267 -> Some (_135_1267)) _135_1268))
end
in (let _135_1269 = (solve_prob orig guard [] wl)
in (solve env _135_1269)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _56_2815, _56_2817), _56_2821) -> begin
(solve_t' env (
# 1951 "FStar.TypeChecker.Rel.fst"
let _56_2823 = problem
in {FStar_TypeChecker_Common.pid = _56_2823.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _56_2823.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_2823.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2823.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2823.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2823.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2823.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2823.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2823.FStar_TypeChecker_Common.rank}) wl)
end
| (_56_2826, FStar_Syntax_Syntax.Tm_ascribed (t2, _56_2829, _56_2831)) -> begin
(solve_t' env (
# 1954 "FStar.TypeChecker.Rel.fst"
let _56_2835 = problem
in {FStar_TypeChecker_Common.pid = _56_2835.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2835.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_2835.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _56_2835.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2835.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2835.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2835.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2835.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2835.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _135_1272 = (let _135_1271 = (FStar_Syntax_Print.tag_of_term t1)
in (let _135_1270 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _135_1271 _135_1270)))
in (FStar_All.failwith _135_1272))
end
| _56_2874 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1966 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1967 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1968 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1969 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1971 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1972 "FStar.TypeChecker.Rel.fst"
let _56_2891 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1974 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _56_2896 _56_2900 -> (match ((_56_2896, _56_2900)) with
| ((a1, _56_2895), (a2, _56_2899)) -> begin
(let _135_1287 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _135_1286 -> FStar_TypeChecker_Common.TProb (_135_1286)) _135_1287))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1977 "FStar.TypeChecker.Rel.fst"
let guard = (let _135_1289 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _135_1289))
in (
# 1978 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _135_1290 = (solve_prob orig None [] wl)
in (solve env _135_1290))
end else begin
(
# 1982 "FStar.TypeChecker.Rel.fst"
let _56_2905 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1292 = (FStar_Syntax_Print.comp_to_string c1)
in (let _135_1291 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _135_1292 (rel_to_string problem.FStar_TypeChecker_Common.relation) _135_1291)))
end else begin
()
end
in (
# 1987 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1988 "FStar.TypeChecker.Rel.fst"
let _56_2910 = (c1, c2)
in (match (_56_2910) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_56_2912), FStar_Syntax_Syntax.Total (_56_2915)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _135_1293 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _135_1293 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _135_1295 = (
# 2000 "FStar.TypeChecker.Rel.fst"
let _56_2943 = problem
in (let _135_1294 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _56_2943.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _135_1294; FStar_TypeChecker_Common.relation = _56_2943.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _56_2943.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _56_2943.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2943.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2943.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2943.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2943.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2943.FStar_TypeChecker_Common.rank}))
in (solve_c env _135_1295 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _135_1297 = (
# 2004 "FStar.TypeChecker.Rel.fst"
let _56_2959 = problem
in (let _135_1296 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _56_2959.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _56_2959.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _56_2959.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _135_1296; FStar_TypeChecker_Common.element = _56_2959.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _56_2959.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _56_2959.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _56_2959.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _56_2959.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _56_2959.FStar_TypeChecker_Common.rank}))
in (solve_c env _135_1297 wl))
end
| (FStar_Syntax_Syntax.Comp (_56_2962), FStar_Syntax_Syntax.Comp (_56_2965)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _135_1298 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _135_1298 wl))
end else begin
(
# 2010 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 2011 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2015 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 2016 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 2017 "FStar.TypeChecker.Rel.fst"
let _56_2972 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _135_1301 = (let _135_1300 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _135_1299 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _135_1300 _135_1299)))
in (giveup env _135_1301 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 2024 "FStar.TypeChecker.Rel.fst"
let _56_2990 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _56_2983)::(wlp1, _56_2979)::[] -> begin
(wp1, wlp1)
end
| _56_2987 -> begin
(let _135_1303 = (let _135_1302 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _135_1302))
in (FStar_All.failwith _135_1303))
end)
in (match (_56_2990) with
| (wp, wlp) -> begin
(
# 2027 "FStar.TypeChecker.Rel.fst"
let c1 = (let _135_1309 = (let _135_1308 = (let _135_1304 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _135_1304))
in (let _135_1307 = (let _135_1306 = (let _135_1305 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _135_1305))
in (_135_1306)::[])
in (_135_1308)::_135_1307))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _135_1309; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2034 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _56_27 -> (match (_56_27) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _56_2997 -> begin
false
end))))
in (
# 2035 "FStar.TypeChecker.Rel.fst"
let _56_3018 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _56_3003)::_56_3000, (wp2, _56_3010)::_56_3007) -> begin
(wp1, wp2)
end
| _56_3015 -> begin
(let _135_1313 = (let _135_1312 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _135_1311 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _135_1312 _135_1311)))
in (FStar_All.failwith _135_1313))
end)
in (match (_56_3018) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _135_1314 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _135_1314 wl))
end else begin
(
# 2042 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 2043 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2045 "FStar.TypeChecker.Rel.fst"
let _56_3020 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _135_1324 = (let _135_1323 = (let _135_1322 = (let _135_1316 = (let _135_1315 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_135_1315)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _135_1316 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _135_1321 = (let _135_1320 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _135_1319 = (let _135_1318 = (let _135_1317 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_1317))
in (_135_1318)::[])
in (_135_1320)::_135_1319))
in (_135_1322, _135_1321)))
in FStar_Syntax_Syntax.Tm_app (_135_1323))
in (FStar_Syntax_Syntax.mk _135_1324 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 2049 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _135_1340 = (let _135_1339 = (let _135_1338 = (let _135_1326 = (let _135_1325 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_135_1325)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _135_1326 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _135_1337 = (let _135_1336 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _135_1335 = (let _135_1334 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _135_1333 = (let _135_1332 = (let _135_1328 = (let _135_1327 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _135_1327 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_1328))
in (let _135_1331 = (let _135_1330 = (let _135_1329 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_1329))
in (_135_1330)::[])
in (_135_1332)::_135_1331))
in (_135_1334)::_135_1333))
in (_135_1336)::_135_1335))
in (_135_1338, _135_1337)))
in FStar_Syntax_Syntax.Tm_app (_135_1339))
in (FStar_Syntax_Syntax.mk _135_1340 None r))
in (let _135_1349 = (let _135_1348 = (let _135_1347 = (let _135_1342 = (let _135_1341 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_135_1341)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _135_1342 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _135_1346 = (let _135_1345 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _135_1344 = (let _135_1343 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_135_1343)::[])
in (_135_1345)::_135_1344))
in (_135_1347, _135_1346)))
in FStar_Syntax_Syntax.Tm_app (_135_1348))
in (FStar_Syntax_Syntax.mk _135_1349 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 2056 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _135_1351 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _135_1350 -> FStar_TypeChecker_Common.TProb (_135_1350)) _135_1351))
in (
# 2057 "FStar.TypeChecker.Rel.fst"
let wl = (let _135_1355 = (let _135_1354 = (let _135_1353 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _135_1353 g))
in (FStar_All.pipe_left (fun _135_1352 -> Some (_135_1352)) _135_1354))
in (solve_prob orig _135_1355 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end
end))))
end))
end
end)
end))))
end))))))

# 2064 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _135_1359 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _56_3038 -> (match (_56_3038) with
| (_56_3028, _56_3030, u, _56_3033, _56_3035, _56_3037) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _135_1359 (FStar_String.concat ", "))))

# 2066 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _56_3045 -> begin
(
# 2070 "FStar.TypeChecker.Rel.fst"
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
# 2077 "FStar.TypeChecker.Rel.fst"
let carry = (let _135_1365 = (FStar_List.map (fun _56_3053 -> (match (_56_3053) with
| (_56_3051, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _135_1365 (FStar_String.concat ",\n")))
in (
# 2078 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 2084 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 2086 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 2088 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _56_3062; FStar_TypeChecker_Env.implicits = _56_3060} -> begin
true
end
| _56_3067 -> begin
false
end))

# 2092 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 2094 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2098 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _56_3085 -> begin
(FStar_All.failwith "impossible")
end)
in (let _135_1384 = (
# 2101 "FStar.TypeChecker.Rel.fst"
let _56_3087 = g
in (let _135_1383 = (let _135_1382 = (let _135_1381 = (let _135_1377 = (FStar_Syntax_Syntax.mk_binder x)
in (_135_1377)::[])
in (let _135_1380 = (let _135_1379 = (let _135_1378 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _135_1378 FStar_Syntax_Util.lcomp_of_comp))
in Some (_135_1379))
in (FStar_Syntax_Util.abs _135_1381 f _135_1380)))
in (FStar_All.pipe_left (fun _135_1376 -> FStar_TypeChecker_Common.NonTrivial (_135_1376)) _135_1382))
in {FStar_TypeChecker_Env.guard_f = _135_1383; FStar_TypeChecker_Env.deferred = _56_3087.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3087.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3087.FStar_TypeChecker_Env.implicits}))
in Some (_135_1384)))
end))

# 2103 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2105 "FStar.TypeChecker.Rel.fst"
let _56_3094 = g
in (let _135_1395 = (let _135_1394 = (let _135_1393 = (let _135_1392 = (let _135_1391 = (let _135_1390 = (FStar_Syntax_Syntax.as_arg e)
in (_135_1390)::[])
in (f, _135_1391))
in FStar_Syntax_Syntax.Tm_app (_135_1392))
in (FStar_Syntax_Syntax.mk _135_1393 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _135_1389 -> FStar_TypeChecker_Common.NonTrivial (_135_1389)) _135_1394))
in {FStar_TypeChecker_Env.guard_f = _135_1395; FStar_TypeChecker_Env.deferred = _56_3094.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3094.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3094.FStar_TypeChecker_Env.implicits}))
end))

# 2107 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_56_3099) -> begin
(FStar_All.failwith "impossible")
end))

# 2111 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _135_1402 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_135_1402))
end))

# 2116 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _56_3117 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 2120 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2124 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2126 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _135_1425 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _135_1425; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2130 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2131 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2133 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2135 "FStar.TypeChecker.Rel.fst"
let _56_3144 = g
in (let _135_1440 = (let _135_1439 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _135_1439 (fun _135_1438 -> FStar_TypeChecker_Common.NonTrivial (_135_1438))))
in {FStar_TypeChecker_Env.guard_f = _135_1440; FStar_TypeChecker_Env.deferred = _56_3144.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3144.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3144.FStar_TypeChecker_Env.implicits}))
end))

# 2140 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2141 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _135_1448 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _135_1447 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _135_1448 (rel_to_string rel) _135_1447)))
end else begin
"TOP"
end
in (
# 2146 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2149 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2150 "FStar.TypeChecker.Rel.fst"
let x = (let _135_1459 = (let _135_1458 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _135_1457 -> Some (_135_1457)) _135_1458))
in (FStar_Syntax_Syntax.new_bv _135_1459 t1))
in (
# 2151 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2152 "FStar.TypeChecker.Rel.fst"
let p = (let _135_1463 = (let _135_1461 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _135_1460 -> Some (_135_1460)) _135_1461))
in (let _135_1462 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _135_1463 _135_1462)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2155 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2156 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2156 "FStar.TypeChecker.Rel.fst"
let _56_3164 = probs
in {attempting = _56_3164.attempting; wl_deferred = _56_3164.wl_deferred; ctr = _56_3164.ctr; defer_ok = false; smt_ok = _56_3164.smt_ok; tcenv = _56_3164.tcenv})
end else begin
probs
end
in (
# 2157 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2158 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2161 "FStar.TypeChecker.Rel.fst"
let _56_3171 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2164 "FStar.TypeChecker.Rel.fst"
let _56_3177 = (FStar_Unionfind.rollback tx)
in (
# 2165 "FStar.TypeChecker.Rel.fst"
let _56_3179 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _135_1475 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _135_1475))
end else begin
()
end
in (err (d, s))))
end)))))

# 2169 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2172 "FStar.TypeChecker.Rel.fst"
let _56_3186 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _135_1480 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _135_1480))
end else begin
()
end
in (
# 2173 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2174 "FStar.TypeChecker.Rel.fst"
let _56_3189 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _135_1481 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _135_1481))
end else begin
()
end
in (
# 2175 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _135_1482 = (FStar_Syntax_Util.unmeta f)
in _135_1482.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _56_3194 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2178 "FStar.TypeChecker.Rel.fst"
let _56_3196 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _56_3196.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3196.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3196.FStar_TypeChecker_Env.implicits})))))
end))

# 2180 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _135_1494 = (let _135_1493 = (let _135_1492 = (let _135_1491 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _135_1491 (fun _135_1490 -> FStar_TypeChecker_Common.NonTrivial (_135_1490))))
in {FStar_TypeChecker_Env.guard_f = _135_1492; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _135_1493))
in (FStar_All.pipe_left (fun _135_1489 -> Some (_135_1489)) _135_1494))
end))

# 2185 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2186 "FStar.TypeChecker.Rel.fst"
let _56_3207 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1502 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_1501 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _135_1502 _135_1501)))
end else begin
()
end
in (
# 2188 "FStar.TypeChecker.Rel.fst"
let prob = (let _135_1505 = (let _135_1504 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _135_1504))
in (FStar_All.pipe_left (fun _135_1503 -> FStar_TypeChecker_Common.TProb (_135_1503)) _135_1505))
in (
# 2189 "FStar.TypeChecker.Rel.fst"
let g = (let _135_1507 = (solve_and_commit env (singleton env prob) (fun _56_3210 -> None))
in (FStar_All.pipe_left (with_guard env prob) _135_1507))
in g))))

# 2192 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _135_1517 = (let _135_1516 = (let _135_1515 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _135_1514 = (FStar_TypeChecker_Env.get_range env)
in (_135_1515, _135_1514)))
in FStar_Syntax_Syntax.Error (_135_1516))
in (Prims.raise _135_1517))
end
| Some (g) -> begin
(
# 2196 "FStar.TypeChecker.Rel.fst"
let _56_3219 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1520 = (FStar_Syntax_Print.term_to_string t1)
in (let _135_1519 = (FStar_Syntax_Print.term_to_string t2)
in (let _135_1518 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _135_1520 _135_1519 _135_1518))))
end else begin
()
end
in g)
end))

# 2203 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2204 "FStar.TypeChecker.Rel.fst"
let _56_3224 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1528 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _135_1527 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _135_1528 _135_1527)))
end else begin
()
end
in (
# 2206 "FStar.TypeChecker.Rel.fst"
let _56_3228 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_56_3228) with
| (prob, x) -> begin
(
# 2207 "FStar.TypeChecker.Rel.fst"
let g = (let _135_1530 = (solve_and_commit env (singleton env prob) (fun _56_3229 -> None))
in (FStar_All.pipe_left (with_guard env prob) _135_1530))
in (
# 2208 "FStar.TypeChecker.Rel.fst"
let _56_3232 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _135_1534 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _135_1533 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _135_1532 = (let _135_1531 = (FStar_Util.must g)
in (guard_to_string env _135_1531))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _135_1534 _135_1533 _135_1532))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2216 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _135_1541 = (let _135_1540 = (let _135_1539 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _135_1538 = (FStar_TypeChecker_Env.get_range env)
in (_135_1539, _135_1538)))
in FStar_Syntax_Syntax.Error (_135_1540))
in (Prims.raise _135_1541)))

# 2220 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2221 "FStar.TypeChecker.Rel.fst"
let _56_3240 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1549 = (FStar_Syntax_Print.comp_to_string c1)
in (let _135_1548 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _135_1549 _135_1548)))
end else begin
()
end
in (
# 2223 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2224 "FStar.TypeChecker.Rel.fst"
let prob = (let _135_1552 = (let _135_1551 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _135_1551 "sub_comp"))
in (FStar_All.pipe_left (fun _135_1550 -> FStar_TypeChecker_Common.CProb (_135_1550)) _135_1552))
in (let _135_1554 = (solve_and_commit env (singleton env prob) (fun _56_3244 -> None))
in (FStar_All.pipe_left (with_guard env prob) _135_1554))))))

# 2228 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2229 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2230 "FStar.TypeChecker.Rel.fst"
let _56_3253 = (FStar_Unionfind.rollback tx)
in (
# 2231 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _135_1572 = (let _135_1571 = (let _135_1570 = (let _135_1568 = (FStar_Syntax_Print.univ_to_string u1)
in (let _135_1567 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _135_1568 _135_1567 msg)))
in (let _135_1569 = (FStar_TypeChecker_Env.get_range env)
in (_135_1570, _135_1569)))
in FStar_Syntax_Syntax.Error (_135_1571))
in (Prims.raise _135_1572)))))
in (
# 2240 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2243 "FStar.TypeChecker.Rel.fst"
let _56_3269 = hd
in (match (_56_3269) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _135_1579 = (insert uv u1 tl)
in (hd)::_135_1579)
end
end))
end))
in (
# 2248 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2251 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2254 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _135_1584 = (insert uv u1 out)
in (group_by _135_1584 rest))
end)
end
| _56_3284 -> begin
None
end))
end))
in (
# 2261 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _56_3286 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _56_3289 -> begin
(
# 2266 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2266 "FStar.TypeChecker.Rel.fst"
let _56_3290 = (empty_worklist env)
in {attempting = _56_3290.attempting; wl_deferred = _56_3290.wl_deferred; ctr = _56_3290.ctr; defer_ok = true; smt_ok = _56_3290.smt_ok; tcenv = _56_3290.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _56_3295 -> (match (_56_3295) with
| (u1, u2) -> begin
(
# 2268 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2269 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _56_3300 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2275 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _56_3310 -> begin
(u1)::[]
end)
in (
# 2278 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _56_3315 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _56_28 -> (match (_56_28) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2284 "FStar.TypeChecker.Rel.fst"
let _56_3322 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_3322) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2286 "FStar.TypeChecker.Rel.fst"
let _56_3326 = (FStar_Syntax_Util.univ_kernel u')
in (match (_56_3326) with
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
| USolved (_56_3328) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2296 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2296 "FStar.TypeChecker.Rel.fst"
let _56_3332 = (empty_worklist env)
in {attempting = _56_3332.attempting; wl_deferred = _56_3332.wl_deferred; ctr = _56_3332.ctr; defer_ok = false; smt_ok = _56_3332.smt_ok; tcenv = _56_3332.tcenv})
in (
# 2297 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _56_3347 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2309 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2310 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2311 "FStar.TypeChecker.Rel.fst"
let _56_3352 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2314 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2315 "FStar.TypeChecker.Rel.fst"
let fail = (fun _56_3359 -> (match (_56_3359) with
| (d, s) -> begin
(
# 2316 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2318 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2319 "FStar.TypeChecker.Rel.fst"
let _56_3362 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_1605 = (wl_to_string wl)
in (let _135_1604 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _135_1605 _135_1604)))
end else begin
()
end
in (
# 2321 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2322 "FStar.TypeChecker.Rel.fst"
let _56_3366 = g
in {FStar_TypeChecker_Env.guard_f = _56_3366.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _56_3366.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3366.FStar_TypeChecker_Env.implicits})
end
| _56_3369 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2324 "FStar.TypeChecker.Rel.fst"
let _56_3371 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2325 "FStar.TypeChecker.Rel.fst"
let _56_3373 = g
in {FStar_TypeChecker_Env.guard_f = _56_3373.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3373.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _56_3373.FStar_TypeChecker_Env.implicits})))))))

# 2327 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2328 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2329 "FStar.TypeChecker.Rel.fst"
let _56_3388 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2333 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2337 "FStar.TypeChecker.Rel.fst"
let _56_3386 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _135_1622 = (FStar_TypeChecker_Env.get_range env)
in (let _135_1621 = (let _135_1620 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _135_1620))
in (FStar_TypeChecker_Errors.diag _135_1622 _135_1621)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2342 "FStar.TypeChecker.Rel.fst"
let _56_3390 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_3390.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3390.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3390.FStar_TypeChecker_Env.implicits}))))

# 2344 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2346 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2347 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _56_3399 -> begin
false
end))
in (
# 2350 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _56_3403 implicits -> (match (_56_3403) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint ([], false) out)
end
end
| hd::tl -> begin
(
# 2354 "FStar.TypeChecker.Rel.fst"
let _56_3416 = hd
in (match (_56_3416) with
| (_56_3410, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2357 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2358 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2359 "FStar.TypeChecker.Rel.fst"
let _56_3419 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _135_1638 = (FStar_Syntax_Print.uvar_to_string u)
in (let _135_1637 = (FStar_Syntax_Print.term_to_string tm)
in (let _135_1636 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _135_1638 _135_1637 _135_1636))))
end else begin
()
end
in (
# 2362 "FStar.TypeChecker.Rel.fst"
let _56_3426 = (env.FStar_TypeChecker_Env.type_of (
# 2362 "FStar.TypeChecker.Rel.fst"
let _56_3421 = env
in {FStar_TypeChecker_Env.solver = _56_3421.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_3421.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_3421.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_3421.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_3421.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_3421.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _56_3421.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _56_3421.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_3421.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_3421.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_3421.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_3421.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_3421.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_3421.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_3421.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _56_3421.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _56_3421.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_3421.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _56_3421.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _56_3421.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_3421.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_56_3426) with
| (_56_3424, g) -> begin
(
# 2363 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2364 "FStar.TypeChecker.Rel.fst"
let _56_3427 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _56_3427.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3427.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _56_3427.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2366 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _56_3430 -> (match (()) with
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
# 2368 "FStar.TypeChecker.Rel.fst"
let _56_3432 = g
in (let _135_1642 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _56_3432.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3432.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _56_3432.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _135_1642})))))

# 2370 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2371 "FStar.TypeChecker.Rel.fst"
let g = (let _135_1647 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _135_1647 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _135_1648 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _135_1648))
end
| (reason, _56_3442, _56_3444, e, t, r)::_56_3439 -> begin
(let _135_1653 = (let _135_1652 = (let _135_1651 = (let _135_1650 = (FStar_Syntax_Print.term_to_string t)
in (let _135_1649 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _135_1650 _135_1649 reason)))
in (_135_1651, r))
in FStar_Syntax_Syntax.Error (_135_1652))
in (Prims.raise _135_1653))
end)))

# 2382 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2384 "FStar.TypeChecker.Rel.fst"
let _56_3452 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _56_3452.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _56_3452.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _56_3452.FStar_TypeChecker_Env.implicits}))





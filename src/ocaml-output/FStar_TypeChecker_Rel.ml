
open Prims
# 60 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _144_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _144_8 Prims.op_Negation)))))
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
| _55_40 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _144_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _144_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _144_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_144_10, uv)))))
end))))

# 76 "FStar.TypeChecker.Rel.fst"
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
| TERM (_55_46) -> begin
_55_46
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_49) -> begin
_55_49
end))

# 84 "FStar.TypeChecker.Rel.fst"
type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

# 87 "FStar.TypeChecker.Rel.fst"
let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

# 94 "FStar.TypeChecker.Rel.fst"
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
| Success (_55_59) -> begin
_55_59
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_62) -> begin
_55_62
end))

# 99 "FStar.TypeChecker.Rel.fst"
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

# 104 "FStar.TypeChecker.Rel.fst"
type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

# 106 "FStar.TypeChecker.Rel.fst"
type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

# 107 "FStar.TypeChecker.Rel.fst"
type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

# 108 "FStar.TypeChecker.Rel.fst"
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

# 120 "FStar.TypeChecker.Rel.fst"
let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

# 122 "FStar.TypeChecker.Rel.fst"
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_109 = (let _144_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _144_107 = (let _144_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _144_105 = (let _144_104 = (let _144_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _144_102 = (let _144_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _144_100 = (let _144_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _144_98 = (let _144_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_144_97)::[])
in (_144_99)::_144_98))
in (_144_101)::_144_100))
in (_144_103)::_144_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_144_104)
in (_144_106)::_144_105))
in (_144_108)::_144_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _144_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _144_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _144_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _144_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_110)))
end))

# 138 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _144_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _144_116 FStar_Util.string_of_int))
end
in (let _144_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _144_117)))
end
| TERM ((u, _55_86), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _144_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _144_118 FStar_Util.string_of_int))
end
in (let _144_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _144_119)))
end))

# 147 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _144_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _144_124 (FStar_String.concat ", "))))

# 148 "FStar.TypeChecker.Rel.fst"
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _144_128 = (let _144_127 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _144_127 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _144_128 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _144_131 = (FStar_All.pipe_right args (FStar_List.map (fun _55_99 -> (match (_55_99) with
| (x, _55_98) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _144_131 (FStar_String.concat " "))))

# 150 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 166 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _55_103 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_103.wl_deferred; ctr = _55_103.ctr; defer_ok = _55_103.defer_ok; smt_ok = _55_103.smt_ok; tcenv = _55_103.tcenv}))

# 167 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _55_107 = (empty_worklist env)
in (let _144_140 = (FStar_List.map Prims.snd g)
in {attempting = _144_140; wl_deferred = _55_107.wl_deferred; ctr = _55_107.ctr; defer_ok = false; smt_ok = _55_107.smt_ok; tcenv = _55_107.tcenv})))

# 168 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _55_112 = wl
in {attempting = _55_112.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _55_112.ctr; defer_ok = _55_112.defer_ok; smt_ok = _55_112.smt_ok; tcenv = _55_112.tcenv}))

# 169 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _55_116 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_116.wl_deferred; ctr = _55_116.ctr; defer_ok = _55_116.defer_ok; smt_ok = _55_116.smt_ok; tcenv = _55_116.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _55_121 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_157 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _144_157))
end else begin
()
end
in Failed ((prob, reason))))

# 175 "FStar.TypeChecker.Rel.fst"
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

# 186 "FStar.TypeChecker.Rel.fst"
let invert = (fun p -> (
# 187 "FStar.TypeChecker.Rel.fst"
let _55_128 = p
in {FStar_TypeChecker_Common.pid = _55_128.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_128.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_128.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_128.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_128.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_128.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_128.FStar_TypeChecker_Common.rank}))

# 187 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _144_164 -> FStar_TypeChecker_Common.TProb (_144_164)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _144_165 -> FStar_TypeChecker_Common.CProb (_144_165)))
end))

# 191 "FStar.TypeChecker.Rel.fst"
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

# 195 "FStar.TypeChecker.Rel.fst"
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _55_7 -> (match (_55_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 198 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _55_8 -> (match (_55_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 201 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _55_9 -> (match (_55_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 204 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _55_10 -> (match (_55_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 207 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _55_11 -> (match (_55_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 210 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _55_12 -> (match (_55_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 213 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_13 -> (match (_55_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _144_184 -> FStar_TypeChecker_Common.TProb (_144_184)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _144_185 -> FStar_TypeChecker_Common.CProb (_144_185)) (invert p))
end))

# 216 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 217 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _55_178 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _55_179 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 220 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _144_198 = (next_pid ())
in (let _144_197 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _144_198; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _144_197; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 233 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _144_208 = (next_pid ())
in (let _144_207 = (let _144_206 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _144_206 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _144_208; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _144_207; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 247 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _144_215 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _144_215; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 259 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 263 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _144_227 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _144_226 = (prob_to_string env d)
in (let _144_225 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _144_227 _144_226 _144_225 s)))))

# 269 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _55_14 -> (match (_55_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _55_220 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_223), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 284 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_232) -> begin
None
end
| TERM ((u, _55_236), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 288 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _55_16 -> (match (_55_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _55_249 -> begin
None
end))))

# 292 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _144_246 = (let _144_245 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _144_245))
in (FStar_Syntax_Subst.compress _144_246)))

# 302 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _144_251 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _144_251)))

# 303 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _144_254 = (sn env (Prims.fst t))
in (_144_254, (Prims.snd t))))

# 304 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_260 -> (match (_55_260) with
| (x, imp) -> begin
(let _144_261 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _55_261 = x
in (let _144_260 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_261.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_261.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_260}))
in (_144_261, imp))
end)))))

# 306 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _144_268 = (aux u)
in FStar_Syntax_Syntax.U_succ (_144_268))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _144_269 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_144_269))
end
| _55_273 -> begin
u
end)))
in (let _144_270 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _144_270))))

# 323 "FStar.TypeChecker.Rel.fst"
let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))

# 325 "FStar.TypeChecker.Rel.fst"
let base_and_refinement = (fun env wl t1 -> (
# 328 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_293; FStar_Syntax_Syntax.pos = _55_291; FStar_Syntax_Syntax.vars = _55_289} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _144_284 = (let _144_283 = (FStar_Syntax_Print.term_to_string tt)
in (let _144_282 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _144_283 _144_282)))
in (FStar_All.failwith _144_284))
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
in (match ((let _144_285 = (FStar_Syntax_Subst.compress t1')
in _144_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_311) -> begin
(aux true t1')
end
| _55_314 -> begin
(t1, None)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _144_288 = (let _144_287 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_286 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _144_287 _144_286)))
in (FStar_All.failwith _144_288))
end))
in (let _144_289 = (whnf env t1)
in (aux false _144_289))))

# 364 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _144_294 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _144_294 Prims.fst)))

# 366 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _144_297 = (FStar_Syntax_Syntax.null_bv t)
in (_144_297, FStar_Syntax_Util.t_true)))

# 368 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 371 "FStar.TypeChecker.Rel.fst"
let _55_360 = (base_and_refinement env wl t)
in (match (_55_360) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

# 374 "FStar.TypeChecker.Rel.fst"
let force_refinement = (fun _55_368 -> (match (_55_368) with
| (t_base, refopt) -> begin
(
# 377 "FStar.TypeChecker.Rel.fst"
let _55_376 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_376) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 380 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_310 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _144_309 = (let _144_306 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _144_306))
in (let _144_308 = (let _144_307 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _144_307))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _144_310 _144_309 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_308))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _144_313 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _144_312 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _144_311 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _144_313 _144_312 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_311))))
end))

# 403 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _144_319 = (let _144_318 = (let _144_317 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_389 -> (match (_55_389) with
| (_55_385, _55_387, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _144_317))
in (FStar_List.map (wl_prob_to_string wl) _144_318))
in (FStar_All.pipe_right _144_319 (FStar_String.concat "\n\t"))))

# 406 "FStar.TypeChecker.Rel.fst"
let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (
# 416 "FStar.TypeChecker.Rel.fst"
let _55_408 = (match ((let _144_326 = (FStar_Syntax_Subst.compress k)
in _144_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _144_327 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _144_327))
end else begin
(
# 420 "FStar.TypeChecker.Rel.fst"
let _55_399 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_399) with
| (ys', t) -> begin
(let _144_328 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _144_328))
end))
end
end
| _55_401 -> begin
(let _144_330 = (let _144_329 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _144_329))
in ((ys, t), _144_330))
end)
in (match (_55_408) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(
# 425 "FStar.TypeChecker.Rel.fst"
let c = (let _144_331 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _144_331 c))
in (let _144_335 = (let _144_334 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_332 -> FStar_Util.Inl (_144_332)))
in (FStar_All.pipe_right _144_334 (fun _144_333 -> Some (_144_333))))
in (FStar_Syntax_Util.abs ys t _144_335)))
end
end)))

# 426 "FStar.TypeChecker.Rel.fst"
let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (
# 429 "FStar.TypeChecker.Rel.fst"
let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (
# 432 "FStar.TypeChecker.Rel.fst"
let _55_422 = (p_guard prob)
in (match (_55_422) with
| (_55_420, uv) -> begin
(
# 433 "FStar.TypeChecker.Rel.fst"
let _55_435 = (match ((let _144_346 = (FStar_Syntax_Subst.compress uv)
in _144_346.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 435 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 436 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _144_348 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _144_348 Prims.op_Negation)))))
in (
# 437 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs k bs phi)
in (
# 438 "FStar.TypeChecker.Rel.fst"
let _55_431 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _144_351 = (FStar_Util.string_of_int (p_pid prob))
in (let _144_350 = (FStar_Syntax_Print.term_to_string uv)
in (let _144_349 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _144_351 _144_350 _144_349))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _55_434 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 445 "FStar.TypeChecker.Rel.fst"
let _55_437 = (commit uvis)
in (
# 446 "FStar.TypeChecker.Rel.fst"
let _55_439 = wl
in {attempting = _55_439.attempting; wl_deferred = _55_439.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_439.defer_ok; smt_ok = _55_439.smt_ok; tcenv = _55_439.tcenv})))
end))))

# 446 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 449 "FStar.TypeChecker.Rel.fst"
let _55_444 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_360 = (FStar_Util.string_of_int pid)
in (let _144_359 = (let _144_358 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _144_358 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _144_360 _144_359)))
end else begin
()
end
in (
# 451 "FStar.TypeChecker.Rel.fst"
let _55_446 = (commit sol)
in (
# 452 "FStar.TypeChecker.Rel.fst"
let _55_448 = wl
in {attempting = _55_448.attempting; wl_deferred = _55_448.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_448.defer_ok; smt_ok = _55_448.smt_ok; tcenv = _55_448.tcenv}))))

# 452 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 455 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_55_458, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _144_373 = (FStar_Syntax_Util.mk_conj t f)
in Some (_144_373))
end))
in (
# 459 "FStar.TypeChecker.Rel.fst"
let _55_470 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_376 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _144_375 = (let _144_374 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _144_374 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _144_376 _144_375)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 461 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _144_386 = (let _144_384 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _144_384 FStar_Util.set_elements))
in (FStar_All.pipe_right _144_386 (FStar_Util.for_some (fun _55_479 -> (match (_55_479) with
| (uv, _55_478) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 475 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 478 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 479 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _144_393 = (let _144_392 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _144_391 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _144_392 _144_391)))
in Some (_144_393))
end
in (occurs_ok, msg))))

# 484 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 487 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 488 "FStar.TypeChecker.Rel.fst"
let _55_494 = (occurs_check env wl uk t)
in (match (_55_494) with
| (occurs_ok, msg) -> begin
(let _144_399 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _144_399, (msg, fvs, fvs_t)))
end))))

# 489 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 492 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 494 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 495 "FStar.TypeChecker.Rel.fst"
let _55_512 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_504 _55_507 -> (match ((_55_504, _55_507)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _144_408 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _144_408)) then begin
(isect, isect_set)
end else begin
(
# 501 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _144_409 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _144_409))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_55_512) with
| (isect, _55_511) -> begin
(FStar_List.rev isect)
end)))))

# 506 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_518 _55_522 -> (match ((_55_518, _55_522)) with
| ((a, _55_517), (b, _55_521)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 510 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 513 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_532 -> (match (_55_532) with
| (b, _55_531) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _55_534 -> begin
None
end)))

# 520 "FStar.TypeChecker.Rel.fst"
let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 526 "FStar.TypeChecker.Rel.fst"
let _55_543 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_424 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _144_424))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 528 "FStar.TypeChecker.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_557; FStar_Syntax_Syntax.pos = _55_555; FStar_Syntax_Syntax.vars = _55_553}, args) -> begin
(t, uv, k, args)
end
| _55_567 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 533 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 536 "FStar.TypeChecker.Rel.fst"
let _55_574 = (destruct_flex_t t)
in (match (_55_574) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _55_578 -> begin
((t, uv, k, args), None)
end)
end)))

# 539 "FStar.TypeChecker.Rel.fst"
type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch

# 611 "FStar.TypeChecker.Rel.fst"
let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 612 "FStar.TypeChecker.Rel.fst"
let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 613 "FStar.TypeChecker.Rel.fst"
let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 611 "FStar.TypeChecker.Rel.fst"
let ___MisMatch____0 = (fun projectee -> (match (projectee) with
| MisMatch (_55_581) -> begin
_55_581
end))

# 613 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _55_588 -> begin
HeadMatch
end))

# 617 "FStar.TypeChecker.Rel.fst"
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

# 624 "FStar.TypeChecker.Rel.fst"
let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (
# 627 "FStar.TypeChecker.Rel.fst"
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

# 645 "FStar.TypeChecker.Rel.fst"
let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (
# 649 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Util.unmeta t1)
in (
# 650 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_674), FStar_Syntax_Syntax.Tm_uinst (g, _55_679)) -> begin
(let _144_460 = (head_matches env f g)
in (FStar_All.pipe_right _144_460 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_690), FStar_Syntax_Syntax.Tm_uvar (uv', _55_695)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_701), FStar_Syntax_Syntax.Tm_refine (y, _55_706)) -> begin
(let _144_461 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _144_461 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_712), _55_716) -> begin
(let _144_462 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _144_462 head_match))
end
| (_55_719, FStar_Syntax_Syntax.Tm_refine (x, _55_722)) -> begin
(let _144_463 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _144_463 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_742), FStar_Syntax_Syntax.Tm_app (head', _55_747)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_753), _55_757) -> begin
(head_matches env head t2)
end
| (_55_760, FStar_Syntax_Syntax.Tm_app (head, _55_763)) -> begin
(head_matches env t1 head)
end
| _55_768 -> begin
(let _144_466 = (let _144_465 = (delta_depth_of_term env t1)
in (let _144_464 = (delta_depth_of_term env t2)
in (_144_465, _144_464)))
in MisMatch (_144_466))
end))))

# 670 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 674 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 675 "FStar.TypeChecker.Rel.fst"
let fail = (fun r -> (r, None))
in (
# 676 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun n_delta t1 t2 -> (
# 677 "FStar.TypeChecker.Rel.fst"
let r = (head_matches env t1 t2)
in (match (r) with
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(
# 685 "FStar.TypeChecker.Rel.fst"
let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (
# 686 "FStar.TypeChecker.Rel.fst"
let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(
# 695 "FStar.TypeChecker.Rel.fst"
let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (
# 696 "FStar.TypeChecker.Rel.fst"
let _55_819 = if d1_greater_than_d2 then begin
(
# 697 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 699 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _144_487 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _144_487)))
end
in (match (_55_819) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_55_821) -> begin
(fail r)
end
| _55_824 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 706 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 709 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 710 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 709 "FStar.TypeChecker.Rel.fst"
let ___T____0 = (fun projectee -> (match (projectee) with
| T (_55_827) -> begin
_55_827
end))

# 710 "FStar.TypeChecker.Rel.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_830) -> begin
_55_830
end))

# 710 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 711 "FStar.TypeChecker.Rel.fst"
let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (
# 714 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 715 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_837) -> begin
false
end
| _55_840 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 720 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 721 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_55_850, imp), T (t)) -> begin
(t, imp)
end
| _55_857 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 726 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_862 -> (match (_55_862) with
| (t, _55_861) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 732 "FStar.TypeChecker.Rel.fst"
let fail = (fun _55_869 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 733 "FStar.TypeChecker.Rel.fst"
let _55_872 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_872) with
| (bs, c) -> begin
(
# 735 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 736 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 737 "FStar.TypeChecker.Rel.fst"
let _55_889 = x
in {FStar_Syntax_Syntax.ppname = _55_889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_897 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 742 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 745 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _144_569 = (decompose [] bs)
in (rebuild, matches, _144_569))))
end)))
end
| _55_907 -> begin
(
# 753 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_911 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 757 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t) -> begin
t
end
| _55_918 -> begin
(FStar_All.failwith "Impossible")
end))

# 761 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_923 -> begin
(FStar_All.failwith "Impossible")
end))

# 765 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 772 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 773 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 774 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_55_936, variance, T (ti)) -> begin
(
# 777 "FStar.TypeChecker.Rel.fst"
let k = (
# 778 "FStar.TypeChecker.Rel.fst"
let _55_944 = (FStar_Syntax_Util.type_u ())
in (match (_55_944) with
| (t, _55_943) -> begin
(let _144_591 = (new_uvar r scope t)
in (Prims.fst _144_591))
end))
in (
# 780 "FStar.TypeChecker.Rel.fst"
let _55_948 = (new_uvar r scope k)
in (match (_55_948) with
| (gi_xs, gi) -> begin
(
# 781 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_951 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _144_594 = (let _144_593 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _144_592 -> FStar_TypeChecker_Common.TProb (_144_592)) _144_593))
in (T (gi_xs), _144_594)))
end)))
end
| (_55_954, _55_956, C (_55_958)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 789 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 793 "FStar.TypeChecker.Rel.fst"
let _55_1036 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _55_976; FStar_Syntax_Syntax.pos = _55_974; FStar_Syntax_Syntax.vars = _55_972})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _144_603 = (let _144_602 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _144_601 -> C (_144_601)) _144_602))
in (_144_603, (prob)::[]))
end
| _55_987 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _55_995; FStar_Syntax_Syntax.pos = _55_993; FStar_Syntax_Syntax.vars = _55_991})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _144_606 = (let _144_605 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _144_604 -> C (_144_604)) _144_605))
in (_144_606, (prob)::[]))
end
| _55_1006 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1008, _55_1010, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1016; FStar_Syntax_Syntax.pos = _55_1014; FStar_Syntax_Syntax.vars = _55_1012})) -> begin
(
# 807 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 808 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 809 "FStar.TypeChecker.Rel.fst"
let _55_1027 = (let _144_608 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _144_608 FStar_List.unzip))
in (match (_55_1027) with
| (tcs, sub_probs) -> begin
(
# 810 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _144_613 = (let _144_612 = (let _144_609 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _144_609 un_T))
in (let _144_611 = (let _144_610 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _144_610 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _144_612; FStar_Syntax_Syntax.effect_args = _144_611; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _144_613))
in (C (gi_xs), sub_probs))
end))))
end
| _55_1030 -> begin
(
# 819 "FStar.TypeChecker.Rel.fst"
let _55_1033 = (sub_prob scope args q)
in (match (_55_1033) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_55_1036) with
| (tc, probs) -> begin
(
# 822 "FStar.TypeChecker.Rel.fst"
let _55_1049 = (match (q) with
| (Some (b), _55_1040, _55_1042) -> begin
(let _144_615 = (let _144_614 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_144_614)::args)
in (Some (b), (b)::scope, _144_615))
end
| _55_1045 -> begin
(None, scope, args)
end)
in (match (_55_1049) with
| (bopt, scope, args) -> begin
(
# 826 "FStar.TypeChecker.Rel.fst"
let _55_1053 = (aux scope args qs)
in (match (_55_1053) with
| (sub_probs, tcs, f) -> begin
(
# 827 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _144_618 = (let _144_617 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_144_617)
in (FStar_Syntax_Util.mk_conj_l _144_618))
end
| Some (b) -> begin
(let _144_622 = (let _144_621 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _144_620 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_144_621)::_144_620))
in (FStar_Syntax_Util.mk_conj_l _144_622))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 833 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 843 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 844 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1081), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1086)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1100 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1106 _55_1110 -> (match ((_55_1106, _55_1110)) with
| ((a1, _55_1105), (a2, _55_1109)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 856 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 861 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 864 "FStar.TypeChecker.Rel.fst"
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
# 874 "FStar.TypeChecker.Rel.fst"
let _55_1113 = p
in (let _144_644 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _144_643 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1113.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_644; FStar_TypeChecker_Common.relation = _55_1113.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_643; FStar_TypeChecker_Common.element = _55_1113.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1113.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1113.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1113.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1113.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1113.FStar_TypeChecker_Common.rank}))))

# 874 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_650 = (compress_tprob wl p)
in (FStar_All.pipe_right _144_650 (fun _144_649 -> FStar_TypeChecker_Common.TProb (_144_649))))
end
| FStar_TypeChecker_Common.CProb (_55_1120) -> begin
p
end))

# 878 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 884 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_655 = (compress_prob wl pr)
in (FStar_All.pipe_right _144_655 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 887 "FStar.TypeChecker.Rel.fst"
let _55_1130 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1130) with
| (lh, _55_1129) -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let _55_1134 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1134) with
| (rh, _55_1133) -> begin
(
# 889 "FStar.TypeChecker.Rel.fst"
let _55_1190 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1136), FStar_Syntax_Syntax.Tm_uvar (_55_1139)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1155), _55_1158) -> begin
(
# 896 "FStar.TypeChecker.Rel.fst"
let _55_1162 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1162) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _55_1165 -> begin
(
# 900 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _144_657 = (
# 904 "FStar.TypeChecker.Rel.fst"
let _55_1167 = tp
in (let _144_656 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1167.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1167.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1167.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_656; FStar_TypeChecker_Common.element = _55_1167.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1167.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1167.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1167.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1167.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1167.FStar_TypeChecker_Common.rank}))
in (rank, _144_657)))
end)
end))
end
| (_55_1170, FStar_Syntax_Syntax.Tm_uvar (_55_1172)) -> begin
(
# 908 "FStar.TypeChecker.Rel.fst"
let _55_1177 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1177) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _55_1180 -> begin
(let _144_659 = (
# 911 "FStar.TypeChecker.Rel.fst"
let _55_1181 = tp
in (let _144_658 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1181.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_658; FStar_TypeChecker_Common.relation = _55_1181.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1181.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1181.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1181.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1181.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1181.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1181.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1181.FStar_TypeChecker_Common.rank}))
in (refine_flex, _144_659))
end)
end))
end
| (_55_1184, _55_1186) -> begin
(rigid_rigid, tp)
end)
in (match (_55_1190) with
| (rank, tp) -> begin
(let _144_661 = (FStar_All.pipe_right (
# 916 "FStar.TypeChecker.Rel.fst"
let _55_1191 = tp
in {FStar_TypeChecker_Common.pid = _55_1191.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1191.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1191.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1191.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1191.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1191.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1191.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1191.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1191.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _144_660 -> FStar_TypeChecker_Common.TProb (_144_660)))
in (rank, _144_661))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _144_663 = (FStar_All.pipe_right (
# 918 "FStar.TypeChecker.Rel.fst"
let _55_1195 = cp
in {FStar_TypeChecker_Common.pid = _55_1195.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1195.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1195.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1195.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1195.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1195.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1195.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1195.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1195.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _144_662 -> FStar_TypeChecker_Common.CProb (_144_662)))
in (rigid_rigid, _144_663))
end)))

# 918 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 924 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _55_1202 probs -> (match (_55_1202) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 927 "FStar.TypeChecker.Rel.fst"
let _55_1210 = (rank wl hd)
in (match (_55_1210) with
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

# 938 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 940 "FStar.TypeChecker.Rel.fst"
let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

# 941 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 947 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 948 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 949 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 947 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_55_1221) -> begin
_55_1221
end))

# 948 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1224) -> begin
_55_1224
end))

# 949 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1227) -> begin
_55_1227
end))

# 949 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 952 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 953 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 954 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 957 "FStar.TypeChecker.Rel.fst"
let _55_1243 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1243) with
| (k, _55_1242) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1247 -> begin
false
end)
end)))))
end
| _55_1249 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 963 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(
# 967 "FStar.TypeChecker.Rel.fst"
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
| _55_1274 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _144_743 = (let _144_742 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_741 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _144_742 _144_741)))
in UFailed (_144_743))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 980 "FStar.TypeChecker.Rel.fst"
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
| _55_1292 -> begin
(let _144_750 = (let _144_749 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_748 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _144_749 _144_748 msg)))
in UFailed (_144_750))
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
# 1012 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 1017 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _144_753 = (let _144_752 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _144_751 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _144_752 _144_751)))
in (try_umax_components u1 u2 _144_753))
end else begin
(let _144_754 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_144_754))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(
# 1027 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1028 "FStar.TypeChecker.Rel.fst"
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

# 1039 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1046 "FStar.TypeChecker.Rel.fst"
let _55_1389 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_800 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _144_800))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1050 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1050 "FStar.TypeChecker.Rel.fst"
let _55_1396 = probs
in {attempting = tl; wl_deferred = _55_1396.wl_deferred; ctr = _55_1396.ctr; defer_ok = _55_1396.defer_ok; smt_ok = _55_1396.smt_ok; tcenv = _55_1396.tcenv})
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
| (None, _55_1411, _55_1413) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1417 -> begin
(
# 1077 "FStar.TypeChecker.Rel.fst"
let _55_1426 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1423 -> (match (_55_1423) with
| (c, _55_1420, _55_1422) -> begin
(c < probs.ctr)
end))))
in (match (_55_1426) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _144_803 = (FStar_List.map (fun _55_1432 -> (match (_55_1432) with
| (_55_1429, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_144_803))
end
| _55_1434 -> begin
(let _144_806 = (
# 1083 "FStar.TypeChecker.Rel.fst"
let _55_1435 = probs
in (let _144_805 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1442 -> (match (_55_1442) with
| (_55_1438, _55_1440, y) -> begin
y
end))))
in {attempting = _144_805; wl_deferred = rest; ctr = _55_1435.ctr; defer_ok = _55_1435.defer_ok; smt_ok = _55_1435.smt_ok; tcenv = _55_1435.tcenv}))
in (solve env _144_806))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _144_812 = (solve_prob orig None [] wl)
in (solve env _144_812))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1097 "FStar.TypeChecker.Rel.fst"
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
| _55_1477 -> begin
UFailed ("Unequal number of universes")
end))
in (
# 1110 "FStar.TypeChecker.Rel.fst"
let t1 = (whnf env t1)
in (
# 1111 "FStar.TypeChecker.Rel.fst"
let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1485; FStar_Syntax_Syntax.pos = _55_1483; FStar_Syntax_Syntax.vars = _55_1481}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1497; FStar_Syntax_Syntax.pos = _55_1495; FStar_Syntax_Syntax.vars = _55_1493}, us2)) -> begin
(
# 1114 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1115 "FStar.TypeChecker.Rel.fst"
let _55_1506 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1521 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1128 "FStar.TypeChecker.Rel.fst"
let _55_1526 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_828 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _144_828 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1138 "FStar.TypeChecker.Rel.fst"
let _55_1531 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_832 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _144_832))
end else begin
()
end
in (
# 1140 "FStar.TypeChecker.Rel.fst"
let _55_1535 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1535) with
| (u, args) -> begin
(
# 1142 "FStar.TypeChecker.Rel.fst"
let disjoin = (fun t1 t2 -> (
# 1143 "FStar.TypeChecker.Rel.fst"
let _55_1541 = (head_matches_delta env () t1 t2)
in (match (_55_1541) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1543) -> begin
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
# 1156 "FStar.TypeChecker.Rel.fst"
let _55_1559 = (match (ts) with
| Some (t1, t2) -> begin
(let _144_838 = (FStar_Syntax_Subst.compress t1)
in (let _144_837 = (FStar_Syntax_Subst.compress t2)
in (_144_838, _144_837)))
end
| None -> begin
(let _144_840 = (FStar_Syntax_Subst.compress t1)
in (let _144_839 = (FStar_Syntax_Subst.compress t2)
in (_144_840, _144_839)))
end)
in (match (_55_1559) with
| (t1, t2) -> begin
(
# 1159 "FStar.TypeChecker.Rel.fst"
let eq_prob = (fun t1 t2 -> (let _144_846 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _144_845 -> FStar_TypeChecker_Common.TProb (_144_845)) _144_846)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _144_853 = (let _144_852 = (let _144_849 = (let _144_848 = (let _144_847 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _144_847))
in FStar_Syntax_Syntax.Tm_refine (_144_848))
in (FStar_Syntax_Syntax.mk _144_849 None t1.FStar_Syntax_Syntax.pos))
in (let _144_851 = (let _144_850 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_144_850)::[])
in (_144_852, _144_851)))
in Some (_144_853))
end
| (_55_1573, FStar_Syntax_Syntax.Tm_refine (x, _55_1576)) -> begin
(let _144_856 = (let _144_855 = (let _144_854 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_144_854)::[])
in (t1, _144_855))
in Some (_144_856))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1582), _55_1586) -> begin
(let _144_859 = (let _144_858 = (let _144_857 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_144_857)::[])
in (t2, _144_858))
in Some (_144_859))
end
| _55_1589 -> begin
None
end))
end))
end)
end)))
in (
# 1175 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1593) -> begin
(
# 1179 "FStar.TypeChecker.Rel.fst"
let _55_1618 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(
# 1183 "FStar.TypeChecker.Rel.fst"
let _55_1604 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1604) with
| (u', _55_1603) -> begin
(match ((let _144_861 = (whnf env u')
in _144_861.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1607) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1611 -> begin
false
end)
end))
end
| _55_1613 -> begin
false
end)
end
| _55_1615 -> begin
false
end))))
in (match (_55_1618) with
| (lower_bounds, rest) -> begin
(
# 1192 "FStar.TypeChecker.Rel.fst"
let rec make_lower_bound = (fun _55_1622 tps -> (match (_55_1622) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _144_866 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _144_866))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1635 -> begin
None
end)
end))
in (match ((let _144_868 = (let _144_867 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_144_867, []))
in (make_lower_bound _144_868 lower_bounds))) with
| None -> begin
(
# 1203 "FStar.TypeChecker.Rel.fst"
let _55_1637 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(
# 1208 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (
# 1209 "FStar.TypeChecker.Rel.fst"
let _55_1647 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1210 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1210 "FStar.TypeChecker.Rel.fst"
let _55_1644 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1644.wl_deferred; ctr = _55_1644.ctr; defer_ok = _55_1644.defer_ok; smt_ok = _55_1644.smt_ok; tcenv = _55_1644.tcenv})
in (let _144_869 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _144_869)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1212 "FStar.TypeChecker.Rel.fst"
let _55_1649 = wl
in {attempting = sub_probs; wl_deferred = _55_1649.wl_deferred; ctr = _55_1649.ctr; defer_ok = _55_1649.defer_ok; smt_ok = _55_1649.smt_ok; tcenv = _55_1649.tcenv}))) with
| Success (_55_1652) -> begin
(
# 1214 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1214 "FStar.TypeChecker.Rel.fst"
let _55_1654 = wl
in {attempting = rest; wl_deferred = _55_1654.wl_deferred; ctr = _55_1654.ctr; defer_ok = _55_1654.defer_ok; smt_ok = _55_1654.smt_ok; tcenv = _55_1654.tcenv})
in (
# 1215 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1216 "FStar.TypeChecker.Rel.fst"
let _55_1660 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1663 -> begin
None
end)))
end))
end))
end
| _55_1665 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1227 "FStar.TypeChecker.Rel.fst"
let _55_1669 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_875 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _144_875))
end else begin
()
end
in (
# 1229 "FStar.TypeChecker.Rel.fst"
let _55_1673 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1673) with
| (u, args) -> begin
(
# 1230 "FStar.TypeChecker.Rel.fst"
let _55_1679 = (0, 1, 2, 3, 4)
in (match (_55_1679) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1231 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1233 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1234 "FStar.TypeChecker.Rel.fst"
let _55_1688 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1688) with
| (h1, args1) -> begin
(
# 1235 "FStar.TypeChecker.Rel.fst"
let _55_1692 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1692) with
| (h2, _55_1691) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _144_887 = (let _144_886 = (let _144_885 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _144_884 -> FStar_TypeChecker_Common.TProb (_144_884)) _144_885))
in (_144_886)::[])
in Some (_144_887))
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
| _55_1704 -> begin
None
end)
end))
end)))
in (
# 1251 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1253 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1257 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1258 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1259 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1260 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _144_894 = (let _144_893 = (let _144_892 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _144_892))
in (_144_893, m))
in Some (_144_894))))))
end))
end
| (_55_1726, FStar_Syntax_Syntax.Tm_refine (y, _55_1729)) -> begin
(
# 1265 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1739), _55_1743) -> begin
(
# 1272 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _55_1750 -> begin
(
# 1279 "FStar.TypeChecker.Rel.fst"
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
# 1285 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1758) -> begin
(
# 1289 "FStar.TypeChecker.Rel.fst"
let _55_1783 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1293 "FStar.TypeChecker.Rel.fst"
let _55_1769 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1769) with
| (u', _55_1768) -> begin
(match ((let _144_896 = (whnf env u')
in _144_896.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1772) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1776 -> begin
false
end)
end))
end
| _55_1778 -> begin
false
end)
end
| _55_1780 -> begin
false
end))))
in (match (_55_1783) with
| (upper_bounds, rest) -> begin
(
# 1302 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _55_1787 tps -> (match (_55_1787) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _144_901 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _144_901))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1800 -> begin
None
end)
end))
in (match ((let _144_903 = (let _144_902 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_144_902, []))
in (make_upper_bound _144_903 upper_bounds))) with
| None -> begin
(
# 1313 "FStar.TypeChecker.Rel.fst"
let _55_1802 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1326 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1327 "FStar.TypeChecker.Rel.fst"
let _55_1812 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1328 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1328 "FStar.TypeChecker.Rel.fst"
let _55_1809 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1809.wl_deferred; ctr = _55_1809.ctr; defer_ok = _55_1809.defer_ok; smt_ok = _55_1809.smt_ok; tcenv = _55_1809.tcenv})
in (let _144_904 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _144_904)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1330 "FStar.TypeChecker.Rel.fst"
let _55_1814 = wl
in {attempting = sub_probs; wl_deferred = _55_1814.wl_deferred; ctr = _55_1814.ctr; defer_ok = _55_1814.defer_ok; smt_ok = _55_1814.smt_ok; tcenv = _55_1814.tcenv}))) with
| Success (_55_1817) -> begin
(
# 1332 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1332 "FStar.TypeChecker.Rel.fst"
let _55_1819 = wl
in {attempting = rest; wl_deferred = _55_1819.wl_deferred; ctr = _55_1819.ctr; defer_ok = _55_1819.defer_ok; smt_ok = _55_1819.smt_ok; tcenv = _55_1819.tcenv})
in (
# 1333 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1334 "FStar.TypeChecker.Rel.fst"
let _55_1825 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1828 -> begin
None
end)))
end))
end))
end
| _55_1830 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1344 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1347 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1348 "FStar.TypeChecker.Rel.fst"
let _55_1847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_932 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _144_932))
end else begin
()
end
in (
# 1350 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1354 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1354 "FStar.TypeChecker.Rel.fst"
let _55_1861 = hd1
in (let _144_933 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1861.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1861.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_933}))
in (
# 1355 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1355 "FStar.TypeChecker.Rel.fst"
let _55_1864 = hd2
in (let _144_934 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1864.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1864.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_934}))
in (
# 1356 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_937 = (let _144_936 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _144_936 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _144_935 -> FStar_TypeChecker_Common.TProb (_144_935)) _144_937))
in (
# 1357 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1358 "FStar.TypeChecker.Rel.fst"
let subst = (let _144_938 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_144_938)
in (
# 1359 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1362 "FStar.TypeChecker.Rel.fst"
let phi = (let _144_940 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _144_939 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _144_940 _144_939)))
in (
# 1363 "FStar.TypeChecker.Rel.fst"
let _55_1876 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_942 = (FStar_Syntax_Print.term_to_string phi)
in (let _144_941 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _144_942 _144_941)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _55_1880 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1372 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1376 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _144_946 = (compress_tprob wl problem)
in (solve_t' env _144_946 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1383 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1386 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1387 "FStar.TypeChecker.Rel.fst"
let _55_1908 = (head_matches_delta env wl t1 t2)
in (match (_55_1908) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_55_1910), _55_1913) -> begin
(
# 1390 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_1926 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1396 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1399 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1403 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _144_975 = (let _144_974 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _144_974 t2))
in (FStar_Syntax_Util.mk_forall x _144_975)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _144_976 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _144_976)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_1936, Some (t1, t2)) -> begin
(solve_t env (
# 1412 "FStar.TypeChecker.Rel.fst"
let _55_1942 = problem
in {FStar_TypeChecker_Common.pid = _55_1942.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_1942.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_1942.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1942.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1942.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1942.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1942.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1942.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_1945, None) -> begin
(
# 1415 "FStar.TypeChecker.Rel.fst"
let _55_1948 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_980 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_979 = (FStar_Syntax_Print.tag_of_term t1)
in (let _144_978 = (FStar_Syntax_Print.term_to_string t2)
in (let _144_977 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _144_980 _144_979 _144_978 _144_977)))))
end else begin
()
end
in (
# 1419 "FStar.TypeChecker.Rel.fst"
let _55_1952 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1952) with
| (head1, args1) -> begin
(
# 1420 "FStar.TypeChecker.Rel.fst"
let _55_1955 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1955) with
| (head2, args2) -> begin
(
# 1421 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _144_985 = (let _144_984 = (FStar_Syntax_Print.term_to_string head1)
in (let _144_983 = (args_to_string args1)
in (let _144_982 = (FStar_Syntax_Print.term_to_string head2)
in (let _144_981 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _144_984 _144_983 _144_982 _144_981)))))
in (giveup env _144_985 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _144_986 = (solve_prob orig None [] wl)
in (solve env _144_986))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1442 "FStar.TypeChecker.Rel.fst"
let _55_1965 = (base_and_refinement env wl t1)
in (match (_55_1965) with
| (base1, refinement1) -> begin
(
# 1443 "FStar.TypeChecker.Rel.fst"
let _55_1968 = (base_and_refinement env wl t2)
in (match (_55_1968) with
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
# 1450 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _55_1981 _55_1985 -> (match ((_55_1981, _55_1985)) with
| ((a, _55_1980), (a', _55_1984)) -> begin
(let _144_990 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _144_989 -> FStar_TypeChecker_Common.TProb (_144_989)) _144_990))
end)) args1 args2)
in (
# 1451 "FStar.TypeChecker.Rel.fst"
let formula = (let _144_992 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _144_992))
in (
# 1452 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_1991 -> begin
(
# 1457 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1458 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1459 "FStar.TypeChecker.Rel.fst"
let _55_1994 = problem
in {FStar_TypeChecker_Common.pid = _55_1994.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_1994.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_1994.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1994.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1994.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1994.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1994.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1994.FStar_TypeChecker_Common.rank}) wl)))
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
# 1465 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1466 "FStar.TypeChecker.Rel.fst"
let _55_2013 = p
in (match (_55_2013) with
| (((u, k), xs, c), ps, (h, _55_2010, qs)) -> begin
(
# 1467 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1472 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1473 "FStar.TypeChecker.Rel.fst"
let _55_2019 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2019) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1474 "FStar.TypeChecker.Rel.fst"
let im = (let _144_1007 = (h gs_xs)
in (let _144_1006 = (let _144_1005 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_1003 -> FStar_Util.Inl (_144_1003)))
in (FStar_All.pipe_right _144_1005 (fun _144_1004 -> Some (_144_1004))))
in (FStar_Syntax_Util.abs xs _144_1007 _144_1006)))
in (
# 1475 "FStar.TypeChecker.Rel.fst"
let _55_2021 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1014 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _144_1013 = (FStar_Syntax_Print.comp_to_string c)
in (let _144_1012 = (FStar_Syntax_Print.term_to_string im)
in (let _144_1011 = (FStar_Syntax_Print.tag_of_term im)
in (let _144_1010 = (let _144_1008 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _144_1008 (FStar_String.concat ", ")))
in (let _144_1009 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _144_1014 _144_1013 _144_1012 _144_1011 _144_1010 _144_1009)))))))
end else begin
()
end
in (
# 1482 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1486 "FStar.TypeChecker.Rel.fst"
let imitate' = (fun orig env wl _55_25 -> (match (_55_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (
# 1491 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1492 "FStar.TypeChecker.Rel.fst"
let _55_2047 = p
in (match (_55_2047) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(
# 1496 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1497 "FStar.TypeChecker.Rel.fst"
let _55_2052 = (FStar_List.nth ps i)
in (match (_55_2052) with
| (pi, _55_2051) -> begin
(
# 1498 "FStar.TypeChecker.Rel.fst"
let _55_2056 = (FStar_List.nth xs i)
in (match (_55_2056) with
| (xi, _55_2055) -> begin
(
# 1500 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1501 "FStar.TypeChecker.Rel.fst"
let _55_2061 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2061) with
| (bs, k) -> begin
(
# 1502 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _55_2069)::tl -> begin
(
# 1505 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1506 "FStar.TypeChecker.Rel.fst"
let _55_2075 = (new_uvar r xs k_a)
in (match (_55_2075) with
| (gi_xs, gi) -> begin
(
# 1507 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1508 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1509 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1510 "FStar.TypeChecker.Rel.fst"
let _55_2081 = (aux subst tl)
in (match (_55_2081) with
| (gi_xs', gi_ps') -> begin
(let _144_1044 = (let _144_1041 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_144_1041)::gi_xs')
in (let _144_1043 = (let _144_1042 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_144_1042)::gi_ps')
in (_144_1044, _144_1043)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _144_1045 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _144_1045)) then begin
None
end else begin
(
# 1516 "FStar.TypeChecker.Rel.fst"
let _55_2085 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2085) with
| (g_xs, _55_2084) -> begin
(
# 1517 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1518 "FStar.TypeChecker.Rel.fst"
let proj = (let _144_1050 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _144_1049 = (let _144_1048 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_1046 -> FStar_Util.Inl (_144_1046)))
in (FStar_All.pipe_right _144_1048 (fun _144_1047 -> Some (_144_1047))))
in (FStar_Syntax_Util.abs xs _144_1050 _144_1049)))
in (
# 1519 "FStar.TypeChecker.Rel.fst"
let sub = (let _144_1056 = (let _144_1055 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _144_1054 = (let _144_1053 = (FStar_List.map (fun _55_2093 -> (match (_55_2093) with
| (_55_2089, _55_2091, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _144_1053))
in (mk_problem (p_scope orig) orig _144_1055 (p_rel orig) _144_1054 None "projection")))
in (FStar_All.pipe_left (fun _144_1051 -> FStar_TypeChecker_Common.TProb (_144_1051)) _144_1056))
in (
# 1520 "FStar.TypeChecker.Rel.fst"
let _55_2095 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1058 = (FStar_Syntax_Print.term_to_string proj)
in (let _144_1057 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _144_1058 _144_1057)))
end else begin
()
end
in (
# 1521 "FStar.TypeChecker.Rel.fst"
let wl = (let _144_1060 = (let _144_1059 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_144_1059))
in (solve_prob orig _144_1060 ((TERM ((u, proj)))::[]) wl))
in (let _144_1062 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _144_1061 -> Some (_144_1061)) _144_1062)))))))
end))
end)
end))
end)))
end)))
in (
# 1526 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1527 "FStar.TypeChecker.Rel.fst"
let _55_2109 = lhs
in (match (_55_2109) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(
# 1528 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1529 "FStar.TypeChecker.Rel.fst"
let _55_2114 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2114) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _144_1084 = (let _144_1083 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _144_1083))
in Some (_144_1084))
end else begin
(
# 1532 "FStar.TypeChecker.Rel.fst"
let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (
# 1533 "FStar.TypeChecker.Rel.fst"
let rec elim = (fun k args -> (match ((let _144_1090 = (let _144_1089 = (FStar_Syntax_Subst.compress k)
in _144_1089.FStar_Syntax_Syntax.n)
in (_144_1090, args))) with
| (_55_2120, []) -> begin
(let _144_1092 = (let _144_1091 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _144_1091))
in Some (_144_1092))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(
# 1538 "FStar.TypeChecker.Rel.fst"
let _55_2137 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2137) with
| (uv, uv_args) -> begin
(match ((let _144_1093 = (FStar_Syntax_Subst.compress uv)
in _144_1093.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2140) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(
# 1544 "FStar.TypeChecker.Rel.fst"
let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2146 -> (let _144_1099 = (let _144_1098 = (let _144_1097 = (let _144_1096 = (let _144_1095 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1095 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _144_1096))
in (Prims.fst _144_1097))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _144_1098))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _144_1099)))))
in (
# 1548 "FStar.TypeChecker.Rel.fst"
let c = (let _144_1103 = (let _144_1102 = (let _144_1101 = (let _144_1100 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1100 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _144_1101))
in (Prims.fst _144_1102))
in (FStar_Syntax_Syntax.mk_Total _144_1103))
in (
# 1549 "FStar.TypeChecker.Rel.fst"
let k' = (FStar_Syntax_Util.arrow xs c)
in (
# 1550 "FStar.TypeChecker.Rel.fst"
let uv_sol = (let _144_1109 = (let _144_1108 = (let _144_1107 = (let _144_1106 = (let _144_1105 = (let _144_1104 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1104 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _144_1105))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _144_1106))
in FStar_Util.Inl (_144_1107))
in Some (_144_1108))
in (FStar_Syntax_Util.abs scope k' _144_1109))
in (
# 1551 "FStar.TypeChecker.Rel.fst"
let _55_2152 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some ((xs, c)))))))
end)
end
| _55_2155 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2161) -> begin
(
# 1556 "FStar.TypeChecker.Rel.fst"
let n_args = (FStar_List.length args)
in (
# 1557 "FStar.TypeChecker.Rel.fst"
let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _144_1111 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _144_1111 (fun _144_1110 -> Some (_144_1110))))
end else begin
if (n_xs < n_args) then begin
(
# 1561 "FStar.TypeChecker.Rel.fst"
let _55_2167 = (FStar_Util.first_N n_xs args)
in (match (_55_2167) with
| (args, rest) -> begin
(
# 1562 "FStar.TypeChecker.Rel.fst"
let _55_2170 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2170) with
| (xs, c) -> begin
(let _144_1113 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _144_1113 (fun _55_2173 -> (match (_55_2173) with
| (xs', c) -> begin
Some (((FStar_List.append xs xs'), c))
end))))
end))
end))
end else begin
(
# 1567 "FStar.TypeChecker.Rel.fst"
let _55_2176 = (FStar_Util.first_N n_args xs)
in (match (_55_2176) with
| (xs, rest) -> begin
(
# 1568 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) None k.FStar_Syntax_Syntax.pos)
in (let _144_1116 = (let _144_1114 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _144_1114))
in (FStar_All.pipe_right _144_1116 (fun _144_1115 -> Some (_144_1115)))))
end))
end
end))
end
| _55_2179 -> begin
(let _144_1120 = (let _144_1119 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _144_1118 = (FStar_Syntax_Print.term_to_string k)
in (let _144_1117 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _144_1119 _144_1118 _144_1117))))
in (FStar_All.failwith _144_1120))
end))
in (let _144_1158 = (elim k_uv ps)
in (FStar_Util.bind_opt _144_1158 (fun _55_2182 -> (match (_55_2182) with
| (xs, c) -> begin
(let _144_1157 = (let _144_1156 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _144_1156))
in Some (_144_1157))
end))))))
end
end)))
in (
# 1578 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n stopt i -> if ((i >= n) || (FStar_Option.isNone stopt)) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1581 "FStar.TypeChecker.Rel.fst"
let st = (FStar_Option.get stopt)
in (
# 1582 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_55_2190) -> begin
(
# 1586 "FStar.TypeChecker.Rel.fst"
let _55_2192 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1593 "FStar.TypeChecker.Rel.fst"
let _55_2200 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (
# 1597 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1598 "FStar.TypeChecker.Rel.fst"
let _55_2210 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2210) with
| (hd, _55_2209) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2221 -> begin
(
# 1604 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1607 "FStar.TypeChecker.Rel.fst"
let _55_2223 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1169 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _144_1169))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1610 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1611 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _144_1173 = (let _144_1172 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _144_1172 Prims.fst))
in (FStar_All.pipe_right _144_1173 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1618 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1619 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1620 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1621 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1622 "FStar.TypeChecker.Rel.fst"
let _55_2236 = (occurs_check env wl (uv, k_uv) t2)
in (match (_55_2236) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _144_1175 = (let _144_1174 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _144_1174))
in (giveup_or_defer orig _144_1175))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _144_1176 = (subterms args_lhs)
in (imitate' orig env wl _144_1176))
end else begin
(
# 1629 "FStar.TypeChecker.Rel.fst"
let _55_2237 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1179 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1178 = (names_to_string fvs1)
in (let _144_1177 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _144_1179 _144_1178 _144_1177))))
end else begin
()
end
in (
# 1634 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2241 -> begin
(let _144_1180 = (sn_binders env vars)
in (u_abs k_uv _144_1180 t2))
end)
in (
# 1637 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1642 "FStar.TypeChecker.Rel.fst"
let _55_2244 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1183 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1182 = (names_to_string fvs1)
in (let _144_1181 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _144_1183 _144_1182 _144_1181))))
end else begin
()
end
in (let _144_1184 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _144_1184 (- (1)))))
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
if (let _144_1185 = (FStar_Syntax_Free.names t1)
in (check_head _144_1185 t2)) then begin
(
# 1654 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1655 "FStar.TypeChecker.Rel.fst"
let _55_2248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1186 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _144_1186 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _144_1187 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _144_1187 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1680 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1683 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _55_2260 -> (match (_55_2260) with
| (t, u, k, args) -> begin
(
# 1686 "FStar.TypeChecker.Rel.fst"
let _55_2264 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2264) with
| (all_formals, _55_2263) -> begin
(
# 1687 "FStar.TypeChecker.Rel.fst"
let _55_2265 = ()
in (
# 1689 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1697 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2278 -> (match (_55_2278) with
| (x, imp) -> begin
(let _144_1209 = (FStar_Syntax_Syntax.bv_to_name x)
in (_144_1209, imp))
end))))
in (
# 1698 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1699 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1700 "FStar.TypeChecker.Rel.fst"
let _55_2284 = (FStar_Syntax_Util.type_u ())
in (match (_55_2284) with
| (t, _55_2283) -> begin
(let _144_1210 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _144_1210))
end))
in (
# 1702 "FStar.TypeChecker.Rel.fst"
let _55_2288 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2288) with
| (t', tm_u1) -> begin
(
# 1703 "FStar.TypeChecker.Rel.fst"
let _55_2295 = (destruct_flex_t t')
in (match (_55_2295) with
| (_55_2290, u1, k1, _55_2294) -> begin
(
# 1704 "FStar.TypeChecker.Rel.fst"
let sol = (let _144_1212 = (let _144_1211 = (u_abs k all_formals t')
in ((u, k), _144_1211))
in TERM (_144_1212))
in (
# 1705 "FStar.TypeChecker.Rel.fst"
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
# 1714 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2314 -> (match (_55_2314) with
| (x, _55_2313) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1721 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _144_1214 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _144_1214 formals tl))
end)
end)
end)
end
| _55_2318 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _144_1215 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _144_1215 all_formals args))))
end))
end))
in (
# 1733 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _55_2325 _55_2330 r -> (match ((_55_2325, _55_2330)) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _144_1224 = (solve_prob orig None [] wl)
in (solve env _144_1224))
end else begin
(
# 1741 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1742 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1743 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1744 "FStar.TypeChecker.Rel.fst"
let _55_2335 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1229 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _144_1228 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _144_1227 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _144_1226 = (FStar_Syntax_Print.term_to_string k1)
in (let _144_1225 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _144_1229 _144_1228 _144_1227 _144_1226 _144_1225))))))
end else begin
()
end
in (
# 1748 "FStar.TypeChecker.Rel.fst"
let _55_2348 = (
# 1749 "FStar.TypeChecker.Rel.fst"
let _55_2340 = (FStar_Syntax_Util.type_u ())
in (match (_55_2340) with
| (t, _55_2339) -> begin
(
# 1750 "FStar.TypeChecker.Rel.fst"
let _55_2344 = (new_uvar r zs t)
in (match (_55_2344) with
| (k, _55_2343) -> begin
(new_uvar r zs k)
end))
end))
in (match (_55_2348) with
| (u_zs, _55_2347) -> begin
(
# 1752 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs k1 xs u_zs)
in (
# 1753 "FStar.TypeChecker.Rel.fst"
let _55_2352 = (occurs_check env wl (u1, k1) sub1)
in (match (_55_2352) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1756 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1758 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1760 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs k2 ys u_zs)
in (
# 1761 "FStar.TypeChecker.Rel.fst"
let _55_2358 = (occurs_check env wl (u2, k2) sub2)
in (match (_55_2358) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1764 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1765 "FStar.TypeChecker.Rel.fst"
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
# 1769 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _55_2366 _55_2371 -> (match ((_55_2366, _55_2371)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1771 "FStar.TypeChecker.Rel.fst"
let _55_2372 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1235 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1234 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _144_1235 _144_1234)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1774 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _55_2377 _55_2381 -> (match ((_55_2377, _55_2381)) with
| ((a, _55_2376), (t2, _55_2380)) -> begin
(let _144_1240 = (let _144_1238 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _144_1238 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _144_1240 (fun _144_1239 -> FStar_TypeChecker_Common.TProb (_144_1239))))
end)) xs args2)
in (
# 1777 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1242 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _144_1242))
in (
# 1778 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1781 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1782 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1783 "FStar.TypeChecker.Rel.fst"
let _55_2391 = (occurs_check env wl (u1, k1) t2)
in (match (_55_2391) with
| (occurs_ok, _55_2390) -> begin
(
# 1784 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1787 "FStar.TypeChecker.Rel.fst"
let sol = (let _144_1244 = (let _144_1243 = (u_abs k1 xs t2)
in ((u1, k1), _144_1243))
in TERM (_144_1244))
in (
# 1788 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1791 "FStar.TypeChecker.Rel.fst"
let _55_2402 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_55_2402) with
| (sol, (_55_2397, u2, k2, ys)) -> begin
(
# 1792 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1793 "FStar.TypeChecker.Rel.fst"
let _55_2404 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _144_1245 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _144_1245))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2409 -> begin
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
# 1801 "FStar.TypeChecker.Rel.fst"
let _55_2414 = lhs
in (match (_55_2414) with
| (t1, u1, k1, args1) -> begin
(
# 1802 "FStar.TypeChecker.Rel.fst"
let _55_2419 = rhs
in (match (_55_2419) with
| (t2, u2, k2, args2) -> begin
(
# 1803 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1804 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1805 "FStar.TypeChecker.Rel.fst"
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
| _55_2437 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1814 "FStar.TypeChecker.Rel.fst"
let _55_2441 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_55_2441) with
| (sol, _55_2440) -> begin
(
# 1815 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1816 "FStar.TypeChecker.Rel.fst"
let _55_2443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _144_1246 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _144_1246))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2448 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1823 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _144_1247 = (solve_prob orig None [] wl)
in (solve env _144_1247))
end else begin
(
# 1825 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1826 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _144_1248 = (solve_prob orig None [] wl)
in (solve env _144_1248))
end else begin
(
# 1828 "FStar.TypeChecker.Rel.fst"
let _55_2452 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1249 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _144_1249))
end else begin
()
end
in (
# 1831 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1833 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _55_2457 _55_2460 -> (match ((_55_2457, _55_2460)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1835 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1836 "FStar.TypeChecker.Rel.fst"
let _55_2467 = (FStar_Util.first_N n bs)
in (match (_55_2467) with
| (bs, rest) -> begin
(let _144_1279 = (mk_cod rest)
in (bs, _144_1279))
end)))
in (
# 1839 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1840 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _144_1283 = (let _144_1280 = (mk_cod1 [])
in (bs1, _144_1280))
in (let _144_1282 = (let _144_1281 = (mk_cod2 [])
in (bs2, _144_1281))
in (_144_1283, _144_1282)))
end else begin
if (l1 > l2) then begin
(let _144_1286 = (curry l2 bs1 mk_cod1)
in (let _144_1285 = (let _144_1284 = (mk_cod2 [])
in (bs2, _144_1284))
in (_144_1286, _144_1285)))
end else begin
(let _144_1289 = (let _144_1287 = (mk_cod1 [])
in (bs1, _144_1287))
in (let _144_1288 = (curry l1 bs2 mk_cod2)
in (_144_1289, _144_1288)))
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
# 1858 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _55_26 -> (match (_55_26) with
| [] -> begin
c
end
| bs -> begin
(let _144_1294 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _144_1294))
end))
in (
# 1862 "FStar.TypeChecker.Rel.fst"
let _55_2510 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_55_2510) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1867 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1868 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1869 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _144_1301 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _144_1300 -> FStar_TypeChecker_Common.CProb (_144_1300)) _144_1301)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(
# 1873 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, l))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1876 "FStar.TypeChecker.Rel.fst"
let _55_2540 = (match_num_binders (bs1, (mk_t tbody1 lopt1)) (bs2, (mk_t tbody2 lopt2)))
in (match (_55_2540) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _144_1316 = (let _144_1315 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _144_1314 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _144_1315 problem.FStar_TypeChecker_Common.relation _144_1314 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _144_1313 -> FStar_TypeChecker_Common.TProb (_144_1313)) _144_1316))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2545), FStar_Syntax_Syntax.Tm_refine (_55_2548)) -> begin
(
# 1885 "FStar.TypeChecker.Rel.fst"
let _55_2553 = (as_refinement env wl t1)
in (match (_55_2553) with
| (x1, phi1) -> begin
(
# 1886 "FStar.TypeChecker.Rel.fst"
let _55_2556 = (as_refinement env wl t2)
in (match (_55_2556) with
| (x2, phi2) -> begin
(
# 1887 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1318 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _144_1317 -> FStar_TypeChecker_Common.TProb (_144_1317)) _144_1318))
in (
# 1888 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1889 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1890 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1891 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1892 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1893 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _144_1335 = (imp phi1 phi2)
in (FStar_All.pipe_right _144_1335 (guard_on_element problem x1))))
in (
# 1894 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _55_2568 -> (match (()) with
| () -> begin
(
# 1895 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1899 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1338 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1338 impl))
in (
# 1900 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1903 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _144_1342 = (let _144_1341 = (let _144_1340 = (FStar_Syntax_Syntax.mk_binder x1)
in (_144_1340)::(p_scope orig))
in (mk_problem _144_1341 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _144_1339 -> FStar_TypeChecker_Common.TProb (_144_1339)) _144_1342))
in (match ((solve env (
# 1904 "FStar.TypeChecker.Rel.fst"
let _55_2573 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2573.ctr; defer_ok = false; smt_ok = _55_2573.smt_ok; tcenv = _55_2573.tcenv}))) with
| Failed (_55_2576) -> begin
(fallback ())
end
| Success (_55_2579) -> begin
(
# 1907 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1345 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _144_1344 = (let _144_1343 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _144_1343 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _144_1345 _144_1344)))
in (
# 1908 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1909 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1909 "FStar.TypeChecker.Rel.fst"
let _55_2583 = wl
in {attempting = _55_2583.attempting; wl_deferred = _55_2583.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_2583.defer_ok; smt_ok = _55_2583.smt_ok; tcenv = _55_2583.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _144_1347 = (destruct_flex_t t1)
in (let _144_1346 = (destruct_flex_t t2)
in (flex_flex orig _144_1347 _144_1346)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _144_1348 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _144_1348 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1937 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _144_1349 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _144_1349)) then begin
(let _144_1352 = (FStar_All.pipe_left (fun _144_1350 -> FStar_TypeChecker_Common.TProb (_144_1350)) (
# 1939 "FStar.TypeChecker.Rel.fst"
let _55_2728 = problem
in {FStar_TypeChecker_Common.pid = _55_2728.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2728.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2728.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2728.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2728.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2728.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2728.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2728.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2728.FStar_TypeChecker_Common.rank}))
in (let _144_1351 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _144_1352 _144_1351 t2 wl)))
end else begin
(
# 1940 "FStar.TypeChecker.Rel.fst"
let _55_2732 = (base_and_refinement env wl t2)
in (match (_55_2732) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _144_1355 = (FStar_All.pipe_left (fun _144_1353 -> FStar_TypeChecker_Common.TProb (_144_1353)) (
# 1943 "FStar.TypeChecker.Rel.fst"
let _55_2734 = problem
in {FStar_TypeChecker_Common.pid = _55_2734.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2734.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2734.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2734.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2734.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2734.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2734.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2734.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2734.FStar_TypeChecker_Common.rank}))
in (let _144_1354 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _144_1355 _144_1354 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1946 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1946 "FStar.TypeChecker.Rel.fst"
let _55_2740 = y
in {FStar_Syntax_Syntax.ppname = _55_2740.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2740.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1947 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1948 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1357 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _144_1356 -> FStar_TypeChecker_Common.TProb (_144_1356)) _144_1357))
in (
# 1950 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1358 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1358 impl))
in (
# 1951 "FStar.TypeChecker.Rel.fst"
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
# 1960 "FStar.TypeChecker.Rel.fst"
let _55_2773 = (base_and_refinement env wl t1)
in (match (_55_2773) with
| (t_base, _55_2772) -> begin
(solve_t env (
# 1961 "FStar.TypeChecker.Rel.fst"
let _55_2774 = problem
in {FStar_TypeChecker_Common.pid = _55_2774.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2774.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2774.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2774.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2774.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2774.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2774.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2774.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2777), _55_2780) -> begin
(
# 1964 "FStar.TypeChecker.Rel.fst"
let t2 = (let _144_1359 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _144_1359))
in (solve_t env (
# 1965 "FStar.TypeChecker.Rel.fst"
let _55_2783 = problem
in {FStar_TypeChecker_Common.pid = _55_2783.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2783.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2783.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2783.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2783.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2783.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2783.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2783.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2783.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_2786, FStar_Syntax_Syntax.Tm_refine (_55_2788)) -> begin
(
# 1968 "FStar.TypeChecker.Rel.fst"
let t1 = (let _144_1360 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _144_1360))
in (solve_t env (
# 1969 "FStar.TypeChecker.Rel.fst"
let _55_2792 = problem
in {FStar_TypeChecker_Common.pid = _55_2792.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2792.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2792.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2792.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2792.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2792.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2792.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2792.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2792.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1973 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2809) -> begin
t
end
| _55_2812 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _144_1365 = (
# 1976 "FStar.TypeChecker.Rel.fst"
let _55_2813 = problem
in (let _144_1364 = (maybe_eta t1)
in (let _144_1363 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2813.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_1364; FStar_TypeChecker_Common.relation = _55_2813.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_1363; FStar_TypeChecker_Common.element = _55_2813.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2813.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2813.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2813.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2813.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2813.FStar_TypeChecker_Common.rank})))
in (solve_t env _144_1365 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1990 "FStar.TypeChecker.Rel.fst"
let head1 = (let _144_1366 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _144_1366 Prims.fst))
in (
# 1991 "FStar.TypeChecker.Rel.fst"
let head2 = (let _144_1367 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _144_1367 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1996 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1997 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1999 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _144_1369 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _144_1368 -> Some (_144_1368)) _144_1369))
end
in (let _144_1370 = (solve_prob orig guard [] wl)
in (solve env _144_1370)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_2894, _55_2896), _55_2900) -> begin
(solve_t' env (
# 2007 "FStar.TypeChecker.Rel.fst"
let _55_2902 = problem
in {FStar_TypeChecker_Common.pid = _55_2902.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2902.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2902.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2902.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2902.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2902.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2902.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2902.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2902.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2905, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_2908, _55_2910)) -> begin
(solve_t' env (
# 2010 "FStar.TypeChecker.Rel.fst"
let _55_2914 = problem
in {FStar_TypeChecker_Common.pid = _55_2914.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2914.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2914.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2914.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2914.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2914.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2914.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2914.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2914.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _144_1373 = (let _144_1372 = (FStar_Syntax_Print.tag_of_term t1)
in (let _144_1371 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _144_1372 _144_1371)))
in (FStar_All.failwith _144_1373))
end
| _55_2953 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end)))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 2022 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 2023 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 2024 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 2025 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 2028 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 2029 "FStar.TypeChecker.Rel.fst"
let _55_2970 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 2031 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _55_2975 _55_2979 -> (match ((_55_2975, _55_2979)) with
| ((a1, _55_2974), (a2, _55_2978)) -> begin
(let _144_1388 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _144_1387 -> FStar_TypeChecker_Common.TProb (_144_1387)) _144_1388))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 2034 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1390 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _144_1390))
in (
# 2035 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (
# 2039 "FStar.TypeChecker.Rel.fst"
let solve_sub = (fun c1 edge c2 -> (
# 2040 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 2042 "FStar.TypeChecker.Rel.fst"
let _55_3002 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _55_2995)::(wlp1, _55_2991)::[] -> begin
(wp1, wlp1)
end
| _55_2999 -> begin
(let _144_1398 = (let _144_1397 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _144_1397))
in (FStar_All.failwith _144_1398))
end)
in (match (_55_3002) with
| (wp, wlp) -> begin
(
# 2045 "FStar.TypeChecker.Rel.fst"
let c1 = (let _144_1404 = (let _144_1403 = (let _144_1399 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _144_1399))
in (let _144_1402 = (let _144_1401 = (let _144_1400 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _144_1400))
in (_144_1401)::[])
in (_144_1403)::_144_1402))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _144_1404; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2052 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3009 -> begin
false
end))))
in (
# 2053 "FStar.TypeChecker.Rel.fst"
let _55_3030 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _55_3015)::_55_3012, (wp2, _55_3022)::_55_3019) -> begin
(wp1, wp2)
end
| _55_3027 -> begin
(let _144_1408 = (let _144_1407 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _144_1406 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _144_1407 _144_1406)))
in (FStar_All.failwith _144_1408))
end)
in (match (_55_3030) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _144_1409 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _144_1409 wl))
end else begin
(
# 2060 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 2061 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2063 "FStar.TypeChecker.Rel.fst"
let _55_3032 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _144_1419 = (let _144_1418 = (let _144_1417 = (let _144_1411 = (let _144_1410 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_144_1410)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1411 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _144_1416 = (let _144_1415 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _144_1414 = (let _144_1413 = (let _144_1412 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1412))
in (_144_1413)::[])
in (_144_1415)::_144_1414))
in (_144_1417, _144_1416)))
in FStar_Syntax_Syntax.Tm_app (_144_1418))
in (FStar_Syntax_Syntax.mk _144_1419 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 2067 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _144_1435 = (let _144_1434 = (let _144_1433 = (let _144_1421 = (let _144_1420 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_144_1420)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1421 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _144_1432 = (let _144_1431 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _144_1430 = (let _144_1429 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _144_1428 = (let _144_1427 = (let _144_1423 = (let _144_1422 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _144_1422 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1423))
in (let _144_1426 = (let _144_1425 = (let _144_1424 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1424))
in (_144_1425)::[])
in (_144_1427)::_144_1426))
in (_144_1429)::_144_1428))
in (_144_1431)::_144_1430))
in (_144_1433, _144_1432)))
in FStar_Syntax_Syntax.Tm_app (_144_1434))
in (FStar_Syntax_Syntax.mk _144_1435 None r))
in (let _144_1444 = (let _144_1443 = (let _144_1442 = (let _144_1437 = (let _144_1436 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_144_1436)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1437 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _144_1441 = (let _144_1440 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _144_1439 = (let _144_1438 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_144_1438)::[])
in (_144_1440)::_144_1439))
in (_144_1442, _144_1441)))
in FStar_Syntax_Syntax.Tm_app (_144_1443))
in (FStar_Syntax_Syntax.mk _144_1444 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 2074 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1446 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _144_1445 -> FStar_TypeChecker_Common.TProb (_144_1445)) _144_1446))
in (
# 2075 "FStar.TypeChecker.Rel.fst"
let wl = (let _144_1450 = (let _144_1449 = (let _144_1448 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1448 g))
in (FStar_All.pipe_left (fun _144_1447 -> Some (_144_1447)) _144_1449))
in (solve_prob orig _144_1450 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _144_1451 = (solve_prob orig None [] wl)
in (solve env _144_1451))
end else begin
(
# 2081 "FStar.TypeChecker.Rel.fst"
let _55_3038 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1453 = (FStar_Syntax_Print.comp_to_string c1)
in (let _144_1452 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _144_1453 (rel_to_string problem.FStar_TypeChecker_Common.relation) _144_1452)))
end else begin
()
end
in (
# 2086 "FStar.TypeChecker.Rel.fst"
let _55_3042 = (let _144_1455 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _144_1454 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in (_144_1455, _144_1454)))
in (match (_55_3042) with
| (c1, c2) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _144_1456 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _144_1456 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3049), FStar_Syntax_Syntax.Total (_55_3052)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _144_1457 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _144_1457 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _144_1459 = (
# 2101 "FStar.TypeChecker.Rel.fst"
let _55_3080 = problem
in (let _144_1458 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3080.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_1458; FStar_TypeChecker_Common.relation = _55_3080.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3080.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3080.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3080.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3080.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3080.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3080.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3080.FStar_TypeChecker_Common.rank}))
in (solve_c env _144_1459 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _144_1461 = (
# 2105 "FStar.TypeChecker.Rel.fst"
let _55_3096 = problem
in (let _144_1460 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3096.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3096.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3096.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_1460; FStar_TypeChecker_Common.element = _55_3096.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3096.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3096.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3096.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3096.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3096.FStar_TypeChecker_Common.rank}))
in (solve_c env _144_1461 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3099), FStar_Syntax_Syntax.Comp (_55_3102)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _144_1462 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _144_1462 wl))
end else begin
(
# 2111 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 2112 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2116 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 2117 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 2118 "FStar.TypeChecker.Rel.fst"
let _55_3109 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _144_1463 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _144_1463))) then begin
(
# 2124 "FStar.TypeChecker.Rel.fst"
let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _144_1468 = (let _144_1467 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _144_1466 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _144_1467 _144_1466)))
in (giveup env _144_1468 orig))
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

# 2131 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _144_1472 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3129 -> (match (_55_3129) with
| (_55_3119, _55_3121, u, _55_3124, _55_3126, _55_3128) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _144_1472 (FStar_String.concat ", "))))

# 2136 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3136 -> begin
(
# 2142 "FStar.TypeChecker.Rel.fst"
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
# 2149 "FStar.TypeChecker.Rel.fst"
let carry = (let _144_1478 = (FStar_List.map (fun _55_3144 -> (match (_55_3144) with
| (_55_3142, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _144_1478 (FStar_String.concat ",\n")))
in (
# 2150 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 2151 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 2156 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 2158 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3153; FStar_TypeChecker_Env.implicits = _55_3151} -> begin
true
end
| _55_3158 -> begin
false
end))

# 2162 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 2164 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2170 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _55_3176 -> begin
(FStar_All.failwith "impossible")
end)
in (let _144_1499 = (
# 2173 "FStar.TypeChecker.Rel.fst"
let _55_3178 = g
in (let _144_1498 = (let _144_1497 = (let _144_1496 = (let _144_1490 = (FStar_Syntax_Syntax.mk_binder x)
in (_144_1490)::[])
in (let _144_1495 = (let _144_1494 = (let _144_1493 = (let _144_1491 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _144_1491 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _144_1493 (fun _144_1492 -> FStar_Util.Inl (_144_1492))))
in Some (_144_1494))
in (FStar_Syntax_Util.abs _144_1496 f _144_1495)))
in (FStar_All.pipe_left (fun _144_1489 -> FStar_TypeChecker_Common.NonTrivial (_144_1489)) _144_1497))
in {FStar_TypeChecker_Env.guard_f = _144_1498; FStar_TypeChecker_Env.deferred = _55_3178.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3178.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3178.FStar_TypeChecker_Env.implicits}))
in Some (_144_1499)))
end))

# 2173 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2177 "FStar.TypeChecker.Rel.fst"
let _55_3185 = g
in (let _144_1510 = (let _144_1509 = (let _144_1508 = (let _144_1507 = (let _144_1506 = (let _144_1505 = (FStar_Syntax_Syntax.as_arg e)
in (_144_1505)::[])
in (f, _144_1506))
in FStar_Syntax_Syntax.Tm_app (_144_1507))
in (FStar_Syntax_Syntax.mk _144_1508 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _144_1504 -> FStar_TypeChecker_Common.NonTrivial (_144_1504)) _144_1509))
in {FStar_TypeChecker_Env.guard_f = _144_1510; FStar_TypeChecker_Env.deferred = _55_3185.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3185.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3185.FStar_TypeChecker_Env.implicits}))
end))

# 2177 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3190) -> begin
(FStar_All.failwith "impossible")
end))

# 2181 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _144_1517 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_144_1517))
end))

# 2186 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3208 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 2190 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2196 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2196 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _144_1540 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _144_1540; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2201 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2202 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2203 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2207 "FStar.TypeChecker.Rel.fst"
let _55_3235 = g
in (let _144_1555 = (let _144_1554 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _144_1554 (fun _144_1553 -> FStar_TypeChecker_Common.NonTrivial (_144_1553))))
in {FStar_TypeChecker_Env.guard_f = _144_1555; FStar_TypeChecker_Env.deferred = _55_3235.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3235.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3235.FStar_TypeChecker_Env.implicits}))
end))

# 2207 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2213 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _144_1563 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _144_1562 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _144_1563 (rel_to_string rel) _144_1562)))
end else begin
"TOP"
end
in (
# 2218 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2219 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2222 "FStar.TypeChecker.Rel.fst"
let x = (let _144_1574 = (let _144_1573 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _144_1572 -> Some (_144_1572)) _144_1573))
in (FStar_Syntax_Syntax.new_bv _144_1574 t1))
in (
# 2223 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2224 "FStar.TypeChecker.Rel.fst"
let p = (let _144_1578 = (let _144_1576 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _144_1575 -> Some (_144_1575)) _144_1576))
in (let _144_1577 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _144_1578 _144_1577)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2225 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2228 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2228 "FStar.TypeChecker.Rel.fst"
let _55_3255 = probs
in {attempting = _55_3255.attempting; wl_deferred = _55_3255.wl_deferred; ctr = _55_3255.ctr; defer_ok = false; smt_ok = _55_3255.smt_ok; tcenv = _55_3255.tcenv})
end else begin
probs
end
in (
# 2229 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2230 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2233 "FStar.TypeChecker.Rel.fst"
let _55_3262 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2236 "FStar.TypeChecker.Rel.fst"
let _55_3268 = (FStar_Unionfind.rollback tx)
in (
# 2237 "FStar.TypeChecker.Rel.fst"
let _55_3270 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _144_1590 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _144_1590))
end else begin
()
end
in (err (d, s))))
end)))))

# 2239 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2244 "FStar.TypeChecker.Rel.fst"
let _55_3277 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _144_1595 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _144_1595))
end else begin
()
end
in (
# 2245 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2246 "FStar.TypeChecker.Rel.fst"
let _55_3280 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _144_1596 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _144_1596))
end else begin
()
end
in (
# 2247 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _144_1597 = (FStar_Syntax_Util.unmeta f)
in _144_1597.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3285 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2250 "FStar.TypeChecker.Rel.fst"
let _55_3287 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3287.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3287.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3287.FStar_TypeChecker_Env.implicits})))))
end))

# 2250 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _144_1609 = (let _144_1608 = (let _144_1607 = (let _144_1606 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _144_1606 (fun _144_1605 -> FStar_TypeChecker_Common.NonTrivial (_144_1605))))
in {FStar_TypeChecker_Env.guard_f = _144_1607; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _144_1608))
in (FStar_All.pipe_left (fun _144_1604 -> Some (_144_1604)) _144_1609))
end))

# 2255 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2258 "FStar.TypeChecker.Rel.fst"
let _55_3298 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1617 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1616 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _144_1617 _144_1616)))
end else begin
()
end
in (
# 2260 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_1620 = (let _144_1619 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _144_1619))
in (FStar_All.pipe_left (fun _144_1618 -> FStar_TypeChecker_Common.TProb (_144_1618)) _144_1620))
in (
# 2261 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1622 = (solve_and_commit env (singleton env prob) (fun _55_3301 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1622))
in g))))

# 2262 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _144_1632 = (let _144_1631 = (let _144_1630 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _144_1629 = (FStar_TypeChecker_Env.get_range env)
in (_144_1630, _144_1629)))
in FStar_Syntax_Syntax.Error (_144_1631))
in (Prims.raise _144_1632))
end
| Some (g) -> begin
(
# 2268 "FStar.TypeChecker.Rel.fst"
let _55_3310 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1635 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1634 = (FStar_Syntax_Print.term_to_string t2)
in (let _144_1633 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _144_1635 _144_1634 _144_1633))))
end else begin
()
end
in g)
end))

# 2273 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2276 "FStar.TypeChecker.Rel.fst"
let _55_3315 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1643 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _144_1642 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _144_1643 _144_1642)))
end else begin
()
end
in (
# 2278 "FStar.TypeChecker.Rel.fst"
let _55_3319 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3319) with
| (prob, x) -> begin
(
# 2279 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1645 = (solve_and_commit env (singleton env prob) (fun _55_3320 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1645))
in (
# 2280 "FStar.TypeChecker.Rel.fst"
let _55_3323 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _144_1649 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _144_1648 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _144_1647 = (let _144_1646 = (FStar_Util.must g)
in (guard_to_string env _144_1646))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _144_1649 _144_1648 _144_1647))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2286 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _144_1656 = (let _144_1655 = (let _144_1654 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _144_1653 = (FStar_TypeChecker_Env.get_range env)
in (_144_1654, _144_1653)))
in FStar_Syntax_Syntax.Error (_144_1655))
in (Prims.raise _144_1656)))

# 2289 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2293 "FStar.TypeChecker.Rel.fst"
let _55_3331 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1664 = (FStar_Syntax_Print.comp_to_string c1)
in (let _144_1663 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _144_1664 _144_1663)))
end else begin
()
end
in (
# 2295 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2296 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_1667 = (let _144_1666 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _144_1666 "sub_comp"))
in (FStar_All.pipe_left (fun _144_1665 -> FStar_TypeChecker_Common.CProb (_144_1665)) _144_1667))
in (let _144_1669 = (solve_and_commit env (singleton env prob) (fun _55_3335 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1669))))))

# 2297 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2301 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2302 "FStar.TypeChecker.Rel.fst"
let _55_3344 = (FStar_Unionfind.rollback tx)
in (
# 2303 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _144_1687 = (let _144_1686 = (let _144_1685 = (let _144_1683 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_1682 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _144_1683 _144_1682 msg)))
in (let _144_1684 = (FStar_TypeChecker_Env.get_range env)
in (_144_1685, _144_1684)))
in FStar_Syntax_Syntax.Error (_144_1686))
in (Prims.raise _144_1687)))))
in (
# 2312 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2315 "FStar.TypeChecker.Rel.fst"
let _55_3360 = hd
in (match (_55_3360) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _144_1694 = (insert uv u1 tl)
in (hd)::_144_1694)
end
end))
end))
in (
# 2320 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2323 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2326 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _144_1699 = (insert uv u1 out)
in (group_by _144_1699 rest))
end)
end
| _55_3375 -> begin
None
end))
end))
in (
# 2333 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _55_3377 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3380 -> begin
(
# 2338 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2338 "FStar.TypeChecker.Rel.fst"
let _55_3381 = (empty_worklist env)
in {attempting = _55_3381.attempting; wl_deferred = _55_3381.wl_deferred; ctr = _55_3381.ctr; defer_ok = true; smt_ok = _55_3381.smt_ok; tcenv = _55_3381.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3386 -> (match (_55_3386) with
| (u1, u2) -> begin
(
# 2340 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2341 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3391 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2347 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3401 -> begin
(u1)::[]
end)
in (
# 2350 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3406 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2356 "FStar.TypeChecker.Rel.fst"
let _55_3413 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3413) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2358 "FStar.TypeChecker.Rel.fst"
let _55_3417 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3417) with
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
| USolved (_55_3419) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2368 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2368 "FStar.TypeChecker.Rel.fst"
let _55_3423 = (empty_worklist env)
in {attempting = _55_3423.attempting; wl_deferred = _55_3423.wl_deferred; ctr = _55_3423.ctr; defer_ok = false; smt_ok = _55_3423.smt_ok; tcenv = _55_3423.tcenv})
in (
# 2369 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _55_3438 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2379 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2382 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2383 "FStar.TypeChecker.Rel.fst"
let _55_3443 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2384 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2387 "FStar.TypeChecker.Rel.fst"
let fail = (fun _55_3450 -> (match (_55_3450) with
| (d, s) -> begin
(
# 2388 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2390 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2391 "FStar.TypeChecker.Rel.fst"
let _55_3453 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1720 = (wl_to_string wl)
in (let _144_1719 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _144_1720 _144_1719)))
end else begin
()
end
in (
# 2393 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2394 "FStar.TypeChecker.Rel.fst"
let _55_3457 = g
in {FStar_TypeChecker_Env.guard_f = _55_3457.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3457.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3457.FStar_TypeChecker_Env.implicits})
end
| _55_3460 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2396 "FStar.TypeChecker.Rel.fst"
let _55_3462 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2397 "FStar.TypeChecker.Rel.fst"
let _55_3464 = g
in {FStar_TypeChecker_Env.guard_f = _55_3464.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3464.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3464.FStar_TypeChecker_Env.implicits})))))))

# 2397 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2400 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2401 "FStar.TypeChecker.Rel.fst"
let _55_3479 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2405 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2409 "FStar.TypeChecker.Rel.fst"
let _55_3477 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1737 = (FStar_TypeChecker_Env.get_range env)
in (let _144_1736 = (let _144_1735 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _144_1735))
in (FStar_TypeChecker_Errors.diag _144_1737 _144_1736)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2414 "FStar.TypeChecker.Rel.fst"
let _55_3481 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3481.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3481.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3481.FStar_TypeChecker_Env.implicits}))))

# 2414 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2416 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2419 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3490 -> begin
false
end))
in (
# 2422 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _55_3494 implicits -> (match (_55_3494) with
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
# 2426 "FStar.TypeChecker.Rel.fst"
let _55_3507 = hd
in (match (_55_3507) with
| (_55_3501, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2429 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2430 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2431 "FStar.TypeChecker.Rel.fst"
let _55_3510 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1753 = (FStar_Syntax_Print.uvar_to_string u)
in (let _144_1752 = (FStar_Syntax_Print.term_to_string tm)
in (let _144_1751 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _144_1753 _144_1752 _144_1751))))
end else begin
()
end
in (
# 2434 "FStar.TypeChecker.Rel.fst"
let _55_3519 = (env.FStar_TypeChecker_Env.type_of (
# 2434 "FStar.TypeChecker.Rel.fst"
let _55_3512 = env
in {FStar_TypeChecker_Env.solver = _55_3512.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3512.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3512.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3512.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3512.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3512.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3512.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3512.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3512.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3512.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3512.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3512.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3512.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3512.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3512.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3512.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3512.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3512.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _55_3512.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3512.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3519) with
| (_55_3515, _55_3517, g) -> begin
(
# 2435 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2436 "FStar.TypeChecker.Rel.fst"
let _55_3520 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3520.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3520.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3520.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2438 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _55_3523 -> (match (()) with
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
# 2440 "FStar.TypeChecker.Rel.fst"
let _55_3525 = g
in (let _144_1757 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3525.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3525.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3525.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _144_1757})))))

# 2440 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2443 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1762 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _144_1762 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _144_1763 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _144_1763))
end
| (reason, _55_3535, _55_3537, e, t, r)::_55_3532 -> begin
(let _144_1768 = (let _144_1767 = (let _144_1766 = (let _144_1765 = (FStar_Syntax_Print.term_to_string t)
in (let _144_1764 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _144_1765 _144_1764 reason)))
in (_144_1766, r))
in FStar_Syntax_Syntax.Error (_144_1767))
in (Prims.raise _144_1768))
end)))

# 2452 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2456 "FStar.TypeChecker.Rel.fst"
let _55_3545 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3545.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3545.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _55_3545.FStar_TypeChecker_Env.implicits}))





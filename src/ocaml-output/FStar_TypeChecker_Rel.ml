
open Prims
# 60 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _155_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _155_8 Prims.op_Negation)))))
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
| _66_40 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _155_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _155_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _155_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_155_10, uv)))))
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
| TERM (_66_46) -> begin
_66_46
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_66_49) -> begin
_66_49
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
| Success (_66_59) -> begin
_66_59
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_66_62) -> begin
_66_62
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
let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _66_1 -> (match (_66_1) with
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
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _66_2 -> (match (_66_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _155_109 = (let _155_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _155_107 = (let _155_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _155_105 = (let _155_104 = (let _155_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _155_102 = (let _155_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _155_100 = (let _155_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _155_98 = (let _155_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_155_97)::[])
in (_155_99)::_155_98))
in (_155_101)::_155_100))
in (_155_103)::_155_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_155_104)
in (_155_106)::_155_105))
in (_155_108)::_155_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _155_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _155_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _155_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _155_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _155_110)))
end))

# 138 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _66_3 -> (match (_66_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _155_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _155_116 FStar_Util.string_of_int))
end
in (let _155_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _155_117)))
end
| TERM ((u, _66_86), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _155_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _155_118 FStar_Util.string_of_int))
end
in (let _155_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _155_119)))
end))

# 147 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _155_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _155_124 (FStar_String.concat ", "))))

# 148 "FStar.TypeChecker.Rel.fst"
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _155_128 = (let _155_127 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _155_127 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _155_128 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _155_131 = (FStar_All.pipe_right args (FStar_List.map (fun _66_99 -> (match (_66_99) with
| (x, _66_98) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _155_131 (FStar_String.concat " "))))

# 150 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 166 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _66_103 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _66_103.wl_deferred; ctr = _66_103.ctr; defer_ok = _66_103.defer_ok; smt_ok = _66_103.smt_ok; tcenv = _66_103.tcenv}))

# 167 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _66_107 = (empty_worklist env)
in (let _155_140 = (FStar_List.map Prims.snd g)
in {attempting = _155_140; wl_deferred = _66_107.wl_deferred; ctr = _66_107.ctr; defer_ok = false; smt_ok = _66_107.smt_ok; tcenv = _66_107.tcenv})))

# 168 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _66_112 = wl
in {attempting = _66_112.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _66_112.ctr; defer_ok = _66_112.defer_ok; smt_ok = _66_112.smt_ok; tcenv = _66_112.tcenv}))

# 169 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _66_116 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _66_116.wl_deferred; ctr = _66_116.ctr; defer_ok = _66_116.defer_ok; smt_ok = _66_116.smt_ok; tcenv = _66_116.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _66_121 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_157 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _155_157))
end else begin
()
end
in Failed ((prob, reason))))

# 175 "FStar.TypeChecker.Rel.fst"
let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _66_4 -> (match (_66_4) with
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
let _66_128 = p
in {FStar_TypeChecker_Common.pid = _66_128.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _66_128.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_128.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_128.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_128.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_128.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_128.FStar_TypeChecker_Common.rank}))

# 187 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _66_5 -> (match (_66_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _155_164 -> FStar_TypeChecker_Common.TProb (_155_164)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _155_165 -> FStar_TypeChecker_Common.CProb (_155_165)))
end))

# 191 "FStar.TypeChecker.Rel.fst"
let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _66_6 -> (match (_66_6) with
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
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _66_7 -> (match (_66_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 198 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _66_8 -> (match (_66_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 201 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _66_9 -> (match (_66_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 204 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _66_10 -> (match (_66_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 207 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _66_11 -> (match (_66_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 210 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _66_12 -> (match (_66_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 213 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _66_13 -> (match (_66_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _155_184 -> FStar_TypeChecker_Common.TProb (_155_184)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _155_185 -> FStar_TypeChecker_Common.CProb (_155_185)) (invert p))
end))

# 216 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 217 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _66_178 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _66_179 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 220 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _155_198 = (next_pid ())
in (let _155_197 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _155_198; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _155_197; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 233 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _155_208 = (next_pid ())
in (let _155_207 = (let _155_206 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _155_206 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _155_208; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _155_207; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 247 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _155_215 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _155_215; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 259 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 263 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _155_227 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _155_226 = (prob_to_string env d)
in (let _155_225 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _155_227 _155_226 _155_225 s)))))

# 269 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _66_14 -> (match (_66_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _66_220 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _66_223), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 284 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _66_15 -> (match (_66_15) with
| UNIV (_66_232) -> begin
None
end
| TERM ((u, _66_236), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 288 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _66_16 -> (match (_66_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _66_249 -> begin
None
end))))

# 292 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _155_246 = (let _155_245 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _155_245))
in (FStar_Syntax_Subst.compress _155_246)))

# 302 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _155_251 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _155_251)))

# 303 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _155_254 = (sn env (Prims.fst t))
in (_155_254, (Prims.snd t))))

# 304 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _66_260 -> (match (_66_260) with
| (x, imp) -> begin
(let _155_261 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _66_261 = x
in (let _155_260 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_261.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_261.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_260}))
in (_155_261, imp))
end)))))

# 306 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _155_268 = (aux u)
in FStar_Syntax_Syntax.U_succ (_155_268))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _155_269 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_155_269))
end
| _66_273 -> begin
u
end)))
in (let _155_270 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _155_270))))

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
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _66_293; FStar_Syntax_Syntax.pos = _66_291; FStar_Syntax_Syntax.vars = _66_289} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _155_284 = (let _155_283 = (FStar_Syntax_Print.term_to_string tt)
in (let _155_282 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _155_283 _155_282)))
in (FStar_All.failwith _155_284))
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
in (match ((let _155_285 = (FStar_Syntax_Subst.compress t1')
in _155_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_66_311) -> begin
(aux true t1')
end
| _66_314 -> begin
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
(let _155_288 = (let _155_287 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_286 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _155_287 _155_286)))
in (FStar_All.failwith _155_288))
end))
in (let _155_289 = (whnf env t1)
in (aux false _155_289))))

# 365 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _155_294 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _155_294 Prims.fst)))

# 367 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _155_297 = (FStar_Syntax_Syntax.null_bv t)
in (_155_297, FStar_Syntax_Util.t_true)))

# 369 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _66_360 = (base_and_refinement env wl t)
in (match (_66_360) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

# 375 "FStar.TypeChecker.Rel.fst"
let force_refinement = (fun _66_368 -> (match (_66_368) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _66_376 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_66_376) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 381 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _66_17 -> (match (_66_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _155_310 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _155_309 = (let _155_306 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _155_306))
in (let _155_308 = (let _155_307 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _155_307))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _155_310 _155_309 (rel_to_string p.FStar_TypeChecker_Common.relation) _155_308))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _155_313 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _155_312 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _155_311 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _155_313 _155_312 (rel_to_string p.FStar_TypeChecker_Common.relation) _155_311))))
end))

# 404 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _155_319 = (let _155_318 = (let _155_317 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _66_389 -> (match (_66_389) with
| (_66_385, _66_387, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _155_317))
in (FStar_List.map (wl_prob_to_string wl) _155_318))
in (FStar_All.pipe_right _155_319 (FStar_String.concat "\n\t"))))

# 407 "FStar.TypeChecker.Rel.fst"
let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (
# 417 "FStar.TypeChecker.Rel.fst"
let _66_408 = (match ((let _155_326 = (FStar_Syntax_Subst.compress k)
in _155_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _155_327 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _155_327))
end else begin
(
# 421 "FStar.TypeChecker.Rel.fst"
let _66_399 = (FStar_Syntax_Util.abs_formals t)
in (match (_66_399) with
| (ys', t) -> begin
(let _155_328 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _155_328))
end))
end
end
| _66_401 -> begin
(let _155_330 = (let _155_329 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _155_329))
in ((ys, t), _155_330))
end)
in (match (_66_408) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t None)
end else begin
(
# 426 "FStar.TypeChecker.Rel.fst"
let c = (let _155_331 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _155_331 c))
in (let _155_333 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _155_332 -> Some (_155_332)))
in (FStar_Syntax_Util.abs ys t _155_333)))
end
end)))

# 427 "FStar.TypeChecker.Rel.fst"
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
let _66_422 = (p_guard prob)
in (match (_66_422) with
| (_66_420, uv) -> begin
(
# 434 "FStar.TypeChecker.Rel.fst"
let _66_435 = (match ((let _155_344 = (FStar_Syntax_Subst.compress uv)
in _155_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 436 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 437 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _155_346 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _155_346 Prims.op_Negation)))))
in (
# 438 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs k bs phi)
in (
# 439 "FStar.TypeChecker.Rel.fst"
let _66_431 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _155_349 = (FStar_Util.string_of_int (p_pid prob))
in (let _155_348 = (FStar_Syntax_Print.term_to_string uv)
in (let _155_347 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _155_349 _155_348 _155_347))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _66_434 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 446 "FStar.TypeChecker.Rel.fst"
let _66_437 = (commit uvis)
in (
# 447 "FStar.TypeChecker.Rel.fst"
let _66_439 = wl
in {attempting = _66_439.attempting; wl_deferred = _66_439.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _66_439.defer_ok; smt_ok = _66_439.smt_ok; tcenv = _66_439.tcenv})))
end))))

# 447 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 450 "FStar.TypeChecker.Rel.fst"
let _66_444 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_358 = (FStar_Util.string_of_int pid)
in (let _155_357 = (let _155_356 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _155_356 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _155_358 _155_357)))
end else begin
()
end
in (
# 452 "FStar.TypeChecker.Rel.fst"
let _66_446 = (commit sol)
in (
# 453 "FStar.TypeChecker.Rel.fst"
let _66_448 = wl
in {attempting = _66_448.attempting; wl_deferred = _66_448.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _66_448.defer_ok; smt_ok = _66_448.smt_ok; tcenv = _66_448.tcenv}))))

# 453 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 456 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_66_458, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _155_371 = (FStar_Syntax_Util.mk_conj t f)
in Some (_155_371))
end))
in (
# 460 "FStar.TypeChecker.Rel.fst"
let _66_470 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_374 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _155_373 = (let _155_372 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _155_372 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _155_374 _155_373)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 462 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _155_384 = (let _155_382 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _155_382 FStar_Util.set_elements))
in (FStar_All.pipe_right _155_384 (FStar_Util.for_some (fun _66_479 -> (match (_66_479) with
| (uv, _66_478) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 476 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 479 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 480 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _155_391 = (let _155_390 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _155_389 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _155_390 _155_389)))
in Some (_155_391))
end
in (occurs_ok, msg))))

# 485 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 488 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 489 "FStar.TypeChecker.Rel.fst"
let _66_494 = (occurs_check env wl uk t)
in (match (_66_494) with
| (occurs_ok, msg) -> begin
(let _155_397 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _155_397, (msg, fvs, fvs_t)))
end))))

# 490 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 493 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 495 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 496 "FStar.TypeChecker.Rel.fst"
let _66_512 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _66_504 _66_507 -> (match ((_66_504, _66_507)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _155_406 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _155_406)) then begin
(isect, isect_set)
end else begin
(
# 502 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _155_407 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _155_407))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_66_512) with
| (isect, _66_511) -> begin
(FStar_List.rev isect)
end)))))

# 507 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _66_518 _66_522 -> (match ((_66_518, _66_522)) with
| ((a, _66_517), (b, _66_521)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 511 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 514 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _66_532 -> (match (_66_532) with
| (b, _66_531) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _66_534 -> begin
None
end)))

# 521 "FStar.TypeChecker.Rel.fst"
let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 527 "FStar.TypeChecker.Rel.fst"
let _66_543 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_422 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _155_422))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 529 "FStar.TypeChecker.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _66_557; FStar_Syntax_Syntax.pos = _66_555; FStar_Syntax_Syntax.vars = _66_553}, args) -> begin
(t, uv, k, args)
end
| _66_567 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 534 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 537 "FStar.TypeChecker.Rel.fst"
let _66_574 = (destruct_flex_t t)
in (match (_66_574) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _66_578 -> begin
((t, uv, k, args), None)
end)
end)))

# 540 "FStar.TypeChecker.Rel.fst"
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
| MisMatch (_66_581) -> begin
_66_581
end))

# 614 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _66_18 -> (match (_66_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _66_588 -> begin
HeadMatch
end))

# 618 "FStar.TypeChecker.Rel.fst"
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

# 625 "FStar.TypeChecker.Rel.fst"
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

# 646 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _66_674), FStar_Syntax_Syntax.Tm_uinst (g, _66_679)) -> begin
(let _155_458 = (head_matches env f g)
in (FStar_All.pipe_right _155_458 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _66_690), FStar_Syntax_Syntax.Tm_uvar (uv', _66_695)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _66_701), FStar_Syntax_Syntax.Tm_refine (y, _66_706)) -> begin
(let _155_459 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _155_459 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _66_712), _66_716) -> begin
(let _155_460 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _155_460 head_match))
end
| (_66_719, FStar_Syntax_Syntax.Tm_refine (x, _66_722)) -> begin
(let _155_461 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _155_461 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _66_742), FStar_Syntax_Syntax.Tm_app (head', _66_747)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _66_753), _66_757) -> begin
(head_matches env head t2)
end
| (_66_760, FStar_Syntax_Syntax.Tm_app (head, _66_763)) -> begin
(head_matches env t1 head)
end
| _66_768 -> begin
(let _155_464 = (let _155_463 = (delta_depth_of_term env t1)
in (let _155_462 = (delta_depth_of_term env t2)
in (_155_463, _155_462)))
in MisMatch (_155_464))
end))))

# 671 "FStar.TypeChecker.Rel.fst"
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
let _66_819 = if d1_greater_than_d2 then begin
(
# 698 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 700 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _155_485 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _155_485)))
end
in (match (_66_819) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_66_821) -> begin
(fail r)
end
| _66_824 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 707 "FStar.TypeChecker.Rel.fst"
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
| T (_66_827) -> begin
_66_827
end))

# 711 "FStar.TypeChecker.Rel.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_66_830) -> begin
_66_830
end))

# 711 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 712 "FStar.TypeChecker.Rel.fst"
let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (
# 715 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 716 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_66_837) -> begin
false
end
| _66_840 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 721 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 722 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_66_850, imp), T (t)) -> begin
(t, imp)
end
| _66_857 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 727 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _66_862 -> (match (_66_862) with
| (t, _66_861) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 733 "FStar.TypeChecker.Rel.fst"
let fail = (fun _66_869 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 734 "FStar.TypeChecker.Rel.fst"
let _66_872 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_66_872) with
| (bs, c) -> begin
(
# 736 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 737 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 738 "FStar.TypeChecker.Rel.fst"
let _66_889 = x
in {FStar_Syntax_Syntax.ppname = _66_889.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_889.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _66_897 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 743 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _66_19 -> (match (_66_19) with
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
in (let _155_567 = (decompose [] bs)
in (rebuild, matches, _155_567))))
end)))
end
| _66_907 -> begin
(
# 754 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _66_20 -> (match (_66_20) with
| [] -> begin
t
end
| _66_911 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 758 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _66_21 -> (match (_66_21) with
| T (t) -> begin
t
end
| _66_918 -> begin
(FStar_All.failwith "Impossible")
end))

# 762 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _66_22 -> (match (_66_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _66_923 -> begin
(FStar_All.failwith "Impossible")
end))

# 766 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 773 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 774 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 775 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_66_936, variance, T (ti)) -> begin
(
# 778 "FStar.TypeChecker.Rel.fst"
let k = (
# 779 "FStar.TypeChecker.Rel.fst"
let _66_944 = (FStar_Syntax_Util.type_u ())
in (match (_66_944) with
| (t, _66_943) -> begin
(let _155_589 = (new_uvar r scope t)
in (Prims.fst _155_589))
end))
in (
# 781 "FStar.TypeChecker.Rel.fst"
let _66_948 = (new_uvar r scope k)
in (match (_66_948) with
| (gi_xs, gi) -> begin
(
# 782 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _66_951 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _155_592 = (let _155_591 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _155_590 -> FStar_TypeChecker_Common.TProb (_155_590)) _155_591))
in (T (gi_xs), _155_592)))
end)))
end
| (_66_954, _66_956, C (_66_958)) -> begin
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
let _66_1036 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _66_976; FStar_Syntax_Syntax.pos = _66_974; FStar_Syntax_Syntax.vars = _66_972})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _155_601 = (let _155_600 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _155_599 -> C (_155_599)) _155_600))
in (_155_601, (prob)::[]))
end
| _66_987 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _66_995; FStar_Syntax_Syntax.pos = _66_993; FStar_Syntax_Syntax.vars = _66_991})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _155_604 = (let _155_603 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _155_602 -> C (_155_602)) _155_603))
in (_155_604, (prob)::[]))
end
| _66_1006 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_66_1008, _66_1010, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _66_1016; FStar_Syntax_Syntax.pos = _66_1014; FStar_Syntax_Syntax.vars = _66_1012})) -> begin
(
# 808 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 809 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 810 "FStar.TypeChecker.Rel.fst"
let _66_1027 = (let _155_606 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _155_606 FStar_List.unzip))
in (match (_66_1027) with
| (tcs, sub_probs) -> begin
(
# 811 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _155_611 = (let _155_610 = (let _155_607 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _155_607 un_T))
in (let _155_609 = (let _155_608 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _155_608 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _155_610; FStar_Syntax_Syntax.effect_args = _155_609; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _155_611))
in (C (gi_xs), sub_probs))
end))))
end
| _66_1030 -> begin
(
# 820 "FStar.TypeChecker.Rel.fst"
let _66_1033 = (sub_prob scope args q)
in (match (_66_1033) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_66_1036) with
| (tc, probs) -> begin
(
# 823 "FStar.TypeChecker.Rel.fst"
let _66_1049 = (match (q) with
| (Some (b), _66_1040, _66_1042) -> begin
(let _155_613 = (let _155_612 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_155_612)::args)
in (Some (b), (b)::scope, _155_613))
end
| _66_1045 -> begin
(None, scope, args)
end)
in (match (_66_1049) with
| (bopt, scope, args) -> begin
(
# 827 "FStar.TypeChecker.Rel.fst"
let _66_1053 = (aux scope args qs)
in (match (_66_1053) with
| (sub_probs, tcs, f) -> begin
(
# 828 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _155_616 = (let _155_615 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_155_615)
in (FStar_Syntax_Util.mk_conj_l _155_616))
end
| Some (b) -> begin
(let _155_620 = (let _155_619 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _155_618 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_155_619)::_155_618))
in (FStar_Syntax_Util.mk_conj_l _155_620))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 834 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _66_1081), FStar_Syntax_Syntax.Tm_uvar (u2, _66_1086)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _66_1100 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _66_1106 _66_1110 -> (match ((_66_1106, _66_1110)) with
| ((a1, _66_1105), (a2, _66_1109)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 857 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 862 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 865 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 867 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 868 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 869 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 870 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 871 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 872 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 873 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 874 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 875 "FStar.TypeChecker.Rel.fst"
let _66_1113 = p
in (let _155_642 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _155_641 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _66_1113.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _155_642; FStar_TypeChecker_Common.relation = _66_1113.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _155_641; FStar_TypeChecker_Common.element = _66_1113.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1113.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1113.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1113.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1113.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_1113.FStar_TypeChecker_Common.rank}))))

# 875 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _155_648 = (compress_tprob wl p)
in (FStar_All.pipe_right _155_648 (fun _155_647 -> FStar_TypeChecker_Common.TProb (_155_647))))
end
| FStar_TypeChecker_Common.CProb (_66_1120) -> begin
p
end))

# 879 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 885 "FStar.TypeChecker.Rel.fst"
let prob = (let _155_653 = (compress_prob wl pr)
in (FStar_All.pipe_right _155_653 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let _66_1130 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_66_1130) with
| (lh, _66_1129) -> begin
(
# 889 "FStar.TypeChecker.Rel.fst"
let _66_1134 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_66_1134) with
| (rh, _66_1133) -> begin
(
# 890 "FStar.TypeChecker.Rel.fst"
let _66_1190 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_66_1136), FStar_Syntax_Syntax.Tm_uvar (_66_1139)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_66_1155), _66_1158) -> begin
(
# 897 "FStar.TypeChecker.Rel.fst"
let _66_1162 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_66_1162) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _66_1165 -> begin
(
# 901 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _155_655 = (
# 905 "FStar.TypeChecker.Rel.fst"
let _66_1167 = tp
in (let _155_654 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _66_1167.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_1167.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_1167.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _155_654; FStar_TypeChecker_Common.element = _66_1167.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1167.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1167.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1167.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1167.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_1167.FStar_TypeChecker_Common.rank}))
in (rank, _155_655)))
end)
end))
end
| (_66_1170, FStar_Syntax_Syntax.Tm_uvar (_66_1172)) -> begin
(
# 909 "FStar.TypeChecker.Rel.fst"
let _66_1177 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_66_1177) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _66_1180 -> begin
(let _155_657 = (
# 912 "FStar.TypeChecker.Rel.fst"
let _66_1181 = tp
in (let _155_656 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _66_1181.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _155_656; FStar_TypeChecker_Common.relation = _66_1181.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_1181.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_1181.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1181.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1181.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1181.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1181.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_1181.FStar_TypeChecker_Common.rank}))
in (refine_flex, _155_657))
end)
end))
end
| (_66_1184, _66_1186) -> begin
(rigid_rigid, tp)
end)
in (match (_66_1190) with
| (rank, tp) -> begin
(let _155_659 = (FStar_All.pipe_right (
# 917 "FStar.TypeChecker.Rel.fst"
let _66_1191 = tp
in {FStar_TypeChecker_Common.pid = _66_1191.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_1191.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_1191.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_1191.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_1191.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1191.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1191.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1191.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1191.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _155_658 -> FStar_TypeChecker_Common.TProb (_155_658)))
in (rank, _155_659))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _155_661 = (FStar_All.pipe_right (
# 919 "FStar.TypeChecker.Rel.fst"
let _66_1195 = cp
in {FStar_TypeChecker_Common.pid = _66_1195.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_1195.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_1195.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_1195.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_1195.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1195.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1195.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1195.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1195.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _155_660 -> FStar_TypeChecker_Common.CProb (_155_660)))
in (rigid_rigid, _155_661))
end)))

# 919 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 925 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _66_1202 probs -> (match (_66_1202) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 928 "FStar.TypeChecker.Rel.fst"
let _66_1210 = (rank wl hd)
in (match (_66_1210) with
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

# 941 "FStar.TypeChecker.Rel.fst"
let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

# 942 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 948 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 949 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 950 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 948 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_66_1221) -> begin
_66_1221
end))

# 949 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_66_1224) -> begin
_66_1224
end))

# 950 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_66_1227) -> begin
_66_1227
end))

# 950 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 953 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 954 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 955 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 958 "FStar.TypeChecker.Rel.fst"
let _66_1243 = (FStar_Syntax_Util.univ_kernel u)
in (match (_66_1243) with
| (k, _66_1242) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _66_1247 -> begin
false
end)
end)))))
end
| _66_1249 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 964 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(
# 968 "FStar.TypeChecker.Rel.fst"
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
| _66_1274 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _155_741 = (let _155_740 = (FStar_Syntax_Print.univ_to_string u1)
in (let _155_739 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _155_740 _155_739)))
in UFailed (_155_741))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 981 "FStar.TypeChecker.Rel.fst"
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
| _66_1292 -> begin
(let _155_748 = (let _155_747 = (FStar_Syntax_Print.univ_to_string u1)
in (let _155_746 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _155_747 _155_746 msg)))
in UFailed (_155_748))
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
# 1013 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 1018 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _155_751 = (let _155_750 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _155_749 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _155_750 _155_749)))
in (try_umax_components u1 u2 _155_751))
end else begin
(let _155_752 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_155_752))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(
# 1028 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1029 "FStar.TypeChecker.Rel.fst"
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

# 1040 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1047 "FStar.TypeChecker.Rel.fst"
let _66_1389 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_798 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _155_798))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1051 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1051 "FStar.TypeChecker.Rel.fst"
let _66_1396 = probs
in {attempting = tl; wl_deferred = _66_1396.wl_deferred; ctr = _66_1396.ctr; defer_ok = _66_1396.defer_ok; smt_ok = _66_1396.smt_ok; tcenv = _66_1396.tcenv})
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
| (None, _66_1411, _66_1413) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _66_1417 -> begin
(
# 1078 "FStar.TypeChecker.Rel.fst"
let _66_1426 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _66_1423 -> (match (_66_1423) with
| (c, _66_1420, _66_1422) -> begin
(c < probs.ctr)
end))))
in (match (_66_1426) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _155_801 = (FStar_List.map (fun _66_1432 -> (match (_66_1432) with
| (_66_1429, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_155_801))
end
| _66_1434 -> begin
(let _155_804 = (
# 1084 "FStar.TypeChecker.Rel.fst"
let _66_1435 = probs
in (let _155_803 = (FStar_All.pipe_right attempt (FStar_List.map (fun _66_1442 -> (match (_66_1442) with
| (_66_1438, _66_1440, y) -> begin
y
end))))
in {attempting = _155_803; wl_deferred = rest; ctr = _66_1435.ctr; defer_ok = _66_1435.defer_ok; smt_ok = _66_1435.smt_ok; tcenv = _66_1435.tcenv}))
in (solve env _155_804))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _155_810 = (solve_prob orig None [] wl)
in (solve env _155_810))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1098 "FStar.TypeChecker.Rel.fst"
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
| _66_1477 -> begin
UFailed ("Unequal number of universes")
end))
in (
# 1111 "FStar.TypeChecker.Rel.fst"
let t1 = (whnf env t1)
in (
# 1112 "FStar.TypeChecker.Rel.fst"
let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _66_1485; FStar_Syntax_Syntax.pos = _66_1483; FStar_Syntax_Syntax.vars = _66_1481}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _66_1497; FStar_Syntax_Syntax.pos = _66_1495; FStar_Syntax_Syntax.vars = _66_1493}, us2)) -> begin
(
# 1115 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1116 "FStar.TypeChecker.Rel.fst"
let _66_1506 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _66_1521 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1129 "FStar.TypeChecker.Rel.fst"
let _66_1526 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_826 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _155_826 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1139 "FStar.TypeChecker.Rel.fst"
let _66_1531 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_830 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _155_830))
end else begin
()
end
in (
# 1141 "FStar.TypeChecker.Rel.fst"
let _66_1535 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_66_1535) with
| (u, args) -> begin
(
# 1143 "FStar.TypeChecker.Rel.fst"
let disjoin = (fun t1 t2 -> (
# 1144 "FStar.TypeChecker.Rel.fst"
let _66_1541 = (head_matches_delta env () t1 t2)
in (match (_66_1541) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_66_1543) -> begin
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
# 1157 "FStar.TypeChecker.Rel.fst"
let _66_1559 = (match (ts) with
| Some (t1, t2) -> begin
(let _155_836 = (FStar_Syntax_Subst.compress t1)
in (let _155_835 = (FStar_Syntax_Subst.compress t2)
in (_155_836, _155_835)))
end
| None -> begin
(let _155_838 = (FStar_Syntax_Subst.compress t1)
in (let _155_837 = (FStar_Syntax_Subst.compress t2)
in (_155_838, _155_837)))
end)
in (match (_66_1559) with
| (t1, t2) -> begin
(
# 1160 "FStar.TypeChecker.Rel.fst"
let eq_prob = (fun t1 t2 -> (let _155_844 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _155_843 -> FStar_TypeChecker_Common.TProb (_155_843)) _155_844)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _155_851 = (let _155_850 = (let _155_847 = (let _155_846 = (let _155_845 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _155_845))
in FStar_Syntax_Syntax.Tm_refine (_155_846))
in (FStar_Syntax_Syntax.mk _155_847 None t1.FStar_Syntax_Syntax.pos))
in (let _155_849 = (let _155_848 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_155_848)::[])
in (_155_850, _155_849)))
in Some (_155_851))
end
| (_66_1573, FStar_Syntax_Syntax.Tm_refine (x, _66_1576)) -> begin
(let _155_854 = (let _155_853 = (let _155_852 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_155_852)::[])
in (t1, _155_853))
in Some (_155_854))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _66_1582), _66_1586) -> begin
(let _155_857 = (let _155_856 = (let _155_855 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_155_855)::[])
in (t2, _155_856))
in Some (_155_857))
end
| _66_1589 -> begin
None
end))
end))
end)
end)))
in (
# 1176 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _66_1593) -> begin
(
# 1180 "FStar.TypeChecker.Rel.fst"
let _66_1618 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _66_23 -> (match (_66_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(
# 1184 "FStar.TypeChecker.Rel.fst"
let _66_1604 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_66_1604) with
| (u', _66_1603) -> begin
(match ((let _155_859 = (whnf env u')
in _155_859.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _66_1607) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _66_1611 -> begin
false
end)
end))
end
| _66_1613 -> begin
false
end)
end
| _66_1615 -> begin
false
end))))
in (match (_66_1618) with
| (lower_bounds, rest) -> begin
(
# 1193 "FStar.TypeChecker.Rel.fst"
let rec make_lower_bound = (fun _66_1622 tps -> (match (_66_1622) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _155_864 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _155_864))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _66_1635 -> begin
None
end)
end))
in (match ((let _155_866 = (let _155_865 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_155_865, []))
in (make_lower_bound _155_866 lower_bounds))) with
| None -> begin
(
# 1204 "FStar.TypeChecker.Rel.fst"
let _66_1637 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(
# 1209 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (
# 1210 "FStar.TypeChecker.Rel.fst"
let _66_1647 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1211 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1211 "FStar.TypeChecker.Rel.fst"
let _66_1644 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _66_1644.wl_deferred; ctr = _66_1644.ctr; defer_ok = _66_1644.defer_ok; smt_ok = _66_1644.smt_ok; tcenv = _66_1644.tcenv})
in (let _155_867 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _155_867)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1213 "FStar.TypeChecker.Rel.fst"
let _66_1649 = wl
in {attempting = sub_probs; wl_deferred = _66_1649.wl_deferred; ctr = _66_1649.ctr; defer_ok = _66_1649.defer_ok; smt_ok = _66_1649.smt_ok; tcenv = _66_1649.tcenv}))) with
| Success (_66_1652) -> begin
(
# 1215 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1215 "FStar.TypeChecker.Rel.fst"
let _66_1654 = wl
in {attempting = rest; wl_deferred = _66_1654.wl_deferred; ctr = _66_1654.ctr; defer_ok = _66_1654.defer_ok; smt_ok = _66_1654.smt_ok; tcenv = _66_1654.tcenv})
in (
# 1216 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1217 "FStar.TypeChecker.Rel.fst"
let _66_1660 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _66_1663 -> begin
None
end)))
end))
end))
end
| _66_1665 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1228 "FStar.TypeChecker.Rel.fst"
let _66_1669 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_873 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _155_873))
end else begin
()
end
in (
# 1230 "FStar.TypeChecker.Rel.fst"
let _66_1673 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_66_1673) with
| (u, args) -> begin
(
# 1231 "FStar.TypeChecker.Rel.fst"
let _66_1679 = (0, 1, 2, 3, 4)
in (match (_66_1679) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1232 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1234 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1235 "FStar.TypeChecker.Rel.fst"
let _66_1688 = (FStar_Syntax_Util.head_and_args t1)
in (match (_66_1688) with
| (h1, args1) -> begin
(
# 1236 "FStar.TypeChecker.Rel.fst"
let _66_1692 = (FStar_Syntax_Util.head_and_args t2)
in (match (_66_1692) with
| (h2, _66_1691) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _155_885 = (let _155_884 = (let _155_883 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _155_882 -> FStar_TypeChecker_Common.TProb (_155_882)) _155_883))
in (_155_884)::[])
in Some (_155_885))
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
| _66_1704 -> begin
None
end)
end))
end)))
in (
# 1252 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1254 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1258 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1259 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1260 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1261 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _155_892 = (let _155_891 = (let _155_890 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _155_890))
in (_155_891, m))
in Some (_155_892))))))
end))
end
| (_66_1726, FStar_Syntax_Syntax.Tm_refine (y, _66_1729)) -> begin
(
# 1266 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _66_1739), _66_1743) -> begin
(
# 1273 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _66_1750 -> begin
(
# 1280 "FStar.TypeChecker.Rel.fst"
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
# 1286 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _66_1758) -> begin
(
# 1290 "FStar.TypeChecker.Rel.fst"
let _66_1783 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _66_24 -> (match (_66_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1294 "FStar.TypeChecker.Rel.fst"
let _66_1769 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_66_1769) with
| (u', _66_1768) -> begin
(match ((let _155_894 = (whnf env u')
in _155_894.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _66_1772) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _66_1776 -> begin
false
end)
end))
end
| _66_1778 -> begin
false
end)
end
| _66_1780 -> begin
false
end))))
in (match (_66_1783) with
| (upper_bounds, rest) -> begin
(
# 1303 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _66_1787 tps -> (match (_66_1787) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _155_899 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _155_899))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _66_1800 -> begin
None
end)
end))
in (match ((let _155_901 = (let _155_900 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_155_900, []))
in (make_upper_bound _155_901 upper_bounds))) with
| None -> begin
(
# 1314 "FStar.TypeChecker.Rel.fst"
let _66_1802 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1327 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1328 "FStar.TypeChecker.Rel.fst"
let _66_1812 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1329 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1329 "FStar.TypeChecker.Rel.fst"
let _66_1809 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _66_1809.wl_deferred; ctr = _66_1809.ctr; defer_ok = _66_1809.defer_ok; smt_ok = _66_1809.smt_ok; tcenv = _66_1809.tcenv})
in (let _155_902 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _155_902)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1331 "FStar.TypeChecker.Rel.fst"
let _66_1814 = wl
in {attempting = sub_probs; wl_deferred = _66_1814.wl_deferred; ctr = _66_1814.ctr; defer_ok = _66_1814.defer_ok; smt_ok = _66_1814.smt_ok; tcenv = _66_1814.tcenv}))) with
| Success (_66_1817) -> begin
(
# 1333 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1333 "FStar.TypeChecker.Rel.fst"
let _66_1819 = wl
in {attempting = rest; wl_deferred = _66_1819.wl_deferred; ctr = _66_1819.ctr; defer_ok = _66_1819.defer_ok; smt_ok = _66_1819.smt_ok; tcenv = _66_1819.tcenv})
in (
# 1334 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1335 "FStar.TypeChecker.Rel.fst"
let _66_1825 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _66_1828 -> begin
None
end)))
end))
end))
end
| _66_1830 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1345 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1348 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1349 "FStar.TypeChecker.Rel.fst"
let _66_1847 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_930 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _155_930))
end else begin
()
end
in (
# 1351 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1355 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1355 "FStar.TypeChecker.Rel.fst"
let _66_1861 = hd1
in (let _155_931 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_1861.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1861.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_931}))
in (
# 1356 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1356 "FStar.TypeChecker.Rel.fst"
let _66_1864 = hd2
in (let _155_932 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_1864.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1864.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _155_932}))
in (
# 1357 "FStar.TypeChecker.Rel.fst"
let prob = (let _155_935 = (let _155_934 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _155_934 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _155_933 -> FStar_TypeChecker_Common.TProb (_155_933)) _155_935))
in (
# 1358 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1359 "FStar.TypeChecker.Rel.fst"
let subst = (let _155_936 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_155_936)
in (
# 1360 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1363 "FStar.TypeChecker.Rel.fst"
let phi = (let _155_938 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _155_937 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _155_938 _155_937)))
in (
# 1364 "FStar.TypeChecker.Rel.fst"
let _66_1876 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_940 = (FStar_Syntax_Print.term_to_string phi)
in (let _155_939 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _155_940 _155_939)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _66_1880 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1373 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1377 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _155_944 = (compress_tprob wl problem)
in (solve_t' env _155_944 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1384 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1387 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1388 "FStar.TypeChecker.Rel.fst"
let _66_1908 = (head_matches_delta env wl t1 t2)
in (match (_66_1908) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_66_1910), _66_1913) -> begin
(
# 1391 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _66_1926 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1397 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1400 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1404 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _155_973 = (let _155_972 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _155_972 t2))
in (FStar_Syntax_Util.mk_forall x _155_973)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _155_974 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _155_974)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_66_1936, Some (t1, t2)) -> begin
(solve_t env (
# 1413 "FStar.TypeChecker.Rel.fst"
let _66_1942 = problem
in {FStar_TypeChecker_Common.pid = _66_1942.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _66_1942.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _66_1942.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1942.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1942.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1942.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1942.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_1942.FStar_TypeChecker_Common.rank}) wl)
end
| (_66_1945, None) -> begin
(
# 1416 "FStar.TypeChecker.Rel.fst"
let _66_1948 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_978 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_977 = (FStar_Syntax_Print.tag_of_term t1)
in (let _155_976 = (FStar_Syntax_Print.term_to_string t2)
in (let _155_975 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _155_978 _155_977 _155_976 _155_975)))))
end else begin
()
end
in (
# 1420 "FStar.TypeChecker.Rel.fst"
let _66_1952 = (FStar_Syntax_Util.head_and_args t1)
in (match (_66_1952) with
| (head1, args1) -> begin
(
# 1421 "FStar.TypeChecker.Rel.fst"
let _66_1955 = (FStar_Syntax_Util.head_and_args t2)
in (match (_66_1955) with
| (head2, args2) -> begin
(
# 1422 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _155_983 = (let _155_982 = (FStar_Syntax_Print.term_to_string head1)
in (let _155_981 = (args_to_string args1)
in (let _155_980 = (FStar_Syntax_Print.term_to_string head2)
in (let _155_979 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _155_982 _155_981 _155_980 _155_979)))))
in (giveup env _155_983 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _155_984 = (solve_prob orig None [] wl)
in (solve env _155_984))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1443 "FStar.TypeChecker.Rel.fst"
let _66_1965 = (base_and_refinement env wl t1)
in (match (_66_1965) with
| (base1, refinement1) -> begin
(
# 1444 "FStar.TypeChecker.Rel.fst"
let _66_1968 = (base_and_refinement env wl t2)
in (match (_66_1968) with
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
# 1451 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _66_1981 _66_1985 -> (match ((_66_1981, _66_1985)) with
| ((a, _66_1980), (a', _66_1984)) -> begin
(let _155_988 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _155_987 -> FStar_TypeChecker_Common.TProb (_155_987)) _155_988))
end)) args1 args2)
in (
# 1452 "FStar.TypeChecker.Rel.fst"
let formula = (let _155_990 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _155_990))
in (
# 1453 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _66_1991 -> begin
(
# 1458 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1459 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1460 "FStar.TypeChecker.Rel.fst"
let _66_1994 = problem
in {FStar_TypeChecker_Common.pid = _66_1994.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _66_1994.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _66_1994.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_1994.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_1994.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_1994.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_1994.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_1994.FStar_TypeChecker_Common.rank}) wl)))
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
# 1466 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1467 "FStar.TypeChecker.Rel.fst"
let _66_2013 = p
in (match (_66_2013) with
| (((u, k), xs, c), ps, (h, _66_2010, qs)) -> begin
(
# 1468 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1473 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1474 "FStar.TypeChecker.Rel.fst"
let _66_2019 = (imitation_sub_probs orig env xs ps qs)
in (match (_66_2019) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1475 "FStar.TypeChecker.Rel.fst"
let im = (let _155_1003 = (h gs_xs)
in (let _155_1002 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _155_1001 -> Some (_155_1001)))
in (FStar_Syntax_Util.abs xs _155_1003 _155_1002)))
in (
# 1476 "FStar.TypeChecker.Rel.fst"
let _66_2021 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1010 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _155_1009 = (FStar_Syntax_Print.comp_to_string c)
in (let _155_1008 = (FStar_Syntax_Print.term_to_string im)
in (let _155_1007 = (FStar_Syntax_Print.tag_of_term im)
in (let _155_1006 = (let _155_1004 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _155_1004 (FStar_String.concat ", ")))
in (let _155_1005 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _155_1010 _155_1009 _155_1008 _155_1007 _155_1006 _155_1005)))))))
end else begin
()
end
in (
# 1483 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1487 "FStar.TypeChecker.Rel.fst"
let imitate' = (fun orig env wl _66_25 -> (match (_66_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (
# 1492 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1493 "FStar.TypeChecker.Rel.fst"
let _66_2047 = p
in (match (_66_2047) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(
# 1497 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1498 "FStar.TypeChecker.Rel.fst"
let _66_2052 = (FStar_List.nth ps i)
in (match (_66_2052) with
| (pi, _66_2051) -> begin
(
# 1499 "FStar.TypeChecker.Rel.fst"
let _66_2056 = (FStar_List.nth xs i)
in (match (_66_2056) with
| (xi, _66_2055) -> begin
(
# 1501 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1502 "FStar.TypeChecker.Rel.fst"
let _66_2061 = (FStar_Syntax_Util.arrow_formals k)
in (match (_66_2061) with
| (bs, k) -> begin
(
# 1503 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _66_2069)::tl -> begin
(
# 1506 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1507 "FStar.TypeChecker.Rel.fst"
let _66_2075 = (new_uvar r xs k_a)
in (match (_66_2075) with
| (gi_xs, gi) -> begin
(
# 1508 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1509 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1510 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1511 "FStar.TypeChecker.Rel.fst"
let _66_2081 = (aux subst tl)
in (match (_66_2081) with
| (gi_xs', gi_ps') -> begin
(let _155_1040 = (let _155_1037 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_155_1037)::gi_xs')
in (let _155_1039 = (let _155_1038 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_155_1038)::gi_ps')
in (_155_1040, _155_1039)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _155_1041 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _155_1041)) then begin
None
end else begin
(
# 1517 "FStar.TypeChecker.Rel.fst"
let _66_2085 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_66_2085) with
| (g_xs, _66_2084) -> begin
(
# 1518 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1519 "FStar.TypeChecker.Rel.fst"
let proj = (let _155_1044 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _155_1043 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _155_1042 -> Some (_155_1042)))
in (FStar_Syntax_Util.abs xs _155_1044 _155_1043)))
in (
# 1520 "FStar.TypeChecker.Rel.fst"
let sub = (let _155_1050 = (let _155_1049 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _155_1048 = (let _155_1047 = (FStar_List.map (fun _66_2093 -> (match (_66_2093) with
| (_66_2089, _66_2091, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _155_1047))
in (mk_problem (p_scope orig) orig _155_1049 (p_rel orig) _155_1048 None "projection")))
in (FStar_All.pipe_left (fun _155_1045 -> FStar_TypeChecker_Common.TProb (_155_1045)) _155_1050))
in (
# 1521 "FStar.TypeChecker.Rel.fst"
let _66_2095 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1052 = (FStar_Syntax_Print.term_to_string proj)
in (let _155_1051 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _155_1052 _155_1051)))
end else begin
()
end
in (
# 1522 "FStar.TypeChecker.Rel.fst"
let wl = (let _155_1054 = (let _155_1053 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_155_1053))
in (solve_prob orig _155_1054 ((TERM ((u, proj)))::[]) wl))
in (let _155_1056 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _155_1055 -> Some (_155_1055)) _155_1056)))))))
end))
end)
end))
end)))
end)))
in (
# 1527 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1528 "FStar.TypeChecker.Rel.fst"
let _66_2109 = lhs
in (match (_66_2109) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(
# 1529 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1530 "FStar.TypeChecker.Rel.fst"
let _66_2114 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_66_2114) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _155_1078 = (let _155_1077 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _155_1077))
in Some (_155_1078))
end else begin
(
# 1533 "FStar.TypeChecker.Rel.fst"
let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (
# 1534 "FStar.TypeChecker.Rel.fst"
let rec elim = (fun k args -> (match ((let _155_1084 = (let _155_1083 = (FStar_Syntax_Subst.compress k)
in _155_1083.FStar_Syntax_Syntax.n)
in (_155_1084, args))) with
| (_66_2120, []) -> begin
(let _155_1086 = (let _155_1085 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _155_1085))
in Some (_155_1086))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(
# 1539 "FStar.TypeChecker.Rel.fst"
let _66_2137 = (FStar_Syntax_Util.head_and_args k)
in (match (_66_2137) with
| (uv, uv_args) -> begin
(match ((let _155_1087 = (FStar_Syntax_Subst.compress uv)
in _155_1087.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _66_2140) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(
# 1545 "FStar.TypeChecker.Rel.fst"
let xs = (FStar_All.pipe_right args (FStar_List.map (fun _66_2146 -> (let _155_1093 = (let _155_1092 = (let _155_1091 = (let _155_1090 = (let _155_1089 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _155_1089 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _155_1090))
in (Prims.fst _155_1091))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _155_1092))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _155_1093)))))
in (
# 1549 "FStar.TypeChecker.Rel.fst"
let c = (let _155_1097 = (let _155_1096 = (let _155_1095 = (let _155_1094 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _155_1094 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _155_1095))
in (Prims.fst _155_1096))
in (FStar_Syntax_Syntax.mk_Total _155_1097))
in (
# 1550 "FStar.TypeChecker.Rel.fst"
let k' = (FStar_Syntax_Util.arrow xs c)
in (
# 1551 "FStar.TypeChecker.Rel.fst"
let uv_sol = (let _155_1102 = (let _155_1101 = (let _155_1100 = (let _155_1099 = (let _155_1098 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _155_1098 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _155_1099))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _155_1100))
in Some (_155_1101))
in (FStar_Syntax_Util.abs scope k' _155_1102))
in (
# 1552 "FStar.TypeChecker.Rel.fst"
let _66_2152 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some ((xs, c)))))))
end)
end
| _66_2155 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _66_2161) -> begin
(
# 1557 "FStar.TypeChecker.Rel.fst"
let n_args = (FStar_List.length args)
in (
# 1558 "FStar.TypeChecker.Rel.fst"
let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _155_1104 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _155_1104 (fun _155_1103 -> Some (_155_1103))))
end else begin
if (n_xs < n_args) then begin
(
# 1562 "FStar.TypeChecker.Rel.fst"
let _66_2167 = (FStar_Util.first_N n_xs args)
in (match (_66_2167) with
| (args, rest) -> begin
(
# 1563 "FStar.TypeChecker.Rel.fst"
let _66_2170 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_66_2170) with
| (xs, c) -> begin
(let _155_1106 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _155_1106 (fun _66_2173 -> (match (_66_2173) with
| (xs', c) -> begin
Some (((FStar_List.append xs xs'), c))
end))))
end))
end))
end else begin
(
# 1568 "FStar.TypeChecker.Rel.fst"
let _66_2176 = (FStar_Util.first_N n_args xs)
in (match (_66_2176) with
| (xs, rest) -> begin
(
# 1569 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) None k.FStar_Syntax_Syntax.pos)
in (let _155_1109 = (let _155_1107 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _155_1107))
in (FStar_All.pipe_right _155_1109 (fun _155_1108 -> Some (_155_1108)))))
end))
end
end))
end
| _66_2179 -> begin
(let _155_1113 = (let _155_1112 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _155_1111 = (FStar_Syntax_Print.term_to_string k)
in (let _155_1110 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _155_1112 _155_1111 _155_1110))))
in (FStar_All.failwith _155_1113))
end))
in (let _155_1151 = (elim k_uv ps)
in (FStar_Util.bind_opt _155_1151 (fun _66_2182 -> (match (_66_2182) with
| (xs, c) -> begin
(let _155_1150 = (let _155_1149 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _155_1149))
in Some (_155_1150))
end))))))
end
end)))
in (
# 1579 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n stopt i -> if ((i >= n) || (FStar_Option.isNone stopt)) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1582 "FStar.TypeChecker.Rel.fst"
let st = (FStar_Option.get stopt)
in (
# 1583 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_66_2190) -> begin
(
# 1587 "FStar.TypeChecker.Rel.fst"
let _66_2192 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1594 "FStar.TypeChecker.Rel.fst"
let _66_2200 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (
# 1598 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1599 "FStar.TypeChecker.Rel.fst"
let _66_2210 = (FStar_Syntax_Util.head_and_args t2)
in (match (_66_2210) with
| (hd, _66_2209) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _66_2221 -> begin
(
# 1605 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1608 "FStar.TypeChecker.Rel.fst"
let _66_2223 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1162 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _155_1162))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1611 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1612 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _155_1166 = (let _155_1165 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _155_1165 Prims.fst))
in (FStar_All.pipe_right _155_1166 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1619 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1620 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1621 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1622 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1623 "FStar.TypeChecker.Rel.fst"
let _66_2236 = (occurs_check env wl (uv, k_uv) t2)
in (match (_66_2236) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _155_1168 = (let _155_1167 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _155_1167))
in (giveup_or_defer orig _155_1168))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _155_1169 = (subterms args_lhs)
in (imitate' orig env wl _155_1169))
end else begin
(
# 1630 "FStar.TypeChecker.Rel.fst"
let _66_2237 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1172 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_1171 = (names_to_string fvs1)
in (let _155_1170 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _155_1172 _155_1171 _155_1170))))
end else begin
()
end
in (
# 1635 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _66_2241 -> begin
(let _155_1173 = (sn_binders env vars)
in (u_abs k_uv _155_1173 t2))
end)
in (
# 1638 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1643 "FStar.TypeChecker.Rel.fst"
let _66_2244 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1176 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_1175 = (names_to_string fvs1)
in (let _155_1174 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _155_1176 _155_1175 _155_1174))))
end else begin
()
end
in (let _155_1177 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _155_1177 (- (1)))))
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
if (let _155_1178 = (FStar_Syntax_Free.names t1)
in (check_head _155_1178 t2)) then begin
(
# 1655 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1656 "FStar.TypeChecker.Rel.fst"
let _66_2248 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1179 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _155_1179 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _155_1180 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _155_1180 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1681 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1684 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _66_2260 -> (match (_66_2260) with
| (t, u, k, args) -> begin
(
# 1687 "FStar.TypeChecker.Rel.fst"
let _66_2264 = (FStar_Syntax_Util.arrow_formals k)
in (match (_66_2264) with
| (all_formals, _66_2263) -> begin
(
# 1688 "FStar.TypeChecker.Rel.fst"
let _66_2265 = ()
in (
# 1690 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1698 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _66_2278 -> (match (_66_2278) with
| (x, imp) -> begin
(let _155_1202 = (FStar_Syntax_Syntax.bv_to_name x)
in (_155_1202, imp))
end))))
in (
# 1699 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1700 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1701 "FStar.TypeChecker.Rel.fst"
let _66_2284 = (FStar_Syntax_Util.type_u ())
in (match (_66_2284) with
| (t, _66_2283) -> begin
(let _155_1203 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _155_1203))
end))
in (
# 1703 "FStar.TypeChecker.Rel.fst"
let _66_2288 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_66_2288) with
| (t', tm_u1) -> begin
(
# 1704 "FStar.TypeChecker.Rel.fst"
let _66_2295 = (destruct_flex_t t')
in (match (_66_2295) with
| (_66_2290, u1, k1, _66_2294) -> begin
(
# 1705 "FStar.TypeChecker.Rel.fst"
let sol = (let _155_1205 = (let _155_1204 = (u_abs k all_formals t')
in ((u, k), _155_1204))
in TERM (_155_1205))
in (
# 1706 "FStar.TypeChecker.Rel.fst"
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
# 1715 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _66_2314 -> (match (_66_2314) with
| (x, _66_2313) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1722 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _155_1207 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _155_1207 formals tl))
end)
end)
end)
end
| _66_2318 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _155_1208 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _155_1208 all_formals args))))
end))
end))
in (
# 1734 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _66_2325 _66_2330 r -> (match ((_66_2325, _66_2330)) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _155_1217 = (solve_prob orig None [] wl)
in (solve env _155_1217))
end else begin
(
# 1742 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1743 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1744 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1745 "FStar.TypeChecker.Rel.fst"
let _66_2335 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1222 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _155_1221 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _155_1220 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _155_1219 = (FStar_Syntax_Print.term_to_string k1)
in (let _155_1218 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _155_1222 _155_1221 _155_1220 _155_1219 _155_1218))))))
end else begin
()
end
in (
# 1749 "FStar.TypeChecker.Rel.fst"
let _66_2348 = (
# 1750 "FStar.TypeChecker.Rel.fst"
let _66_2340 = (FStar_Syntax_Util.type_u ())
in (match (_66_2340) with
| (t, _66_2339) -> begin
(
# 1751 "FStar.TypeChecker.Rel.fst"
let _66_2344 = (new_uvar r zs t)
in (match (_66_2344) with
| (k, _66_2343) -> begin
(new_uvar r zs k)
end))
end))
in (match (_66_2348) with
| (u_zs, _66_2347) -> begin
(
# 1753 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs k1 xs u_zs)
in (
# 1754 "FStar.TypeChecker.Rel.fst"
let _66_2352 = (occurs_check env wl (u1, k1) sub1)
in (match (_66_2352) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1757 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1761 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs k2 ys u_zs)
in (
# 1762 "FStar.TypeChecker.Rel.fst"
let _66_2358 = (occurs_check env wl (u2, k2) sub2)
in (match (_66_2358) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1765 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1766 "FStar.TypeChecker.Rel.fst"
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
# 1770 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _66_2366 _66_2371 -> (match ((_66_2366, _66_2371)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1772 "FStar.TypeChecker.Rel.fst"
let _66_2372 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1228 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_1227 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _155_1228 _155_1227)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1775 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _66_2377 _66_2381 -> (match ((_66_2377, _66_2381)) with
| ((a, _66_2376), (t2, _66_2380)) -> begin
(let _155_1233 = (let _155_1231 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _155_1231 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _155_1233 (fun _155_1232 -> FStar_TypeChecker_Common.TProb (_155_1232))))
end)) xs args2)
in (
# 1778 "FStar.TypeChecker.Rel.fst"
let guard = (let _155_1235 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _155_1235))
in (
# 1779 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1782 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1783 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1784 "FStar.TypeChecker.Rel.fst"
let _66_2391 = (occurs_check env wl (u1, k1) t2)
in (match (_66_2391) with
| (occurs_ok, _66_2390) -> begin
(
# 1785 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1788 "FStar.TypeChecker.Rel.fst"
let sol = (let _155_1237 = (let _155_1236 = (u_abs k1 xs t2)
in ((u1, k1), _155_1236))
in TERM (_155_1237))
in (
# 1789 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1792 "FStar.TypeChecker.Rel.fst"
let _66_2402 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_66_2402) with
| (sol, (_66_2397, u2, k2, ys)) -> begin
(
# 1793 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1794 "FStar.TypeChecker.Rel.fst"
let _66_2404 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _155_1238 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _155_1238))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _66_2409 -> begin
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
# 1802 "FStar.TypeChecker.Rel.fst"
let _66_2414 = lhs
in (match (_66_2414) with
| (t1, u1, k1, args1) -> begin
(
# 1803 "FStar.TypeChecker.Rel.fst"
let _66_2419 = rhs
in (match (_66_2419) with
| (t2, u2, k2, args2) -> begin
(
# 1804 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1805 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1806 "FStar.TypeChecker.Rel.fst"
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
| _66_2437 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1815 "FStar.TypeChecker.Rel.fst"
let _66_2441 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_66_2441) with
| (sol, _66_2440) -> begin
(
# 1816 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1817 "FStar.TypeChecker.Rel.fst"
let _66_2443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _155_1239 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _155_1239))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _66_2448 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1824 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _155_1240 = (solve_prob orig None [] wl)
in (solve env _155_1240))
end else begin
(
# 1826 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1827 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _155_1241 = (solve_prob orig None [] wl)
in (solve env _155_1241))
end else begin
(
# 1829 "FStar.TypeChecker.Rel.fst"
let _66_2452 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _155_1242 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _155_1242))
end else begin
()
end
in (
# 1832 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1834 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _66_2457 _66_2460 -> (match ((_66_2457, _66_2460)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1836 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1837 "FStar.TypeChecker.Rel.fst"
let _66_2467 = (FStar_Util.first_N n bs)
in (match (_66_2467) with
| (bs, rest) -> begin
(let _155_1272 = (mk_cod rest)
in (bs, _155_1272))
end)))
in (
# 1840 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1841 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _155_1276 = (let _155_1273 = (mk_cod1 [])
in (bs1, _155_1273))
in (let _155_1275 = (let _155_1274 = (mk_cod2 [])
in (bs2, _155_1274))
in (_155_1276, _155_1275)))
end else begin
if (l1 > l2) then begin
(let _155_1279 = (curry l2 bs1 mk_cod1)
in (let _155_1278 = (let _155_1277 = (mk_cod2 [])
in (bs2, _155_1277))
in (_155_1279, _155_1278)))
end else begin
(let _155_1282 = (let _155_1280 = (mk_cod1 [])
in (bs1, _155_1280))
in (let _155_1281 = (curry l1 bs2 mk_cod2)
in (_155_1282, _155_1281)))
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
# 1859 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _66_26 -> (match (_66_26) with
| [] -> begin
c
end
| bs -> begin
(let _155_1287 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _155_1287))
end))
in (
# 1863 "FStar.TypeChecker.Rel.fst"
let _66_2510 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_66_2510) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1868 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1869 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1870 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _155_1294 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _155_1293 -> FStar_TypeChecker_Common.CProb (_155_1293)) _155_1294)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _66_2520), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _66_2526)) -> begin
(
# 1874 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _66_27 -> (match (_66_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1877 "FStar.TypeChecker.Rel.fst"
let _66_2541 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_66_2541) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _155_1307 = (let _155_1306 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _155_1305 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _155_1306 problem.FStar_TypeChecker_Common.relation _155_1305 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _155_1304 -> FStar_TypeChecker_Common.TProb (_155_1304)) _155_1307))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_66_2546), FStar_Syntax_Syntax.Tm_refine (_66_2549)) -> begin
(
# 1886 "FStar.TypeChecker.Rel.fst"
let _66_2554 = (as_refinement env wl t1)
in (match (_66_2554) with
| (x1, phi1) -> begin
(
# 1887 "FStar.TypeChecker.Rel.fst"
let _66_2557 = (as_refinement env wl t2)
in (match (_66_2557) with
| (x2, phi2) -> begin
(
# 1888 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _155_1309 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _155_1308 -> FStar_TypeChecker_Common.TProb (_155_1308)) _155_1309))
in (
# 1889 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1890 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1891 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1892 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1893 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1894 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _155_1326 = (imp phi1 phi2)
in (FStar_All.pipe_right _155_1326 (guard_on_element problem x1))))
in (
# 1895 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _66_2569 -> (match (()) with
| () -> begin
(
# 1896 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1900 "FStar.TypeChecker.Rel.fst"
let guard = (let _155_1329 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _155_1329 impl))
in (
# 1901 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1904 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _155_1333 = (let _155_1332 = (let _155_1331 = (FStar_Syntax_Syntax.mk_binder x1)
in (_155_1331)::(p_scope orig))
in (mk_problem _155_1332 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _155_1330 -> FStar_TypeChecker_Common.TProb (_155_1330)) _155_1333))
in (match ((solve env (
# 1905 "FStar.TypeChecker.Rel.fst"
let _66_2574 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _66_2574.ctr; defer_ok = false; smt_ok = _66_2574.smt_ok; tcenv = _66_2574.tcenv}))) with
| Failed (_66_2577) -> begin
(fallback ())
end
| Success (_66_2580) -> begin
(
# 1908 "FStar.TypeChecker.Rel.fst"
let guard = (let _155_1336 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _155_1335 = (let _155_1334 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _155_1334 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _155_1336 _155_1335)))
in (
# 1909 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1910 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1910 "FStar.TypeChecker.Rel.fst"
let _66_2584 = wl
in {attempting = _66_2584.attempting; wl_deferred = _66_2584.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _66_2584.defer_ok; smt_ok = _66_2584.smt_ok; tcenv = _66_2584.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _155_1338 = (destruct_flex_t t1)
in (let _155_1337 = (destruct_flex_t t2)
in (flex_flex orig _155_1338 _155_1337)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _155_1339 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _155_1339 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1938 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _155_1340 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _155_1340)) then begin
(let _155_1343 = (FStar_All.pipe_left (fun _155_1341 -> FStar_TypeChecker_Common.TProb (_155_1341)) (
# 1940 "FStar.TypeChecker.Rel.fst"
let _66_2729 = problem
in {FStar_TypeChecker_Common.pid = _66_2729.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_2729.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _66_2729.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_2729.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2729.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2729.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2729.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2729.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2729.FStar_TypeChecker_Common.rank}))
in (let _155_1342 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _155_1343 _155_1342 t2 wl)))
end else begin
(
# 1941 "FStar.TypeChecker.Rel.fst"
let _66_2733 = (base_and_refinement env wl t2)
in (match (_66_2733) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _155_1346 = (FStar_All.pipe_left (fun _155_1344 -> FStar_TypeChecker_Common.TProb (_155_1344)) (
# 1944 "FStar.TypeChecker.Rel.fst"
let _66_2735 = problem
in {FStar_TypeChecker_Common.pid = _66_2735.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_2735.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _66_2735.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_2735.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2735.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2735.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2735.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2735.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2735.FStar_TypeChecker_Common.rank}))
in (let _155_1345 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _155_1346 _155_1345 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1947 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1947 "FStar.TypeChecker.Rel.fst"
let _66_2741 = y
in {FStar_Syntax_Syntax.ppname = _66_2741.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_2741.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1948 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1949 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _155_1348 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _155_1347 -> FStar_TypeChecker_Common.TProb (_155_1347)) _155_1348))
in (
# 1951 "FStar.TypeChecker.Rel.fst"
let guard = (let _155_1349 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _155_1349 impl))
in (
# 1952 "FStar.TypeChecker.Rel.fst"
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
# 1961 "FStar.TypeChecker.Rel.fst"
let _66_2774 = (base_and_refinement env wl t1)
in (match (_66_2774) with
| (t_base, _66_2773) -> begin
(solve_t env (
# 1962 "FStar.TypeChecker.Rel.fst"
let _66_2775 = problem
in {FStar_TypeChecker_Common.pid = _66_2775.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _66_2775.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_2775.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2775.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2775.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2775.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2775.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2775.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_66_2778), _66_2781) -> begin
(
# 1965 "FStar.TypeChecker.Rel.fst"
let t2 = (let _155_1350 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _155_1350))
in (solve_t env (
# 1966 "FStar.TypeChecker.Rel.fst"
let _66_2784 = problem
in {FStar_TypeChecker_Common.pid = _66_2784.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_2784.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_2784.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _66_2784.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2784.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2784.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2784.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2784.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2784.FStar_TypeChecker_Common.rank}) wl))
end
| (_66_2787, FStar_Syntax_Syntax.Tm_refine (_66_2789)) -> begin
(
# 1969 "FStar.TypeChecker.Rel.fst"
let t1 = (let _155_1351 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _155_1351))
in (solve_t env (
# 1970 "FStar.TypeChecker.Rel.fst"
let _66_2793 = problem
in {FStar_TypeChecker_Common.pid = _66_2793.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _66_2793.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_2793.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_2793.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2793.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2793.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2793.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2793.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2793.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1974 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_66_2810) -> begin
t
end
| _66_2813 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _155_1356 = (
# 1977 "FStar.TypeChecker.Rel.fst"
let _66_2814 = problem
in (let _155_1355 = (maybe_eta t1)
in (let _155_1354 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _66_2814.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _155_1355; FStar_TypeChecker_Common.relation = _66_2814.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _155_1354; FStar_TypeChecker_Common.element = _66_2814.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2814.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2814.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2814.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2814.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2814.FStar_TypeChecker_Common.rank})))
in (solve_t env _155_1356 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1991 "FStar.TypeChecker.Rel.fst"
let head1 = (let _155_1357 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _155_1357 Prims.fst))
in (
# 1992 "FStar.TypeChecker.Rel.fst"
let head2 = (let _155_1358 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _155_1358 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1997 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1998 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 2000 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _155_1360 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _155_1359 -> Some (_155_1359)) _155_1360))
end
in (let _155_1361 = (solve_prob orig guard [] wl)
in (solve env _155_1361)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _66_2895, _66_2897), _66_2901) -> begin
(solve_t' env (
# 2008 "FStar.TypeChecker.Rel.fst"
let _66_2903 = problem
in {FStar_TypeChecker_Common.pid = _66_2903.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _66_2903.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_2903.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_2903.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2903.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2903.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2903.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2903.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2903.FStar_TypeChecker_Common.rank}) wl)
end
| (_66_2906, FStar_Syntax_Syntax.Tm_ascribed (t2, _66_2909, _66_2911)) -> begin
(solve_t' env (
# 2011 "FStar.TypeChecker.Rel.fst"
let _66_2915 = problem
in {FStar_TypeChecker_Common.pid = _66_2915.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_2915.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_2915.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _66_2915.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_2915.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_2915.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_2915.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_2915.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_2915.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _155_1364 = (let _155_1363 = (FStar_Syntax_Print.tag_of_term t1)
in (let _155_1362 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _155_1363 _155_1362)))
in (FStar_All.failwith _155_1364))
end
| _66_2954 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end)))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 2023 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 2024 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 2025 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 2026 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 2028 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 2029 "FStar.TypeChecker.Rel.fst"
let _66_2971 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 2031 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _66_2976 _66_2980 -> (match ((_66_2976, _66_2980)) with
| ((a1, _66_2975), (a2, _66_2979)) -> begin
(let _155_1379 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _155_1378 -> FStar_TypeChecker_Common.TProb (_155_1378)) _155_1379))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 2034 "FStar.TypeChecker.Rel.fst"
let guard = (let _155_1381 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _155_1381))
in (
# 2035 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _155_1382 = (solve_prob orig None [] wl)
in (solve env _155_1382))
end else begin
(
# 2039 "FStar.TypeChecker.Rel.fst"
let _66_2985 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1384 = (FStar_Syntax_Print.comp_to_string c1)
in (let _155_1383 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _155_1384 (rel_to_string problem.FStar_TypeChecker_Common.relation) _155_1383)))
end else begin
()
end
in (
# 2044 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 2045 "FStar.TypeChecker.Rel.fst"
let _66_2990 = (c1, c2)
in (match (_66_2990) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_66_2992), FStar_Syntax_Syntax.Total (_66_2995)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _155_1385 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _155_1385 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _155_1387 = (
# 2057 "FStar.TypeChecker.Rel.fst"
let _66_3023 = problem
in (let _155_1386 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _66_3023.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _155_1386; FStar_TypeChecker_Common.relation = _66_3023.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _66_3023.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _66_3023.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_3023.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_3023.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_3023.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_3023.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_3023.FStar_TypeChecker_Common.rank}))
in (solve_c env _155_1387 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _155_1389 = (
# 2061 "FStar.TypeChecker.Rel.fst"
let _66_3039 = problem
in (let _155_1388 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _66_3039.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _66_3039.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _66_3039.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _155_1388; FStar_TypeChecker_Common.element = _66_3039.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _66_3039.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _66_3039.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _66_3039.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _66_3039.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _66_3039.FStar_TypeChecker_Common.rank}))
in (solve_c env _155_1389 wl))
end
| (FStar_Syntax_Syntax.Comp (_66_3042), FStar_Syntax_Syntax.Comp (_66_3045)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _155_1390 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _155_1390 wl))
end else begin
(
# 2067 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 2068 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2072 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 2073 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 2074 "FStar.TypeChecker.Rel.fst"
let _66_3052 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _155_1393 = (let _155_1392 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _155_1391 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _155_1392 _155_1391)))
in (giveup env _155_1393 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 2081 "FStar.TypeChecker.Rel.fst"
let _66_3070 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _66_3063)::(wlp1, _66_3059)::[] -> begin
(wp1, wlp1)
end
| _66_3067 -> begin
(let _155_1395 = (let _155_1394 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _155_1394))
in (FStar_All.failwith _155_1395))
end)
in (match (_66_3070) with
| (wp, wlp) -> begin
(
# 2084 "FStar.TypeChecker.Rel.fst"
let c1 = (let _155_1401 = (let _155_1400 = (let _155_1396 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _155_1396))
in (let _155_1399 = (let _155_1398 = (let _155_1397 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _155_1397))
in (_155_1398)::[])
in (_155_1400)::_155_1399))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _155_1401; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2091 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _66_28 -> (match (_66_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _66_3077 -> begin
false
end))))
in (
# 2092 "FStar.TypeChecker.Rel.fst"
let _66_3098 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _66_3083)::_66_3080, (wp2, _66_3090)::_66_3087) -> begin
(wp1, wp2)
end
| _66_3095 -> begin
(let _155_1405 = (let _155_1404 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _155_1403 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _155_1404 _155_1403)))
in (FStar_All.failwith _155_1405))
end)
in (match (_66_3098) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _155_1406 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _155_1406 wl))
end else begin
(
# 2099 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 2100 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2102 "FStar.TypeChecker.Rel.fst"
let _66_3100 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _155_1416 = (let _155_1415 = (let _155_1414 = (let _155_1408 = (let _155_1407 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_155_1407)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _155_1408 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _155_1413 = (let _155_1412 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _155_1411 = (let _155_1410 = (let _155_1409 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_1409))
in (_155_1410)::[])
in (_155_1412)::_155_1411))
in (_155_1414, _155_1413)))
in FStar_Syntax_Syntax.Tm_app (_155_1415))
in (FStar_Syntax_Syntax.mk _155_1416 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 2106 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _155_1432 = (let _155_1431 = (let _155_1430 = (let _155_1418 = (let _155_1417 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_155_1417)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _155_1418 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _155_1429 = (let _155_1428 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _155_1427 = (let _155_1426 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _155_1425 = (let _155_1424 = (let _155_1420 = (let _155_1419 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _155_1419 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_1420))
in (let _155_1423 = (let _155_1422 = (let _155_1421 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _155_1421))
in (_155_1422)::[])
in (_155_1424)::_155_1423))
in (_155_1426)::_155_1425))
in (_155_1428)::_155_1427))
in (_155_1430, _155_1429)))
in FStar_Syntax_Syntax.Tm_app (_155_1431))
in (FStar_Syntax_Syntax.mk _155_1432 None r))
in (let _155_1441 = (let _155_1440 = (let _155_1439 = (let _155_1434 = (let _155_1433 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_155_1433)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _155_1434 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _155_1438 = (let _155_1437 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _155_1436 = (let _155_1435 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_155_1435)::[])
in (_155_1437)::_155_1436))
in (_155_1439, _155_1438)))
in FStar_Syntax_Syntax.Tm_app (_155_1440))
in (FStar_Syntax_Syntax.mk _155_1441 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 2113 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _155_1443 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _155_1442 -> FStar_TypeChecker_Common.TProb (_155_1442)) _155_1443))
in (
# 2114 "FStar.TypeChecker.Rel.fst"
let wl = (let _155_1447 = (let _155_1446 = (let _155_1445 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _155_1445 g))
in (FStar_All.pipe_left (fun _155_1444 -> Some (_155_1444)) _155_1446))
in (solve_prob orig _155_1447 [] wl))
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

# 2116 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _155_1451 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _66_3118 -> (match (_66_3118) with
| (_66_3108, _66_3110, u, _66_3113, _66_3115, _66_3117) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _155_1451 (FStar_String.concat ", "))))

# 2121 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _66_3125 -> begin
(
# 2127 "FStar.TypeChecker.Rel.fst"
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
# 2134 "FStar.TypeChecker.Rel.fst"
let carry = (let _155_1457 = (FStar_List.map (fun _66_3133 -> (match (_66_3133) with
| (_66_3131, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _155_1457 (FStar_String.concat ",\n")))
in (
# 2135 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 2136 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 2141 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 2143 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _66_3142; FStar_TypeChecker_Env.implicits = _66_3140} -> begin
true
end
| _66_3147 -> begin
false
end))

# 2147 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 2149 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2155 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _66_3165 -> begin
(FStar_All.failwith "impossible")
end)
in (let _155_1476 = (
# 2158 "FStar.TypeChecker.Rel.fst"
let _66_3167 = g
in (let _155_1475 = (let _155_1474 = (let _155_1473 = (let _155_1469 = (FStar_Syntax_Syntax.mk_binder x)
in (_155_1469)::[])
in (let _155_1472 = (let _155_1471 = (let _155_1470 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _155_1470 FStar_Syntax_Util.lcomp_of_comp))
in Some (_155_1471))
in (FStar_Syntax_Util.abs _155_1473 f _155_1472)))
in (FStar_All.pipe_left (fun _155_1468 -> FStar_TypeChecker_Common.NonTrivial (_155_1468)) _155_1474))
in {FStar_TypeChecker_Env.guard_f = _155_1475; FStar_TypeChecker_Env.deferred = _66_3167.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3167.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3167.FStar_TypeChecker_Env.implicits}))
in Some (_155_1476)))
end))

# 2158 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2162 "FStar.TypeChecker.Rel.fst"
let _66_3174 = g
in (let _155_1487 = (let _155_1486 = (let _155_1485 = (let _155_1484 = (let _155_1483 = (let _155_1482 = (FStar_Syntax_Syntax.as_arg e)
in (_155_1482)::[])
in (f, _155_1483))
in FStar_Syntax_Syntax.Tm_app (_155_1484))
in (FStar_Syntax_Syntax.mk _155_1485 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _155_1481 -> FStar_TypeChecker_Common.NonTrivial (_155_1481)) _155_1486))
in {FStar_TypeChecker_Env.guard_f = _155_1487; FStar_TypeChecker_Env.deferred = _66_3174.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3174.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3174.FStar_TypeChecker_Env.implicits}))
end))

# 2162 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_66_3179) -> begin
(FStar_All.failwith "impossible")
end))

# 2166 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _155_1494 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_155_1494))
end))

# 2171 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _66_3197 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 2175 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2181 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2181 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _155_1517 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _155_1517; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2186 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2187 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2188 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2192 "FStar.TypeChecker.Rel.fst"
let _66_3224 = g
in (let _155_1532 = (let _155_1531 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _155_1531 (fun _155_1530 -> FStar_TypeChecker_Common.NonTrivial (_155_1530))))
in {FStar_TypeChecker_Env.guard_f = _155_1532; FStar_TypeChecker_Env.deferred = _66_3224.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3224.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3224.FStar_TypeChecker_Env.implicits}))
end))

# 2192 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2198 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _155_1540 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _155_1539 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _155_1540 (rel_to_string rel) _155_1539)))
end else begin
"TOP"
end
in (
# 2203 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2204 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2207 "FStar.TypeChecker.Rel.fst"
let x = (let _155_1551 = (let _155_1550 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _155_1549 -> Some (_155_1549)) _155_1550))
in (FStar_Syntax_Syntax.new_bv _155_1551 t1))
in (
# 2208 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2209 "FStar.TypeChecker.Rel.fst"
let p = (let _155_1555 = (let _155_1553 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _155_1552 -> Some (_155_1552)) _155_1553))
in (let _155_1554 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _155_1555 _155_1554)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2210 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2213 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2213 "FStar.TypeChecker.Rel.fst"
let _66_3244 = probs
in {attempting = _66_3244.attempting; wl_deferred = _66_3244.wl_deferred; ctr = _66_3244.ctr; defer_ok = false; smt_ok = _66_3244.smt_ok; tcenv = _66_3244.tcenv})
end else begin
probs
end
in (
# 2214 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2215 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2218 "FStar.TypeChecker.Rel.fst"
let _66_3251 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2221 "FStar.TypeChecker.Rel.fst"
let _66_3257 = (FStar_Unionfind.rollback tx)
in (
# 2222 "FStar.TypeChecker.Rel.fst"
let _66_3259 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _155_1567 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _155_1567))
end else begin
()
end
in (err (d, s))))
end)))))

# 2224 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2229 "FStar.TypeChecker.Rel.fst"
let _66_3266 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _155_1572 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _155_1572))
end else begin
()
end
in (
# 2230 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2231 "FStar.TypeChecker.Rel.fst"
let _66_3269 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _155_1573 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _155_1573))
end else begin
()
end
in (
# 2232 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _155_1574 = (FStar_Syntax_Util.unmeta f)
in _155_1574.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _66_3274 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2235 "FStar.TypeChecker.Rel.fst"
let _66_3276 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _66_3276.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3276.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3276.FStar_TypeChecker_Env.implicits})))))
end))

# 2235 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _155_1586 = (let _155_1585 = (let _155_1584 = (let _155_1583 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _155_1583 (fun _155_1582 -> FStar_TypeChecker_Common.NonTrivial (_155_1582))))
in {FStar_TypeChecker_Env.guard_f = _155_1584; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _155_1585))
in (FStar_All.pipe_left (fun _155_1581 -> Some (_155_1581)) _155_1586))
end))

# 2240 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2243 "FStar.TypeChecker.Rel.fst"
let _66_3287 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1594 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_1593 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _155_1594 _155_1593)))
end else begin
()
end
in (
# 2245 "FStar.TypeChecker.Rel.fst"
let prob = (let _155_1597 = (let _155_1596 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _155_1596))
in (FStar_All.pipe_left (fun _155_1595 -> FStar_TypeChecker_Common.TProb (_155_1595)) _155_1597))
in (
# 2246 "FStar.TypeChecker.Rel.fst"
let g = (let _155_1599 = (solve_and_commit env (singleton env prob) (fun _66_3290 -> None))
in (FStar_All.pipe_left (with_guard env prob) _155_1599))
in g))))

# 2247 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _155_1609 = (let _155_1608 = (let _155_1607 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _155_1606 = (FStar_TypeChecker_Env.get_range env)
in (_155_1607, _155_1606)))
in FStar_Syntax_Syntax.Error (_155_1608))
in (Prims.raise _155_1609))
end
| Some (g) -> begin
(
# 2253 "FStar.TypeChecker.Rel.fst"
let _66_3299 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1612 = (FStar_Syntax_Print.term_to_string t1)
in (let _155_1611 = (FStar_Syntax_Print.term_to_string t2)
in (let _155_1610 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _155_1612 _155_1611 _155_1610))))
end else begin
()
end
in g)
end))

# 2258 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2261 "FStar.TypeChecker.Rel.fst"
let _66_3304 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1620 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_1619 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _155_1620 _155_1619)))
end else begin
()
end
in (
# 2263 "FStar.TypeChecker.Rel.fst"
let _66_3308 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_66_3308) with
| (prob, x) -> begin
(
# 2264 "FStar.TypeChecker.Rel.fst"
let g = (let _155_1622 = (solve_and_commit env (singleton env prob) (fun _66_3309 -> None))
in (FStar_All.pipe_left (with_guard env prob) _155_1622))
in (
# 2265 "FStar.TypeChecker.Rel.fst"
let _66_3312 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _155_1626 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _155_1625 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _155_1624 = (let _155_1623 = (FStar_Util.must g)
in (guard_to_string env _155_1623))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _155_1626 _155_1625 _155_1624))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2271 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _155_1633 = (let _155_1632 = (let _155_1631 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _155_1630 = (FStar_TypeChecker_Env.get_range env)
in (_155_1631, _155_1630)))
in FStar_Syntax_Syntax.Error (_155_1632))
in (Prims.raise _155_1633)))

# 2274 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2278 "FStar.TypeChecker.Rel.fst"
let _66_3320 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1641 = (FStar_Syntax_Print.comp_to_string c1)
in (let _155_1640 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _155_1641 _155_1640)))
end else begin
()
end
in (
# 2280 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2281 "FStar.TypeChecker.Rel.fst"
let prob = (let _155_1644 = (let _155_1643 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _155_1643 "sub_comp"))
in (FStar_All.pipe_left (fun _155_1642 -> FStar_TypeChecker_Common.CProb (_155_1642)) _155_1644))
in (let _155_1646 = (solve_and_commit env (singleton env prob) (fun _66_3324 -> None))
in (FStar_All.pipe_left (with_guard env prob) _155_1646))))))

# 2282 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2286 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2287 "FStar.TypeChecker.Rel.fst"
let _66_3333 = (FStar_Unionfind.rollback tx)
in (
# 2288 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _155_1664 = (let _155_1663 = (let _155_1662 = (let _155_1660 = (FStar_Syntax_Print.univ_to_string u1)
in (let _155_1659 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _155_1660 _155_1659 msg)))
in (let _155_1661 = (FStar_TypeChecker_Env.get_range env)
in (_155_1662, _155_1661)))
in FStar_Syntax_Syntax.Error (_155_1663))
in (Prims.raise _155_1664)))))
in (
# 2297 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2300 "FStar.TypeChecker.Rel.fst"
let _66_3349 = hd
in (match (_66_3349) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _155_1671 = (insert uv u1 tl)
in (hd)::_155_1671)
end
end))
end))
in (
# 2305 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2308 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2311 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _155_1676 = (insert uv u1 out)
in (group_by _155_1676 rest))
end)
end
| _66_3364 -> begin
None
end))
end))
in (
# 2318 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _66_3366 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _66_3369 -> begin
(
# 2323 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2323 "FStar.TypeChecker.Rel.fst"
let _66_3370 = (empty_worklist env)
in {attempting = _66_3370.attempting; wl_deferred = _66_3370.wl_deferred; ctr = _66_3370.ctr; defer_ok = true; smt_ok = _66_3370.smt_ok; tcenv = _66_3370.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _66_3375 -> (match (_66_3375) with
| (u1, u2) -> begin
(
# 2325 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2326 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _66_3380 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2332 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _66_3390 -> begin
(u1)::[]
end)
in (
# 2335 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _66_3395 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _66_29 -> (match (_66_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2341 "FStar.TypeChecker.Rel.fst"
let _66_3402 = (FStar_Syntax_Util.univ_kernel u)
in (match (_66_3402) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2343 "FStar.TypeChecker.Rel.fst"
let _66_3406 = (FStar_Syntax_Util.univ_kernel u')
in (match (_66_3406) with
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
| USolved (_66_3408) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2353 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2353 "FStar.TypeChecker.Rel.fst"
let _66_3412 = (empty_worklist env)
in {attempting = _66_3412.attempting; wl_deferred = _66_3412.wl_deferred; ctr = _66_3412.ctr; defer_ok = false; smt_ok = _66_3412.smt_ok; tcenv = _66_3412.tcenv})
in (
# 2354 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _66_3427 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2364 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2367 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2368 "FStar.TypeChecker.Rel.fst"
let _66_3432 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2369 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2372 "FStar.TypeChecker.Rel.fst"
let fail = (fun _66_3439 -> (match (_66_3439) with
| (d, s) -> begin
(
# 2373 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2375 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2376 "FStar.TypeChecker.Rel.fst"
let _66_3442 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_1697 = (wl_to_string wl)
in (let _155_1696 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _155_1697 _155_1696)))
end else begin
()
end
in (
# 2378 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2379 "FStar.TypeChecker.Rel.fst"
let _66_3446 = g
in {FStar_TypeChecker_Env.guard_f = _66_3446.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _66_3446.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3446.FStar_TypeChecker_Env.implicits})
end
| _66_3449 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2381 "FStar.TypeChecker.Rel.fst"
let _66_3451 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2382 "FStar.TypeChecker.Rel.fst"
let _66_3453 = g
in {FStar_TypeChecker_Env.guard_f = _66_3453.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _66_3453.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _66_3453.FStar_TypeChecker_Env.implicits})))))))

# 2382 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2385 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2386 "FStar.TypeChecker.Rel.fst"
let _66_3468 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2390 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2394 "FStar.TypeChecker.Rel.fst"
let _66_3466 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _155_1714 = (FStar_TypeChecker_Env.get_range env)
in (let _155_1713 = (let _155_1712 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _155_1712))
in (FStar_TypeChecker_Errors.diag _155_1714 _155_1713)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2399 "FStar.TypeChecker.Rel.fst"
let _66_3470 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _66_3470.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3470.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3470.FStar_TypeChecker_Env.implicits}))))

# 2399 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2401 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2404 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _66_3479 -> begin
false
end))
in (
# 2407 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _66_3483 implicits -> (match (_66_3483) with
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
# 2411 "FStar.TypeChecker.Rel.fst"
let _66_3496 = hd
in (match (_66_3496) with
| (_66_3490, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2414 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2415 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2416 "FStar.TypeChecker.Rel.fst"
let _66_3499 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _155_1730 = (FStar_Syntax_Print.uvar_to_string u)
in (let _155_1729 = (FStar_Syntax_Print.term_to_string tm)
in (let _155_1728 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _155_1730 _155_1729 _155_1728))))
end else begin
()
end
in (
# 2419 "FStar.TypeChecker.Rel.fst"
let _66_3508 = (env.FStar_TypeChecker_Env.type_of (
# 2419 "FStar.TypeChecker.Rel.fst"
let _66_3501 = env
in {FStar_TypeChecker_Env.solver = _66_3501.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _66_3501.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _66_3501.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _66_3501.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _66_3501.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _66_3501.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _66_3501.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _66_3501.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _66_3501.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _66_3501.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _66_3501.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _66_3501.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _66_3501.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _66_3501.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _66_3501.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _66_3501.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _66_3501.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _66_3501.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _66_3501.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _66_3501.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_66_3508) with
| (_66_3504, _66_3506, g) -> begin
(
# 2420 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2421 "FStar.TypeChecker.Rel.fst"
let _66_3509 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _66_3509.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3509.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _66_3509.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2423 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _66_3512 -> (match (()) with
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
# 2425 "FStar.TypeChecker.Rel.fst"
let _66_3514 = g
in (let _155_1734 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _66_3514.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _66_3514.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _66_3514.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _155_1734})))))

# 2425 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2428 "FStar.TypeChecker.Rel.fst"
let g = (let _155_1739 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _155_1739 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _155_1740 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _155_1740))
end
| (reason, _66_3524, _66_3526, e, t, r)::_66_3521 -> begin
(let _155_1745 = (let _155_1744 = (let _155_1743 = (let _155_1742 = (FStar_Syntax_Print.term_to_string t)
in (let _155_1741 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _155_1742 _155_1741 reason)))
in (_155_1743, r))
in FStar_Syntax_Syntax.Error (_155_1744))
in (Prims.raise _155_1745))
end)))

# 2437 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2441 "FStar.TypeChecker.Rel.fst"
let _66_3534 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _66_3534.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _66_3534.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _66_3534.FStar_TypeChecker_Env.implicits}))





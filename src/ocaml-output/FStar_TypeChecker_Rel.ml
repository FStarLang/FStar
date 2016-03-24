
open Prims
# 60 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _147_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _147_8 Prims.op_Negation)))))
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
| _62_39 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _147_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _147_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _147_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_147_10, uv)))))
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
| TERM (_62_45) -> begin
_62_45
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_62_48) -> begin
_62_48
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
| Success (_62_58) -> begin
_62_58
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_62_61) -> begin
_62_61
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
let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _62_1 -> (match (_62_1) with
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
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _62_2 -> (match (_62_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_109 = (let _147_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _147_107 = (let _147_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _147_105 = (let _147_104 = (let _147_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _147_102 = (let _147_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _147_100 = (let _147_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _147_98 = (let _147_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_147_97)::[])
in (_147_99)::_147_98))
in (_147_101)::_147_100))
in (_147_103)::_147_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_147_104)
in (_147_106)::_147_105))
in (_147_108)::_147_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _147_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _147_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _147_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _147_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_110)))
end))

# 138 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _62_3 -> (match (_62_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _147_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _147_116 FStar_Util.string_of_int))
end
in (let _147_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _147_117)))
end
| TERM ((u, _62_85), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _147_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _147_118 FStar_Util.string_of_int))
end
in (let _147_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _147_119)))
end))

# 147 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _147_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _147_124 (FStar_String.concat ", "))))

# 148 "FStar.TypeChecker.Rel.fst"
let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _147_134 = (let _147_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _147_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _147_134 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _147_137 = (FStar_All.pipe_right args (FStar_List.map (fun _62_98 -> (match (_62_98) with
| (x, _62_97) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _147_137 (FStar_String.concat " "))))

# 150 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 166 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _62_102 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _62_102.wl_deferred; ctr = _62_102.ctr; defer_ok = _62_102.defer_ok; smt_ok = _62_102.smt_ok; tcenv = _62_102.tcenv}))

# 167 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _62_106 = (empty_worklist env)
in (let _147_146 = (FStar_List.map Prims.snd g)
in {attempting = _147_146; wl_deferred = _62_106.wl_deferred; ctr = _62_106.ctr; defer_ok = false; smt_ok = _62_106.smt_ok; tcenv = _62_106.tcenv})))

# 168 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _62_111 = wl
in {attempting = _62_111.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _62_111.ctr; defer_ok = _62_111.defer_ok; smt_ok = _62_111.smt_ok; tcenv = _62_111.tcenv}))

# 169 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _62_115 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _62_115.wl_deferred; ctr = _62_115.ctr; defer_ok = _62_115.defer_ok; smt_ok = _62_115.smt_ok; tcenv = _62_115.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _62_120 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _147_163))
end else begin
()
end
in Failed ((prob, reason))))

# 175 "FStar.TypeChecker.Rel.fst"
let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _62_4 -> (match (_62_4) with
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
let _62_127 = p
in {FStar_TypeChecker_Common.pid = _62_127.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _62_127.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_127.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_127.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_127.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_127.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_127.FStar_TypeChecker_Common.rank}))

# 187 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _62_5 -> (match (_62_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _147_170 -> FStar_TypeChecker_Common.TProb (_147_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _147_171 -> FStar_TypeChecker_Common.CProb (_147_171)))
end))

# 191 "FStar.TypeChecker.Rel.fst"
let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _62_6 -> (match (_62_6) with
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
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _62_7 -> (match (_62_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 198 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _62_8 -> (match (_62_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 201 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _62_9 -> (match (_62_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 204 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _62_10 -> (match (_62_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 207 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _62_11 -> (match (_62_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 210 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _62_12 -> (match (_62_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 213 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _62_13 -> (match (_62_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _147_190 -> FStar_TypeChecker_Common.TProb (_147_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _147_191 -> FStar_TypeChecker_Common.CProb (_147_191)) (invert p))
end))

# 216 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 217 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _62_177 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _62_178 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 220 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _147_204 = (next_pid ())
in (let _147_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _147_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _147_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 233 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _147_214 = (next_pid ())
in (let _147_213 = (let _147_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _147_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _147_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _147_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 247 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _147_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _147_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 259 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 263 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _147_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _147_232 = (prob_to_string env d)
in (let _147_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _147_233 _147_232 _147_231 s)))))

# 269 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _62_14 -> (match (_62_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _62_219 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _62_222), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 284 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _62_15 -> (match (_62_15) with
| UNIV (_62_231) -> begin
None
end
| TERM ((u, _62_235), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 288 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _62_16 -> (match (_62_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _62_248 -> begin
None
end))))

# 292 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _147_252 = (let _147_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _147_251))
in (FStar_Syntax_Subst.compress _147_252)))

# 302 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _147_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _147_257)))

# 303 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _147_260 = (sn env (Prims.fst t))
in (_147_260, (Prims.snd t))))

# 304 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _62_259 -> (match (_62_259) with
| (x, imp) -> begin
(let _147_267 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _62_260 = x
in (let _147_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _62_260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_266}))
in (_147_267, imp))
end)))))

# 306 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_147_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _147_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_147_275))
end
| _62_272 -> begin
u
end)))
in (let _147_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _147_276))))

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
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _62_292; FStar_Syntax_Syntax.pos = _62_290; FStar_Syntax_Syntax.vars = _62_288} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _147_290 = (let _147_289 = (FStar_Syntax_Print.term_to_string tt)
in (let _147_288 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _147_289 _147_288)))
in (FStar_All.failwith _147_290))
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
in (match ((let _147_291 = (FStar_Syntax_Subst.compress t1')
in _147_291.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_62_310) -> begin
(aux true t1')
end
| _62_313 -> begin
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
(let _147_294 = (let _147_293 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_292 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _147_293 _147_292)))
in (FStar_All.failwith _147_294))
end))
in (let _147_295 = (whnf env t1)
in (aux false _147_295))))

# 365 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _147_300 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _147_300 Prims.fst)))

# 367 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _147_303 = (FStar_Syntax_Syntax.null_bv t)
in (_147_303, FStar_Syntax_Util.t_true)))

# 369 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _62_359 = (base_and_refinement env wl t)
in (match (_62_359) with
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
let force_refinement = (fun _62_367 -> (match (_62_367) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _62_375 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_62_375) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 381 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _62_17 -> (match (_62_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_316 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _147_315 = (let _147_312 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _147_312))
in (let _147_314 = (let _147_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _147_313))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _147_316 _147_315 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_314))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _147_319 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _147_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _147_317 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _147_319 _147_318 (rel_to_string p.FStar_TypeChecker_Common.relation) _147_317))))
end))

# 404 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _147_325 = (let _147_324 = (let _147_323 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _62_388 -> (match (_62_388) with
| (_62_384, _62_386, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _147_323))
in (FStar_List.map (wl_prob_to_string wl) _147_324))
in (FStar_All.pipe_right _147_325 (FStar_String.concat "\n\t"))))

# 407 "FStar.TypeChecker.Rel.fst"
let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (
# 417 "FStar.TypeChecker.Rel.fst"
let _62_407 = (match ((let _147_332 = (FStar_Syntax_Subst.compress k)
in _147_332.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _147_333 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _147_333))
end else begin
(
# 421 "FStar.TypeChecker.Rel.fst"
let _62_398 = (FStar_Syntax_Util.abs_formals t)
in (match (_62_398) with
| (ys', t) -> begin
(let _147_334 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _147_334))
end))
end
end
| _62_400 -> begin
(let _147_336 = (let _147_335 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _147_335))
in ((ys, t), _147_336))
end)
in (match (_62_407) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t None)
end else begin
(
# 426 "FStar.TypeChecker.Rel.fst"
let c = (let _147_337 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _147_337 c))
in (let _147_339 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_338 -> Some (_147_338)))
in (FStar_Syntax_Util.abs ys t _147_339)))
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
let _62_421 = (p_guard prob)
in (match (_62_421) with
| (_62_419, uv) -> begin
(
# 434 "FStar.TypeChecker.Rel.fst"
let _62_434 = (match ((let _147_350 = (FStar_Syntax_Subst.compress uv)
in _147_350.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 436 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 437 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _147_352 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _147_352 Prims.op_Negation)))))
in (
# 438 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs k bs phi)
in (
# 439 "FStar.TypeChecker.Rel.fst"
let _62_430 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _147_355 = (FStar_Util.string_of_int (p_pid prob))
in (let _147_354 = (FStar_Syntax_Print.term_to_string uv)
in (let _147_353 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _147_355 _147_354 _147_353))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _62_433 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 446 "FStar.TypeChecker.Rel.fst"
let _62_436 = (commit uvis)
in (
# 447 "FStar.TypeChecker.Rel.fst"
let _62_438 = wl
in {attempting = _62_438.attempting; wl_deferred = _62_438.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _62_438.defer_ok; smt_ok = _62_438.smt_ok; tcenv = _62_438.tcenv})))
end))))

# 447 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 450 "FStar.TypeChecker.Rel.fst"
let _62_443 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_364 = (FStar_Util.string_of_int pid)
in (let _147_363 = (let _147_362 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _147_362 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _147_364 _147_363)))
end else begin
()
end
in (
# 452 "FStar.TypeChecker.Rel.fst"
let _62_445 = (commit sol)
in (
# 453 "FStar.TypeChecker.Rel.fst"
let _62_447 = wl
in {attempting = _62_447.attempting; wl_deferred = _62_447.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _62_447.defer_ok; smt_ok = _62_447.smt_ok; tcenv = _62_447.tcenv}))))

# 453 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 456 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_62_457, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _147_377 = (FStar_Syntax_Util.mk_conj t f)
in Some (_147_377))
end))
in (
# 460 "FStar.TypeChecker.Rel.fst"
let _62_469 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_380 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _147_379 = (let _147_378 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _147_378 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _147_380 _147_379)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 462 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _147_390 = (let _147_388 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _147_388 FStar_Util.set_elements))
in (FStar_All.pipe_right _147_390 (FStar_Util.for_some (fun _62_478 -> (match (_62_478) with
| (uv, _62_477) -> begin
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
(let _147_397 = (let _147_396 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _147_395 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _147_396 _147_395)))
in Some (_147_397))
end
in (occurs_ok, msg))))

# 485 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 488 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 489 "FStar.TypeChecker.Rel.fst"
let _62_493 = (occurs_check env wl uk t)
in (match (_62_493) with
| (occurs_ok, msg) -> begin
(let _147_429 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _147_429, (msg, fvs, fvs_t)))
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
let _62_511 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _62_503 _62_506 -> (match ((_62_503, _62_506)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _147_438 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _147_438)) then begin
(isect, isect_set)
end else begin
(
# 502 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _147_439 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _147_439))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_62_511) with
| (isect, _62_510) -> begin
(FStar_List.rev isect)
end)))))

# 507 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _62_517 _62_521 -> (match ((_62_517, _62_521)) with
| ((a, _62_516), (b, _62_520)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 511 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 514 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _62_531 -> (match (_62_531) with
| (b, _62_530) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _62_533 -> begin
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
let _62_542 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_454 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _147_454))
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
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _62_556; FStar_Syntax_Syntax.pos = _62_554; FStar_Syntax_Syntax.vars = _62_552}, args) -> begin
(t, uv, k, args)
end
| _62_566 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 534 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 537 "FStar.TypeChecker.Rel.fst"
let _62_573 = (destruct_flex_t t)
in (match (_62_573) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _62_577 -> begin
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
| MisMatch (_62_580) -> begin
_62_580
end))

# 614 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _62_18 -> (match (_62_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _62_587 -> begin
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _62_673), FStar_Syntax_Syntax.Tm_uinst (g, _62_678)) -> begin
(let _147_490 = (head_matches env f g)
in (FStar_All.pipe_right _147_490 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _62_689), FStar_Syntax_Syntax.Tm_uvar (uv', _62_694)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _62_700), FStar_Syntax_Syntax.Tm_refine (y, _62_705)) -> begin
(let _147_491 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_491 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _62_711), _62_715) -> begin
(let _147_492 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _147_492 head_match))
end
| (_62_718, FStar_Syntax_Syntax.Tm_refine (x, _62_721)) -> begin
(let _147_493 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _147_493 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _62_741), FStar_Syntax_Syntax.Tm_app (head', _62_746)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _62_752), _62_756) -> begin
(head_matches env head t2)
end
| (_62_759, FStar_Syntax_Syntax.Tm_app (head, _62_762)) -> begin
(head_matches env t1 head)
end
| _62_767 -> begin
(let _147_496 = (let _147_495 = (delta_depth_of_term env t1)
in (let _147_494 = (delta_depth_of_term env t2)
in (_147_495, _147_494)))
in MisMatch (_147_496))
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
let _62_818 = if d1_greater_than_d2 then begin
(
# 698 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 700 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _147_517 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _147_517)))
end
in (match (_62_818) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_62_820) -> begin
(fail r)
end
| _62_823 -> begin
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
| T (_62_826) -> begin
_62_826
end))

# 711 "FStar.TypeChecker.Rel.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_62_829) -> begin
_62_829
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
| MisMatch (_62_836) -> begin
false
end
| _62_839 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 721 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 722 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_62_849, imp), T (t)) -> begin
(t, imp)
end
| _62_856 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 727 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _62_861 -> (match (_62_861) with
| (t, _62_860) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 733 "FStar.TypeChecker.Rel.fst"
let fail = (fun _62_868 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 734 "FStar.TypeChecker.Rel.fst"
let _62_871 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_62_871) with
| (bs, c) -> begin
(
# 736 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 737 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 738 "FStar.TypeChecker.Rel.fst"
let _62_888 = x
in {FStar_Syntax_Syntax.ppname = _62_888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _62_896 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 743 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _62_19 -> (match (_62_19) with
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
in (let _147_599 = (decompose [] bs)
in (rebuild, matches, _147_599))))
end)))
end
| _62_906 -> begin
(
# 754 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _62_20 -> (match (_62_20) with
| [] -> begin
t
end
| _62_910 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 758 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _62_21 -> (match (_62_21) with
| T (t) -> begin
t
end
| _62_917 -> begin
(FStar_All.failwith "Impossible")
end))

# 762 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _62_22 -> (match (_62_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _62_922 -> begin
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
| (_62_935, variance, T (ti)) -> begin
(
# 778 "FStar.TypeChecker.Rel.fst"
let k = (
# 779 "FStar.TypeChecker.Rel.fst"
let _62_943 = (FStar_Syntax_Util.type_u ())
in (match (_62_943) with
| (t, _62_942) -> begin
(let _147_621 = (new_uvar r scope t)
in (Prims.fst _147_621))
end))
in (
# 781 "FStar.TypeChecker.Rel.fst"
let _62_947 = (new_uvar r scope k)
in (match (_62_947) with
| (gi_xs, gi) -> begin
(
# 782 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _62_950 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _147_624 = (let _147_623 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _147_622 -> FStar_TypeChecker_Common.TProb (_147_622)) _147_623))
in (T (gi_xs), _147_624)))
end)))
end
| (_62_953, _62_955, C (_62_957)) -> begin
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
let _62_1035 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _62_975; FStar_Syntax_Syntax.pos = _62_973; FStar_Syntax_Syntax.vars = _62_971})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _147_633 = (let _147_632 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _147_631 -> C (_147_631)) _147_632))
in (_147_633, (prob)::[]))
end
| _62_986 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _62_994; FStar_Syntax_Syntax.pos = _62_992; FStar_Syntax_Syntax.vars = _62_990})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _147_636 = (let _147_635 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _147_634 -> C (_147_634)) _147_635))
in (_147_636, (prob)::[]))
end
| _62_1005 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_62_1007, _62_1009, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _62_1015; FStar_Syntax_Syntax.pos = _62_1013; FStar_Syntax_Syntax.vars = _62_1011})) -> begin
(
# 808 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 809 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 810 "FStar.TypeChecker.Rel.fst"
let _62_1026 = (let _147_638 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _147_638 FStar_List.unzip))
in (match (_62_1026) with
| (tcs, sub_probs) -> begin
(
# 811 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _147_643 = (let _147_642 = (let _147_639 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _147_639 un_T))
in (let _147_641 = (let _147_640 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _147_640 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_642; FStar_Syntax_Syntax.effect_args = _147_641; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _147_643))
in (C (gi_xs), sub_probs))
end))))
end
| _62_1029 -> begin
(
# 820 "FStar.TypeChecker.Rel.fst"
let _62_1032 = (sub_prob scope args q)
in (match (_62_1032) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_62_1035) with
| (tc, probs) -> begin
(
# 823 "FStar.TypeChecker.Rel.fst"
let _62_1048 = (match (q) with
| (Some (b), _62_1039, _62_1041) -> begin
(let _147_645 = (let _147_644 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_147_644)::args)
in (Some (b), (b)::scope, _147_645))
end
| _62_1044 -> begin
(None, scope, args)
end)
in (match (_62_1048) with
| (bopt, scope, args) -> begin
(
# 827 "FStar.TypeChecker.Rel.fst"
let _62_1052 = (aux scope args qs)
in (match (_62_1052) with
| (sub_probs, tcs, f) -> begin
(
# 828 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _147_648 = (let _147_647 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_147_647)
in (FStar_Syntax_Util.mk_conj_l _147_648))
end
| Some (b) -> begin
(let _147_652 = (let _147_651 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _147_650 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_147_651)::_147_650))
in (FStar_Syntax_Util.mk_conj_l _147_652))
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _62_1080), FStar_Syntax_Syntax.Tm_uvar (u2, _62_1085)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _62_1099 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _62_1105 _62_1109 -> (match ((_62_1105, _62_1109)) with
| ((a1, _62_1104), (a2, _62_1108)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 857 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 862 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 863 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 865 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 866 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 867 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 868 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 869 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 870 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 871 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 872 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 873 "FStar.TypeChecker.Rel.fst"
let _62_1112 = p
in (let _147_674 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _147_673 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _62_1112.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_674; FStar_TypeChecker_Common.relation = _62_1112.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_673; FStar_TypeChecker_Common.element = _62_1112.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1112.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1112.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1112.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1112.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_1112.FStar_TypeChecker_Common.rank}))))

# 873 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _147_680 = (compress_tprob wl p)
in (FStar_All.pipe_right _147_680 (fun _147_679 -> FStar_TypeChecker_Common.TProb (_147_679))))
end
| FStar_TypeChecker_Common.CProb (_62_1119) -> begin
p
end))

# 877 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 883 "FStar.TypeChecker.Rel.fst"
let prob = (let _147_685 = (compress_prob wl pr)
in (FStar_All.pipe_right _147_685 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 886 "FStar.TypeChecker.Rel.fst"
let _62_1129 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_62_1129) with
| (lh, _62_1128) -> begin
(
# 887 "FStar.TypeChecker.Rel.fst"
let _62_1133 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_62_1133) with
| (rh, _62_1132) -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let _62_1189 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_62_1135), FStar_Syntax_Syntax.Tm_uvar (_62_1138)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_62_1154), _62_1157) -> begin
(
# 895 "FStar.TypeChecker.Rel.fst"
let _62_1161 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_62_1161) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _62_1164 -> begin
(
# 899 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _147_687 = (
# 903 "FStar.TypeChecker.Rel.fst"
let _62_1166 = tp
in (let _147_686 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _62_1166.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_1166.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_1166.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_686; FStar_TypeChecker_Common.element = _62_1166.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1166.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1166.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1166.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1166.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_1166.FStar_TypeChecker_Common.rank}))
in (rank, _147_687)))
end)
end))
end
| (_62_1169, FStar_Syntax_Syntax.Tm_uvar (_62_1171)) -> begin
(
# 907 "FStar.TypeChecker.Rel.fst"
let _62_1176 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_62_1176) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _62_1179 -> begin
(let _147_689 = (
# 910 "FStar.TypeChecker.Rel.fst"
let _62_1180 = tp
in (let _147_688 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _62_1180.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_688; FStar_TypeChecker_Common.relation = _62_1180.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_1180.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_1180.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1180.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1180.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1180.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1180.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_1180.FStar_TypeChecker_Common.rank}))
in (refine_flex, _147_689))
end)
end))
end
| (_62_1183, _62_1185) -> begin
(rigid_rigid, tp)
end)
in (match (_62_1189) with
| (rank, tp) -> begin
(let _147_691 = (FStar_All.pipe_right (
# 915 "FStar.TypeChecker.Rel.fst"
let _62_1190 = tp
in {FStar_TypeChecker_Common.pid = _62_1190.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_1190.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_1190.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_1190.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_1190.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1190.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1190.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1190.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1190.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _147_690 -> FStar_TypeChecker_Common.TProb (_147_690)))
in (rank, _147_691))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _147_693 = (FStar_All.pipe_right (
# 917 "FStar.TypeChecker.Rel.fst"
let _62_1194 = cp
in {FStar_TypeChecker_Common.pid = _62_1194.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_1194.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_1194.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_1194.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_1194.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1194.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1194.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1194.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1194.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _147_692 -> FStar_TypeChecker_Common.CProb (_147_692)))
in (rigid_rigid, _147_693))
end)))

# 917 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 923 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _62_1201 probs -> (match (_62_1201) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 926 "FStar.TypeChecker.Rel.fst"
let _62_1209 = (rank wl hd)
in (match (_62_1209) with
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

# 937 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 939 "FStar.TypeChecker.Rel.fst"
let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

# 940 "FStar.TypeChecker.Rel.fst"
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
| UDeferred (_62_1220) -> begin
_62_1220
end))

# 947 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_62_1223) -> begin
_62_1223
end))

# 948 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_62_1226) -> begin
_62_1226
end))

# 948 "FStar.TypeChecker.Rel.fst"
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
let _62_1242 = (FStar_Syntax_Util.univ_kernel u)
in (match (_62_1242) with
| (k, _62_1241) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _62_1246 -> begin
false
end)
end)))))
end
| _62_1248 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 962 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_62_1254), FStar_Syntax_Syntax.U_max (_62_1257)) -> begin
(let _147_767 = (let _147_766 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_765 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _147_766 _147_765)))
in UFailed (_147_767))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 969 "FStar.TypeChecker.Rel.fst"
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
| _62_1277 -> begin
(let _147_774 = (let _147_773 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_772 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _147_773 _147_772 msg)))
in UFailed (_147_774))
end))
in (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(
# 990 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 995 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _147_777 = (let _147_776 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _147_775 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _147_776 _147_775)))
in (try_umax_components u1 u2 _147_777))
end else begin
(let _147_778 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_147_778))
end)
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(solve_universe_eq orig wl u1 u2)
end
| ((FStar_Syntax_Syntax.U_succ (_), _)) | ((FStar_Syntax_Syntax.U_zero, _)) | ((_, FStar_Syntax_Syntax.U_succ (_))) | ((_, FStar_Syntax_Syntax.U_zero)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
USolved (wl)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(
# 1020 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1021 "FStar.TypeChecker.Rel.fst"
let u2 = (norm_univ wl u2)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
USolved (wl)
end else begin
(try_umax_components u1 u2 "")
end))
end
end
| ((FStar_Syntax_Syntax.U_name (_), _)) | ((_, FStar_Syntax_Syntax.U_name (_))) -> begin
UFailed ("Incompatible universes")
end))))))

# 1028 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1035 "FStar.TypeChecker.Rel.fst"
let _62_1372 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_824 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _147_824))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1039 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1039 "FStar.TypeChecker.Rel.fst"
let _62_1379 = probs
in {attempting = tl; wl_deferred = _62_1379.wl_deferred; ctr = _62_1379.ctr; defer_ok = _62_1379.defer_ok; smt_ok = _62_1379.smt_ok; tcenv = _62_1379.tcenv})
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
| (None, _62_1394, _62_1396) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _62_1400 -> begin
(
# 1066 "FStar.TypeChecker.Rel.fst"
let _62_1409 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _62_1406 -> (match (_62_1406) with
| (c, _62_1403, _62_1405) -> begin
(c < probs.ctr)
end))))
in (match (_62_1409) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _147_827 = (FStar_List.map (fun _62_1415 -> (match (_62_1415) with
| (_62_1412, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_147_827))
end
| _62_1417 -> begin
(let _147_830 = (
# 1072 "FStar.TypeChecker.Rel.fst"
let _62_1418 = probs
in (let _147_829 = (FStar_All.pipe_right attempt (FStar_List.map (fun _62_1425 -> (match (_62_1425) with
| (_62_1421, _62_1423, y) -> begin
y
end))))
in {attempting = _147_829; wl_deferred = rest; ctr = _62_1418.ctr; defer_ok = _62_1418.defer_ok; smt_ok = _62_1418.smt_ok; tcenv = _62_1418.tcenv}))
in (solve env _147_830))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _147_836 = (solve_prob orig None [] wl)
in (solve env _147_836))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1086 "FStar.TypeChecker.Rel.fst"
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
| _62_1460 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _147_851 = (let _147_848 = (whnf env t1)
in _147_848.FStar_Syntax_Syntax.n)
in (let _147_850 = (let _147_849 = (whnf env t2)
in _147_849.FStar_Syntax_Syntax.n)
in (_147_851, _147_850)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _62_1466; FStar_Syntax_Syntax.pos = _62_1464; FStar_Syntax_Syntax.vars = _62_1462}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _62_1478; FStar_Syntax_Syntax.pos = _62_1476; FStar_Syntax_Syntax.vars = _62_1474}, us2)) -> begin
(
# 1101 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1102 "FStar.TypeChecker.Rel.fst"
let _62_1487 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _62_1502 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1115 "FStar.TypeChecker.Rel.fst"
let _62_1507 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_856 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _147_856 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1125 "FStar.TypeChecker.Rel.fst"
let _62_1512 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_860 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _147_860))
end else begin
()
end
in (
# 1127 "FStar.TypeChecker.Rel.fst"
let _62_1516 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_62_1516) with
| (u, args) -> begin
(
# 1129 "FStar.TypeChecker.Rel.fst"
let disjoin = (fun t1 t2 -> (
# 1130 "FStar.TypeChecker.Rel.fst"
let _62_1522 = (head_matches_delta env () t1 t2)
in (match (_62_1522) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_62_1524) -> begin
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
# 1143 "FStar.TypeChecker.Rel.fst"
let _62_1540 = (match (ts) with
| Some (t1, t2) -> begin
(let _147_866 = (FStar_Syntax_Subst.compress t1)
in (let _147_865 = (FStar_Syntax_Subst.compress t2)
in (_147_866, _147_865)))
end
| None -> begin
(let _147_868 = (FStar_Syntax_Subst.compress t1)
in (let _147_867 = (FStar_Syntax_Subst.compress t2)
in (_147_868, _147_867)))
end)
in (match (_62_1540) with
| (t1, t2) -> begin
(
# 1146 "FStar.TypeChecker.Rel.fst"
let eq_prob = (fun t1 t2 -> (let _147_874 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _147_873 -> FStar_TypeChecker_Common.TProb (_147_873)) _147_874)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _147_881 = (let _147_880 = (let _147_877 = (let _147_876 = (let _147_875 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _147_875))
in FStar_Syntax_Syntax.Tm_refine (_147_876))
in (FStar_Syntax_Syntax.mk _147_877 None t1.FStar_Syntax_Syntax.pos))
in (let _147_879 = (let _147_878 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_147_878)::[])
in (_147_880, _147_879)))
in Some (_147_881))
end
| (_62_1554, FStar_Syntax_Syntax.Tm_refine (x, _62_1557)) -> begin
(let _147_884 = (let _147_883 = (let _147_882 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_147_882)::[])
in (t1, _147_883))
in Some (_147_884))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _62_1563), _62_1567) -> begin
(let _147_887 = (let _147_886 = (let _147_885 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_147_885)::[])
in (t2, _147_886))
in Some (_147_887))
end
| _62_1570 -> begin
None
end))
end))
end)
end)))
in (
# 1162 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _62_1574) -> begin
(
# 1166 "FStar.TypeChecker.Rel.fst"
let _62_1599 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _62_23 -> (match (_62_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(
# 1170 "FStar.TypeChecker.Rel.fst"
let _62_1585 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_62_1585) with
| (u', _62_1584) -> begin
(match ((let _147_889 = (whnf env u')
in _147_889.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _62_1588) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _62_1592 -> begin
false
end)
end))
end
| _62_1594 -> begin
false
end)
end
| _62_1596 -> begin
false
end))))
in (match (_62_1599) with
| (lower_bounds, rest) -> begin
(
# 1179 "FStar.TypeChecker.Rel.fst"
let rec make_lower_bound = (fun _62_1603 tps -> (match (_62_1603) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _147_894 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _147_894))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _62_1616 -> begin
None
end)
end))
in (match ((let _147_896 = (let _147_895 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_147_895, []))
in (make_lower_bound _147_896 lower_bounds))) with
| None -> begin
(
# 1190 "FStar.TypeChecker.Rel.fst"
let _62_1618 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(
# 1195 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (
# 1196 "FStar.TypeChecker.Rel.fst"
let _62_1628 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1197 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1197 "FStar.TypeChecker.Rel.fst"
let _62_1625 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _62_1625.wl_deferred; ctr = _62_1625.ctr; defer_ok = _62_1625.defer_ok; smt_ok = _62_1625.smt_ok; tcenv = _62_1625.tcenv})
in (let _147_897 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _147_897)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1199 "FStar.TypeChecker.Rel.fst"
let _62_1630 = wl
in {attempting = sub_probs; wl_deferred = _62_1630.wl_deferred; ctr = _62_1630.ctr; defer_ok = _62_1630.defer_ok; smt_ok = _62_1630.smt_ok; tcenv = _62_1630.tcenv}))) with
| Success (_62_1633) -> begin
(
# 1201 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1201 "FStar.TypeChecker.Rel.fst"
let _62_1635 = wl
in {attempting = rest; wl_deferred = _62_1635.wl_deferred; ctr = _62_1635.ctr; defer_ok = _62_1635.defer_ok; smt_ok = _62_1635.smt_ok; tcenv = _62_1635.tcenv})
in (
# 1202 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1203 "FStar.TypeChecker.Rel.fst"
let _62_1641 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _62_1644 -> begin
None
end)))
end))
end))
end
| _62_1646 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1214 "FStar.TypeChecker.Rel.fst"
let _62_1650 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_903 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _147_903))
end else begin
()
end
in (
# 1216 "FStar.TypeChecker.Rel.fst"
let _62_1654 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_62_1654) with
| (u, args) -> begin
(
# 1217 "FStar.TypeChecker.Rel.fst"
let _62_1660 = (0, 1, 2, 3, 4)
in (match (_62_1660) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1218 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1220 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1221 "FStar.TypeChecker.Rel.fst"
let _62_1669 = (FStar_Syntax_Util.head_and_args t1)
in (match (_62_1669) with
| (h1, args1) -> begin
(
# 1222 "FStar.TypeChecker.Rel.fst"
let _62_1673 = (FStar_Syntax_Util.head_and_args t2)
in (match (_62_1673) with
| (h2, _62_1672) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _147_915 = (let _147_914 = (let _147_913 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _147_912 -> FStar_TypeChecker_Common.TProb (_147_912)) _147_913))
in (_147_914)::[])
in Some (_147_915))
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
| _62_1685 -> begin
None
end)
end))
end)))
in (
# 1238 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1240 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1244 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1245 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1246 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1247 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _147_922 = (let _147_921 = (let _147_920 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _147_920))
in (_147_921, m))
in Some (_147_922))))))
end))
end
| (_62_1707, FStar_Syntax_Syntax.Tm_refine (y, _62_1710)) -> begin
(
# 1252 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _62_1720), _62_1724) -> begin
(
# 1259 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _62_1731 -> begin
(
# 1266 "FStar.TypeChecker.Rel.fst"
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
# 1272 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _62_1739) -> begin
(
# 1276 "FStar.TypeChecker.Rel.fst"
let _62_1764 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _62_24 -> (match (_62_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1280 "FStar.TypeChecker.Rel.fst"
let _62_1750 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_62_1750) with
| (u', _62_1749) -> begin
(match ((let _147_924 = (whnf env u')
in _147_924.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _62_1753) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _62_1757 -> begin
false
end)
end))
end
| _62_1759 -> begin
false
end)
end
| _62_1761 -> begin
false
end))))
in (match (_62_1764) with
| (upper_bounds, rest) -> begin
(
# 1289 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _62_1768 tps -> (match (_62_1768) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _147_929 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _147_929))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _62_1781 -> begin
None
end)
end))
in (match ((let _147_931 = (let _147_930 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_147_930, []))
in (make_upper_bound _147_931 upper_bounds))) with
| None -> begin
(
# 1300 "FStar.TypeChecker.Rel.fst"
let _62_1783 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1313 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1314 "FStar.TypeChecker.Rel.fst"
let _62_1793 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1315 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1315 "FStar.TypeChecker.Rel.fst"
let _62_1790 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _62_1790.wl_deferred; ctr = _62_1790.ctr; defer_ok = _62_1790.defer_ok; smt_ok = _62_1790.smt_ok; tcenv = _62_1790.tcenv})
in (let _147_932 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _147_932)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1317 "FStar.TypeChecker.Rel.fst"
let _62_1795 = wl
in {attempting = sub_probs; wl_deferred = _62_1795.wl_deferred; ctr = _62_1795.ctr; defer_ok = _62_1795.defer_ok; smt_ok = _62_1795.smt_ok; tcenv = _62_1795.tcenv}))) with
| Success (_62_1798) -> begin
(
# 1319 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1319 "FStar.TypeChecker.Rel.fst"
let _62_1800 = wl
in {attempting = rest; wl_deferred = _62_1800.wl_deferred; ctr = _62_1800.ctr; defer_ok = _62_1800.defer_ok; smt_ok = _62_1800.smt_ok; tcenv = _62_1800.tcenv})
in (
# 1320 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1321 "FStar.TypeChecker.Rel.fst"
let _62_1806 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _62_1809 -> begin
None
end)))
end))
end))
end
| _62_1811 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1331 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1334 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1335 "FStar.TypeChecker.Rel.fst"
let _62_1828 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_960 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _147_960))
end else begin
()
end
in (
# 1337 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1341 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1341 "FStar.TypeChecker.Rel.fst"
let _62_1842 = hd1
in (let _147_961 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _62_1842.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1842.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_961}))
in (
# 1342 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1342 "FStar.TypeChecker.Rel.fst"
let _62_1845 = hd2
in (let _147_962 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _62_1845.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_1845.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_962}))
in (
# 1343 "FStar.TypeChecker.Rel.fst"
let prob = (let _147_965 = (let _147_964 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _147_964 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _147_963 -> FStar_TypeChecker_Common.TProb (_147_963)) _147_965))
in (
# 1344 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1345 "FStar.TypeChecker.Rel.fst"
let subst = (let _147_966 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_147_966)
in (
# 1346 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1349 "FStar.TypeChecker.Rel.fst"
let phi = (let _147_968 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _147_967 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _147_968 _147_967)))
in (
# 1350 "FStar.TypeChecker.Rel.fst"
let _62_1857 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_970 = (FStar_Syntax_Print.term_to_string phi)
in (let _147_969 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _147_970 _147_969)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _62_1861 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1359 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1363 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _147_974 = (compress_tprob wl problem)
in (solve_t' env _147_974 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1370 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1373 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1374 "FStar.TypeChecker.Rel.fst"
let _62_1889 = (head_matches_delta env wl t1 t2)
in (match (_62_1889) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_62_1891), _62_1894) -> begin
(
# 1377 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _62_1907 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1383 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1386 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1390 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _147_1003 = (let _147_1002 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _147_1002 t2))
in (FStar_Syntax_Util.mk_forall x _147_1003)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _147_1004 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _147_1004)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_62_1917, Some (t1, t2)) -> begin
(solve_t env (
# 1399 "FStar.TypeChecker.Rel.fst"
let _62_1923 = problem
in {FStar_TypeChecker_Common.pid = _62_1923.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _62_1923.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _62_1923.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1923.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1923.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1923.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1923.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_1923.FStar_TypeChecker_Common.rank}) wl)
end
| (_62_1926, None) -> begin
(
# 1402 "FStar.TypeChecker.Rel.fst"
let _62_1929 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1008 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1007 = (FStar_Syntax_Print.tag_of_term t1)
in (let _147_1006 = (FStar_Syntax_Print.term_to_string t2)
in (let _147_1005 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _147_1008 _147_1007 _147_1006 _147_1005)))))
end else begin
()
end
in (
# 1406 "FStar.TypeChecker.Rel.fst"
let _62_1933 = (FStar_Syntax_Util.head_and_args t1)
in (match (_62_1933) with
| (head, args) -> begin
(
# 1407 "FStar.TypeChecker.Rel.fst"
let _62_1936 = (FStar_Syntax_Util.head_and_args t2)
in (match (_62_1936) with
| (head', args') -> begin
(
# 1408 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _147_1013 = (let _147_1012 = (FStar_Syntax_Print.term_to_string head)
in (let _147_1011 = (args_to_string args)
in (let _147_1010 = (FStar_Syntax_Print.term_to_string head')
in (let _147_1009 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _147_1012 _147_1011 _147_1010 _147_1009)))))
in (giveup env _147_1013 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _147_1014 = (solve_prob orig None [] wl)
in (solve env _147_1014))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1429 "FStar.TypeChecker.Rel.fst"
let _62_1946 = (base_and_refinement env wl t1)
in (match (_62_1946) with
| (base1, refinement1) -> begin
(
# 1430 "FStar.TypeChecker.Rel.fst"
let _62_1949 = (base_and_refinement env wl t2)
in (match (_62_1949) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(match ((solve_maybe_uinsts env orig base1 base2 wl)) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(
# 1437 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _62_1962 _62_1966 -> (match ((_62_1962, _62_1966)) with
| ((a, _62_1961), (a', _62_1965)) -> begin
(let _147_1018 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _147_1017 -> FStar_TypeChecker_Common.TProb (_147_1017)) _147_1018))
end)) args args')
in (
# 1438 "FStar.TypeChecker.Rel.fst"
let formula = (let _147_1020 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _147_1020))
in (
# 1439 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _62_1972 -> begin
(
# 1444 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1445 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1446 "FStar.TypeChecker.Rel.fst"
let _62_1975 = problem
in {FStar_TypeChecker_Common.pid = _62_1975.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _62_1975.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _62_1975.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_1975.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_1975.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_1975.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_1975.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_1975.FStar_TypeChecker_Common.rank}) wl)))
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
# 1452 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1453 "FStar.TypeChecker.Rel.fst"
let _62_1994 = p
in (match (_62_1994) with
| (((u, k), xs, c), ps, (h, _62_1991, qs)) -> begin
(
# 1454 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1459 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1460 "FStar.TypeChecker.Rel.fst"
let _62_2000 = (imitation_sub_probs orig env xs ps qs)
in (match (_62_2000) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1461 "FStar.TypeChecker.Rel.fst"
let im = (let _147_1033 = (h gs_xs)
in (let _147_1032 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1031 -> Some (_147_1031)))
in (FStar_Syntax_Util.abs xs _147_1033 _147_1032)))
in (
# 1462 "FStar.TypeChecker.Rel.fst"
let _62_2002 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1038 = (FStar_Syntax_Print.term_to_string im)
in (let _147_1037 = (FStar_Syntax_Print.tag_of_term im)
in (let _147_1036 = (let _147_1034 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _147_1034 (FStar_String.concat ", ")))
in (let _147_1035 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _147_1038 _147_1037 _147_1036 _147_1035)))))
end else begin
()
end
in (
# 1467 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1472 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1473 "FStar.TypeChecker.Rel.fst"
let _62_2020 = p
in (match (_62_2020) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(
# 1477 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1478 "FStar.TypeChecker.Rel.fst"
let _62_2025 = (FStar_List.nth ps i)
in (match (_62_2025) with
| (pi, _62_2024) -> begin
(
# 1479 "FStar.TypeChecker.Rel.fst"
let _62_2029 = (FStar_List.nth xs i)
in (match (_62_2029) with
| (xi, _62_2028) -> begin
(
# 1481 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1482 "FStar.TypeChecker.Rel.fst"
let _62_2034 = (FStar_Syntax_Util.arrow_formals k)
in (match (_62_2034) with
| (bs, k) -> begin
(
# 1483 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _62_2042)::tl -> begin
(
# 1486 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1487 "FStar.TypeChecker.Rel.fst"
let _62_2048 = (new_uvar r xs k_a)
in (match (_62_2048) with
| (gi_xs, gi) -> begin
(
# 1488 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1489 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1490 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1491 "FStar.TypeChecker.Rel.fst"
let _62_2054 = (aux subst tl)
in (match (_62_2054) with
| (gi_xs', gi_ps') -> begin
(let _147_1060 = (let _147_1057 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_147_1057)::gi_xs')
in (let _147_1059 = (let _147_1058 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_147_1058)::gi_ps')
in (_147_1060, _147_1059)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _147_1061 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _147_1061)) then begin
None
end else begin
(
# 1497 "FStar.TypeChecker.Rel.fst"
let _62_2058 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_62_2058) with
| (g_xs, _62_2057) -> begin
(
# 1498 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1499 "FStar.TypeChecker.Rel.fst"
let proj = (let _147_1064 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _147_1063 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1062 -> Some (_147_1062)))
in (FStar_Syntax_Util.abs xs _147_1064 _147_1063)))
in (
# 1500 "FStar.TypeChecker.Rel.fst"
let sub = (let _147_1070 = (let _147_1069 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _147_1068 = (let _147_1067 = (FStar_List.map (fun _62_2066 -> (match (_62_2066) with
| (_62_2062, _62_2064, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _147_1067))
in (mk_problem (p_scope orig) orig _147_1069 (p_rel orig) _147_1068 None "projection")))
in (FStar_All.pipe_left (fun _147_1065 -> FStar_TypeChecker_Common.TProb (_147_1065)) _147_1070))
in (
# 1501 "FStar.TypeChecker.Rel.fst"
let _62_2068 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1072 = (FStar_Syntax_Print.term_to_string proj)
in (let _147_1071 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _147_1072 _147_1071)))
end else begin
()
end
in (
# 1502 "FStar.TypeChecker.Rel.fst"
let wl = (let _147_1074 = (let _147_1073 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_147_1073))
in (solve_prob orig _147_1074 ((TERM ((u, proj)))::[]) wl))
in (let _147_1076 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _147_1075 -> Some (_147_1075)) _147_1076)))))))
end))
end)
end))
end)))
end)))
in (
# 1507 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1508 "FStar.TypeChecker.Rel.fst"
let _62_2082 = lhs
in (match (_62_2082) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(
# 1509 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1510 "FStar.TypeChecker.Rel.fst"
let _62_2087 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_62_2087) with
| (xs, c) -> begin
(let _147_1091 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _147_1091))
end)))
in (
# 1513 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1516 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_62_2094) -> begin
(
# 1520 "FStar.TypeChecker.Rel.fst"
let _62_2096 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1527 "FStar.TypeChecker.Rel.fst"
let _62_2104 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1531 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1532 "FStar.TypeChecker.Rel.fst"
let _62_2114 = (FStar_Syntax_Util.head_and_args t2)
in (match (_62_2114) with
| (hd, _62_2113) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _62_2125 -> begin
(
# 1538 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1541 "FStar.TypeChecker.Rel.fst"
let _62_2127 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1102 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _147_1102))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1544 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1545 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _147_1106 = (let _147_1105 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _147_1105 Prims.fst))
in (FStar_All.pipe_right _147_1106 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1552 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1553 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1554 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1555 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1556 "FStar.TypeChecker.Rel.fst"
let _62_2140 = (occurs_check env wl (uv, k_uv) t2)
in (match (_62_2140) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _147_1108 = (let _147_1107 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _147_1107))
in (giveup_or_defer orig _147_1108))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _147_1109 = (subterms args_lhs)
in (imitate orig env wl _147_1109))
end else begin
(
# 1563 "FStar.TypeChecker.Rel.fst"
let _62_2141 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1112 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1111 = (names_to_string fvs1)
in (let _147_1110 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _147_1112 _147_1111 _147_1110))))
end else begin
()
end
in (
# 1568 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _62_2145 -> begin
(let _147_1113 = (sn_binders env vars)
in (u_abs k_uv _147_1113 t2))
end)
in (
# 1571 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1576 "FStar.TypeChecker.Rel.fst"
let _62_2148 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1116 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1115 = (names_to_string fvs1)
in (let _147_1114 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _147_1116 _147_1115 _147_1114))))
end else begin
()
end
in (let _147_1117 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _147_1117 (- (1)))))
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
if (let _147_1118 = (FStar_Syntax_Free.names t1)
in (check_head _147_1118 t2)) then begin
(
# 1588 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1589 "FStar.TypeChecker.Rel.fst"
let _62_2152 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1119 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _147_1119 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _147_1120 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _147_1120 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1614 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1617 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _62_2164 -> (match (_62_2164) with
| (t, u, k, args) -> begin
(
# 1620 "FStar.TypeChecker.Rel.fst"
let _62_2168 = (FStar_Syntax_Util.arrow_formals k)
in (match (_62_2168) with
| (all_formals, _62_2167) -> begin
(
# 1621 "FStar.TypeChecker.Rel.fst"
let _62_2169 = ()
in (
# 1623 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1631 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _62_2182 -> (match (_62_2182) with
| (x, imp) -> begin
(let _147_1142 = (FStar_Syntax_Syntax.bv_to_name x)
in (_147_1142, imp))
end))))
in (
# 1632 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1633 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1634 "FStar.TypeChecker.Rel.fst"
let _62_2188 = (FStar_Syntax_Util.type_u ())
in (match (_62_2188) with
| (t, _62_2187) -> begin
(let _147_1143 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _147_1143))
end))
in (
# 1636 "FStar.TypeChecker.Rel.fst"
let _62_2192 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_62_2192) with
| (t', tm_u1) -> begin
(
# 1637 "FStar.TypeChecker.Rel.fst"
let _62_2199 = (destruct_flex_t t')
in (match (_62_2199) with
| (_62_2194, u1, k1, _62_2198) -> begin
(
# 1638 "FStar.TypeChecker.Rel.fst"
let sol = (let _147_1145 = (let _147_1144 = (u_abs k all_formals t')
in ((u, k), _147_1144))
in TERM (_147_1145))
in (
# 1639 "FStar.TypeChecker.Rel.fst"
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
# 1648 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _62_2218 -> (match (_62_2218) with
| (x, _62_2217) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1655 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _147_1147 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _147_1147 formals tl))
end)
end)
end)
end
| _62_2222 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _147_1148 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _147_1148 all_formals args))))
end))
end))
in (
# 1667 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _62_2228 _62_2232 r -> (match ((_62_2228, _62_2232)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _147_1157 = (solve_prob orig None [] wl)
in (solve env _147_1157))
end else begin
(
# 1675 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1676 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1677 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1678 "FStar.TypeChecker.Rel.fst"
let _62_2237 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1160 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _147_1159 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _147_1158 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _147_1160 _147_1159 _147_1158))))
end else begin
()
end
in (
# 1681 "FStar.TypeChecker.Rel.fst"
let _62_2250 = (
# 1682 "FStar.TypeChecker.Rel.fst"
let _62_2242 = (FStar_Syntax_Util.type_u ())
in (match (_62_2242) with
| (t, _62_2241) -> begin
(
# 1683 "FStar.TypeChecker.Rel.fst"
let _62_2246 = (new_uvar r zs t)
in (match (_62_2246) with
| (k, _62_2245) -> begin
(new_uvar r zs k)
end))
end))
in (match (_62_2250) with
| (u_zs, _62_2249) -> begin
(
# 1685 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs k1 xs u_zs)
in (
# 1686 "FStar.TypeChecker.Rel.fst"
let _62_2254 = (occurs_check env wl (u1, k1) sub1)
in (match (_62_2254) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1689 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1691 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1693 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs k2 ys u_zs)
in (
# 1694 "FStar.TypeChecker.Rel.fst"
let _62_2260 = (occurs_check env wl (u2, k2) sub2)
in (match (_62_2260) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1697 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1698 "FStar.TypeChecker.Rel.fst"
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
# 1701 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _62_2268 _62_2273 -> (match ((_62_2268, _62_2273)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1703 "FStar.TypeChecker.Rel.fst"
let _62_2274 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1166 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1165 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _147_1166 _147_1165)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1706 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _62_2279 _62_2283 -> (match ((_62_2279, _62_2283)) with
| ((a, _62_2278), (t2, _62_2282)) -> begin
(let _147_1171 = (let _147_1169 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _147_1169 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _147_1171 (fun _147_1170 -> FStar_TypeChecker_Common.TProb (_147_1170))))
end)) xs args2)
in (
# 1709 "FStar.TypeChecker.Rel.fst"
let guard = (let _147_1173 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _147_1173))
in (
# 1710 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1713 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1714 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1715 "FStar.TypeChecker.Rel.fst"
let _62_2293 = (occurs_check env wl (u1, k1) t2)
in (match (_62_2293) with
| (occurs_ok, _62_2292) -> begin
(
# 1716 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1719 "FStar.TypeChecker.Rel.fst"
let sol = (let _147_1175 = (let _147_1174 = (u_abs k1 xs t2)
in ((u1, k1), _147_1174))
in TERM (_147_1175))
in (
# 1720 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1723 "FStar.TypeChecker.Rel.fst"
let _62_2304 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_62_2304) with
| (sol, (_62_2299, u2, k2, ys)) -> begin
(
# 1724 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1725 "FStar.TypeChecker.Rel.fst"
let _62_2306 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _147_1176 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _147_1176))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _62_2311 -> begin
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
# 1733 "FStar.TypeChecker.Rel.fst"
let _62_2316 = lhs
in (match (_62_2316) with
| (t1, u1, k1, args1) -> begin
(
# 1734 "FStar.TypeChecker.Rel.fst"
let _62_2321 = rhs
in (match (_62_2321) with
| (t2, u2, k2, args2) -> begin
(
# 1735 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1736 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1737 "FStar.TypeChecker.Rel.fst"
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
| _62_2339 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1746 "FStar.TypeChecker.Rel.fst"
let _62_2343 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_62_2343) with
| (sol, _62_2342) -> begin
(
# 1747 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1748 "FStar.TypeChecker.Rel.fst"
let _62_2345 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _147_1177 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _147_1177))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _62_2350 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1755 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _147_1178 = (solve_prob orig None [] wl)
in (solve env _147_1178))
end else begin
(
# 1757 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1758 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _147_1179 = (solve_prob orig None [] wl)
in (solve env _147_1179))
end else begin
(
# 1760 "FStar.TypeChecker.Rel.fst"
let _62_2354 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1180 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _147_1180))
end else begin
()
end
in (
# 1763 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1765 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _62_2359 _62_2362 -> (match ((_62_2359, _62_2362)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1767 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1768 "FStar.TypeChecker.Rel.fst"
let _62_2369 = (FStar_Util.first_N n bs)
in (match (_62_2369) with
| (bs, rest) -> begin
(let _147_1210 = (mk_cod rest)
in (bs, _147_1210))
end)))
in (
# 1771 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1772 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _147_1214 = (let _147_1211 = (mk_cod1 [])
in (bs1, _147_1211))
in (let _147_1213 = (let _147_1212 = (mk_cod2 [])
in (bs2, _147_1212))
in (_147_1214, _147_1213)))
end else begin
if (l1 > l2) then begin
(let _147_1217 = (curry l2 bs1 mk_cod1)
in (let _147_1216 = (let _147_1215 = (mk_cod2 [])
in (bs2, _147_1215))
in (_147_1217, _147_1216)))
end else begin
(let _147_1220 = (let _147_1218 = (mk_cod1 [])
in (bs1, _147_1218))
in (let _147_1219 = (curry l1 bs2 mk_cod2)
in (_147_1220, _147_1219)))
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
# 1790 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _62_25 -> (match (_62_25) with
| [] -> begin
c
end
| bs -> begin
(let _147_1225 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _147_1225))
end))
in (
# 1794 "FStar.TypeChecker.Rel.fst"
let _62_2412 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_62_2412) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1799 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1800 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1801 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _147_1232 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _147_1231 -> FStar_TypeChecker_Common.CProb (_147_1231)) _147_1232)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _62_2422), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _62_2428)) -> begin
(
# 1805 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _62_26 -> (match (_62_26) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1808 "FStar.TypeChecker.Rel.fst"
let _62_2443 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_62_2443) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _147_1245 = (let _147_1244 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _147_1243 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _147_1244 problem.FStar_TypeChecker_Common.relation _147_1243 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _147_1242 -> FStar_TypeChecker_Common.TProb (_147_1242)) _147_1245))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_62_2448), FStar_Syntax_Syntax.Tm_refine (_62_2451)) -> begin
(
# 1817 "FStar.TypeChecker.Rel.fst"
let _62_2456 = (as_refinement env wl t1)
in (match (_62_2456) with
| (x1, phi1) -> begin
(
# 1818 "FStar.TypeChecker.Rel.fst"
let _62_2459 = (as_refinement env wl t2)
in (match (_62_2459) with
| (x2, phi2) -> begin
(
# 1819 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _147_1247 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _147_1246 -> FStar_TypeChecker_Common.TProb (_147_1246)) _147_1247))
in (
# 1820 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1821 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1822 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1823 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1824 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1825 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _147_1264 = (imp phi1 phi2)
in (FStar_All.pipe_right _147_1264 (guard_on_element problem x1))))
in (
# 1826 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _62_2471 -> (match (()) with
| () -> begin
(
# 1827 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1831 "FStar.TypeChecker.Rel.fst"
let guard = (let _147_1267 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1267 impl))
in (
# 1832 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1835 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _147_1271 = (let _147_1270 = (let _147_1269 = (FStar_Syntax_Syntax.mk_binder x1)
in (_147_1269)::(p_scope orig))
in (mk_problem _147_1270 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _147_1268 -> FStar_TypeChecker_Common.TProb (_147_1268)) _147_1271))
in (match ((solve env (
# 1836 "FStar.TypeChecker.Rel.fst"
let _62_2476 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _62_2476.ctr; defer_ok = false; smt_ok = _62_2476.smt_ok; tcenv = _62_2476.tcenv}))) with
| Failed (_62_2479) -> begin
(fallback ())
end
| Success (_62_2482) -> begin
(
# 1839 "FStar.TypeChecker.Rel.fst"
let guard = (let _147_1274 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _147_1273 = (let _147_1272 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _147_1272 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _147_1274 _147_1273)))
in (
# 1840 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1841 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1841 "FStar.TypeChecker.Rel.fst"
let _62_2486 = wl
in {attempting = _62_2486.attempting; wl_deferred = _62_2486.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _62_2486.defer_ok; smt_ok = _62_2486.smt_ok; tcenv = _62_2486.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _147_1276 = (destruct_flex_t t1)
in (let _147_1275 = (destruct_flex_t t2)
in (flex_flex orig _147_1276 _147_1275)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _147_1277 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _147_1277 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1869 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _147_1278 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _147_1278)) then begin
(let _147_1281 = (FStar_All.pipe_left (fun _147_1279 -> FStar_TypeChecker_Common.TProb (_147_1279)) (
# 1871 "FStar.TypeChecker.Rel.fst"
let _62_2631 = problem
in {FStar_TypeChecker_Common.pid = _62_2631.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_2631.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _62_2631.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2631.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2631.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2631.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2631.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2631.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2631.FStar_TypeChecker_Common.rank}))
in (let _147_1280 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _147_1281 _147_1280 t2 wl)))
end else begin
(
# 1872 "FStar.TypeChecker.Rel.fst"
let _62_2635 = (base_and_refinement env wl t2)
in (match (_62_2635) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _147_1284 = (FStar_All.pipe_left (fun _147_1282 -> FStar_TypeChecker_Common.TProb (_147_1282)) (
# 1875 "FStar.TypeChecker.Rel.fst"
let _62_2637 = problem
in {FStar_TypeChecker_Common.pid = _62_2637.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_2637.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _62_2637.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2637.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2637.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2637.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2637.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2637.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2637.FStar_TypeChecker_Common.rank}))
in (let _147_1283 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _147_1284 _147_1283 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1878 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1878 "FStar.TypeChecker.Rel.fst"
let _62_2643 = y
in {FStar_Syntax_Syntax.ppname = _62_2643.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _62_2643.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1879 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1880 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _147_1286 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _147_1285 -> FStar_TypeChecker_Common.TProb (_147_1285)) _147_1286))
in (
# 1882 "FStar.TypeChecker.Rel.fst"
let guard = (let _147_1287 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1287 impl))
in (
# 1883 "FStar.TypeChecker.Rel.fst"
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
# 1892 "FStar.TypeChecker.Rel.fst"
let _62_2676 = (base_and_refinement env wl t1)
in (match (_62_2676) with
| (t_base, _62_2675) -> begin
(solve_t env (
# 1893 "FStar.TypeChecker.Rel.fst"
let _62_2677 = problem
in {FStar_TypeChecker_Common.pid = _62_2677.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _62_2677.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2677.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2677.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2677.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2677.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2677.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2677.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_62_2680), _62_2683) -> begin
(
# 1896 "FStar.TypeChecker.Rel.fst"
let t2 = (let _147_1288 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _147_1288))
in (solve_t env (
# 1897 "FStar.TypeChecker.Rel.fst"
let _62_2686 = problem
in {FStar_TypeChecker_Common.pid = _62_2686.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_2686.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_2686.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _62_2686.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2686.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2686.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2686.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2686.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2686.FStar_TypeChecker_Common.rank}) wl))
end
| (_62_2689, FStar_Syntax_Syntax.Tm_refine (_62_2691)) -> begin
(
# 1900 "FStar.TypeChecker.Rel.fst"
let t1 = (let _147_1289 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _147_1289))
in (solve_t env (
# 1901 "FStar.TypeChecker.Rel.fst"
let _62_2695 = problem
in {FStar_TypeChecker_Common.pid = _62_2695.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _62_2695.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_2695.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2695.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2695.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2695.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2695.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2695.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2695.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1905 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_62_2712) -> begin
t
end
| _62_2715 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _147_1294 = (
# 1908 "FStar.TypeChecker.Rel.fst"
let _62_2716 = problem
in (let _147_1293 = (maybe_eta t1)
in (let _147_1292 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _62_2716.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_1293; FStar_TypeChecker_Common.relation = _62_2716.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_1292; FStar_TypeChecker_Common.element = _62_2716.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2716.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2716.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2716.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2716.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2716.FStar_TypeChecker_Common.rank})))
in (solve_t env _147_1294 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1922 "FStar.TypeChecker.Rel.fst"
let head1 = (let _147_1295 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _147_1295 Prims.fst))
in (
# 1923 "FStar.TypeChecker.Rel.fst"
let head2 = (let _147_1296 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _147_1296 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1928 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1929 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1931 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _147_1298 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _147_1297 -> Some (_147_1297)) _147_1298))
end
in (let _147_1299 = (solve_prob orig guard [] wl)
in (solve env _147_1299)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _62_2797, _62_2799), _62_2803) -> begin
(solve_t' env (
# 1939 "FStar.TypeChecker.Rel.fst"
let _62_2805 = problem
in {FStar_TypeChecker_Common.pid = _62_2805.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _62_2805.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_2805.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2805.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2805.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2805.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2805.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2805.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2805.FStar_TypeChecker_Common.rank}) wl)
end
| (_62_2808, FStar_Syntax_Syntax.Tm_ascribed (t2, _62_2811, _62_2813)) -> begin
(solve_t' env (
# 1942 "FStar.TypeChecker.Rel.fst"
let _62_2817 = problem
in {FStar_TypeChecker_Common.pid = _62_2817.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_2817.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_2817.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _62_2817.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2817.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2817.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2817.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2817.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2817.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _147_1302 = (let _147_1301 = (FStar_Syntax_Print.tag_of_term t1)
in (let _147_1300 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _147_1301 _147_1300)))
in (FStar_All.failwith _147_1302))
end
| _62_2856 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1954 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1955 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1956 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1957 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1959 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1960 "FStar.TypeChecker.Rel.fst"
let _62_2873 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1962 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _62_2878 _62_2882 -> (match ((_62_2878, _62_2882)) with
| ((a1, _62_2877), (a2, _62_2881)) -> begin
(let _147_1317 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _147_1316 -> FStar_TypeChecker_Common.TProb (_147_1316)) _147_1317))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1965 "FStar.TypeChecker.Rel.fst"
let guard = (let _147_1319 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _147_1319))
in (
# 1966 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _147_1320 = (solve_prob orig None [] wl)
in (solve env _147_1320))
end else begin
(
# 1970 "FStar.TypeChecker.Rel.fst"
let _62_2887 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1322 = (FStar_Syntax_Print.comp_to_string c1)
in (let _147_1321 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _147_1322 (rel_to_string problem.FStar_TypeChecker_Common.relation) _147_1321)))
end else begin
()
end
in (
# 1975 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1976 "FStar.TypeChecker.Rel.fst"
let _62_2892 = (c1, c2)
in (match (_62_2892) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_62_2894), FStar_Syntax_Syntax.Total (_62_2897)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _147_1323 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _147_1323 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _147_1325 = (
# 1988 "FStar.TypeChecker.Rel.fst"
let _62_2925 = problem
in (let _147_1324 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _62_2925.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _147_1324; FStar_TypeChecker_Common.relation = _62_2925.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _62_2925.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _62_2925.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2925.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2925.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2925.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2925.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2925.FStar_TypeChecker_Common.rank}))
in (solve_c env _147_1325 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _147_1327 = (
# 1992 "FStar.TypeChecker.Rel.fst"
let _62_2941 = problem
in (let _147_1326 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _62_2941.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _62_2941.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _62_2941.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _147_1326; FStar_TypeChecker_Common.element = _62_2941.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _62_2941.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _62_2941.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _62_2941.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _62_2941.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _62_2941.FStar_TypeChecker_Common.rank}))
in (solve_c env _147_1327 wl))
end
| (FStar_Syntax_Syntax.Comp (_62_2944), FStar_Syntax_Syntax.Comp (_62_2947)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _147_1328 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _147_1328 wl))
end else begin
(
# 1998 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1999 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2003 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 2004 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 2005 "FStar.TypeChecker.Rel.fst"
let _62_2954 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _147_1331 = (let _147_1330 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _147_1329 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _147_1330 _147_1329)))
in (giveup env _147_1331 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 2012 "FStar.TypeChecker.Rel.fst"
let _62_2972 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _62_2965)::(wlp1, _62_2961)::[] -> begin
(wp1, wlp1)
end
| _62_2969 -> begin
(let _147_1333 = (let _147_1332 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _147_1332))
in (FStar_All.failwith _147_1333))
end)
in (match (_62_2972) with
| (wp, wlp) -> begin
(
# 2015 "FStar.TypeChecker.Rel.fst"
let c1 = (let _147_1339 = (let _147_1338 = (let _147_1334 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _147_1334))
in (let _147_1337 = (let _147_1336 = (let _147_1335 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _147_1335))
in (_147_1336)::[])
in (_147_1338)::_147_1337))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _147_1339; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2022 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _62_27 -> (match (_62_27) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _62_2979 -> begin
false
end))))
in (
# 2023 "FStar.TypeChecker.Rel.fst"
let _62_3000 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _62_2985)::_62_2982, (wp2, _62_2992)::_62_2989) -> begin
(wp1, wp2)
end
| _62_2997 -> begin
(let _147_1343 = (let _147_1342 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _147_1341 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _147_1342 _147_1341)))
in (FStar_All.failwith _147_1343))
end)
in (match (_62_3000) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _147_1344 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _147_1344 wl))
end else begin
(
# 2030 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 2031 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2033 "FStar.TypeChecker.Rel.fst"
let _62_3002 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _147_1354 = (let _147_1353 = (let _147_1352 = (let _147_1346 = (let _147_1345 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_147_1345)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _147_1346 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _147_1351 = (let _147_1350 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _147_1349 = (let _147_1348 = (let _147_1347 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_1347))
in (_147_1348)::[])
in (_147_1350)::_147_1349))
in (_147_1352, _147_1351)))
in FStar_Syntax_Syntax.Tm_app (_147_1353))
in (FStar_Syntax_Syntax.mk _147_1354 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 2037 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _147_1370 = (let _147_1369 = (let _147_1368 = (let _147_1356 = (let _147_1355 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_147_1355)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _147_1356 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _147_1367 = (let _147_1366 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _147_1365 = (let _147_1364 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _147_1363 = (let _147_1362 = (let _147_1358 = (let _147_1357 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _147_1357 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_1358))
in (let _147_1361 = (let _147_1360 = (let _147_1359 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _147_1359))
in (_147_1360)::[])
in (_147_1362)::_147_1361))
in (_147_1364)::_147_1363))
in (_147_1366)::_147_1365))
in (_147_1368, _147_1367)))
in FStar_Syntax_Syntax.Tm_app (_147_1369))
in (FStar_Syntax_Syntax.mk _147_1370 None r))
in (let _147_1379 = (let _147_1378 = (let _147_1377 = (let _147_1372 = (let _147_1371 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_147_1371)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _147_1372 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _147_1376 = (let _147_1375 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _147_1374 = (let _147_1373 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_147_1373)::[])
in (_147_1375)::_147_1374))
in (_147_1377, _147_1376)))
in FStar_Syntax_Syntax.Tm_app (_147_1378))
in (FStar_Syntax_Syntax.mk _147_1379 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 2044 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _147_1381 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _147_1380 -> FStar_TypeChecker_Common.TProb (_147_1380)) _147_1381))
in (
# 2045 "FStar.TypeChecker.Rel.fst"
let wl = (let _147_1385 = (let _147_1384 = (let _147_1383 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _147_1383 g))
in (FStar_All.pipe_left (fun _147_1382 -> Some (_147_1382)) _147_1384))
in (solve_prob orig _147_1385 [] wl))
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

# 2047 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _147_1389 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _62_3018 -> (match (_62_3018) with
| (_62_3010, u, _62_3013, _62_3015, _62_3017) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _147_1389 (FStar_String.concat ", "))))

# 2052 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _62_3025 -> begin
(
# 2058 "FStar.TypeChecker.Rel.fst"
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
# 2065 "FStar.TypeChecker.Rel.fst"
let carry = (let _147_1395 = (FStar_List.map (fun _62_3033 -> (match (_62_3033) with
| (_62_3031, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _147_1395 (FStar_String.concat ",\n")))
in (
# 2066 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 2067 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 2072 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 2074 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _62_3042; FStar_TypeChecker_Env.implicits = _62_3040} -> begin
true
end
| _62_3047 -> begin
false
end))

# 2078 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 2080 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2086 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _62_3065 -> begin
(FStar_All.failwith "impossible")
end)
in (let _147_1414 = (
# 2089 "FStar.TypeChecker.Rel.fst"
let _62_3067 = g
in (let _147_1413 = (let _147_1412 = (let _147_1411 = (let _147_1407 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_1407)::[])
in (let _147_1410 = (let _147_1409 = (let _147_1408 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _147_1408 FStar_Syntax_Util.lcomp_of_comp))
in Some (_147_1409))
in (FStar_Syntax_Util.abs _147_1411 f _147_1410)))
in (FStar_All.pipe_left (fun _147_1406 -> FStar_TypeChecker_Common.NonTrivial (_147_1406)) _147_1412))
in {FStar_TypeChecker_Env.guard_f = _147_1413; FStar_TypeChecker_Env.deferred = _62_3067.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3067.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3067.FStar_TypeChecker_Env.implicits}))
in Some (_147_1414)))
end))

# 2089 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2093 "FStar.TypeChecker.Rel.fst"
let _62_3074 = g
in (let _147_1425 = (let _147_1424 = (let _147_1423 = (let _147_1422 = (let _147_1421 = (let _147_1420 = (FStar_Syntax_Syntax.as_arg e)
in (_147_1420)::[])
in (f, _147_1421))
in FStar_Syntax_Syntax.Tm_app (_147_1422))
in (FStar_Syntax_Syntax.mk _147_1423 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _147_1419 -> FStar_TypeChecker_Common.NonTrivial (_147_1419)) _147_1424))
in {FStar_TypeChecker_Env.guard_f = _147_1425; FStar_TypeChecker_Env.deferred = _62_3074.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3074.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3074.FStar_TypeChecker_Env.implicits}))
end))

# 2093 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_62_3079) -> begin
(FStar_All.failwith "impossible")
end))

# 2097 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _147_1432 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_147_1432))
end))

# 2102 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _62_3097 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 2106 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2112 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2112 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _147_1455 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _147_1455; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2117 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2118 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2119 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2123 "FStar.TypeChecker.Rel.fst"
let _62_3124 = g
in (let _147_1470 = (let _147_1469 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _147_1469 (fun _147_1468 -> FStar_TypeChecker_Common.NonTrivial (_147_1468))))
in {FStar_TypeChecker_Env.guard_f = _147_1470; FStar_TypeChecker_Env.deferred = _62_3124.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3124.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3124.FStar_TypeChecker_Env.implicits}))
end))

# 2123 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2129 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _147_1478 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _147_1477 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _147_1478 (rel_to_string rel) _147_1477)))
end else begin
"TOP"
end
in (
# 2134 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2135 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2138 "FStar.TypeChecker.Rel.fst"
let x = (let _147_1489 = (let _147_1488 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _147_1487 -> Some (_147_1487)) _147_1488))
in (FStar_Syntax_Syntax.new_bv _147_1489 t1))
in (
# 2139 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2140 "FStar.TypeChecker.Rel.fst"
let p = (let _147_1493 = (let _147_1491 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _147_1490 -> Some (_147_1490)) _147_1491))
in (let _147_1492 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _147_1493 _147_1492)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2141 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2144 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2144 "FStar.TypeChecker.Rel.fst"
let _62_3144 = probs
in {attempting = _62_3144.attempting; wl_deferred = _62_3144.wl_deferred; ctr = _62_3144.ctr; defer_ok = false; smt_ok = _62_3144.smt_ok; tcenv = _62_3144.tcenv})
end else begin
probs
end
in (
# 2145 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2146 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2149 "FStar.TypeChecker.Rel.fst"
let _62_3151 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2152 "FStar.TypeChecker.Rel.fst"
let _62_3157 = (FStar_Unionfind.rollback tx)
in (
# 2153 "FStar.TypeChecker.Rel.fst"
let _62_3159 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _147_1505 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _147_1505))
end else begin
()
end
in (err (d, s))))
end)))))

# 2155 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2160 "FStar.TypeChecker.Rel.fst"
let _62_3166 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _147_1510 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _147_1510))
end else begin
()
end
in (
# 2161 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2162 "FStar.TypeChecker.Rel.fst"
let _62_3169 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _147_1511 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _147_1511))
end else begin
()
end
in (
# 2163 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _147_1512 = (FStar_Syntax_Util.unmeta f)
in _147_1512.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _62_3174 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2166 "FStar.TypeChecker.Rel.fst"
let _62_3176 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _62_3176.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3176.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3176.FStar_TypeChecker_Env.implicits})))))
end))

# 2166 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _147_1524 = (let _147_1523 = (let _147_1522 = (let _147_1521 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _147_1521 (fun _147_1520 -> FStar_TypeChecker_Common.NonTrivial (_147_1520))))
in {FStar_TypeChecker_Env.guard_f = _147_1522; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _147_1523))
in (FStar_All.pipe_left (fun _147_1519 -> Some (_147_1519)) _147_1524))
end))

# 2171 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2174 "FStar.TypeChecker.Rel.fst"
let _62_3187 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1532 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1531 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _147_1532 _147_1531)))
end else begin
()
end
in (
# 2176 "FStar.TypeChecker.Rel.fst"
let prob = (let _147_1535 = (let _147_1534 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _147_1534))
in (FStar_All.pipe_left (fun _147_1533 -> FStar_TypeChecker_Common.TProb (_147_1533)) _147_1535))
in (
# 2177 "FStar.TypeChecker.Rel.fst"
let g = (let _147_1537 = (solve_and_commit env (singleton env prob) (fun _62_3190 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1537))
in g))))

# 2178 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _147_1547 = (let _147_1546 = (let _147_1545 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _147_1544 = (FStar_TypeChecker_Env.get_range env)
in (_147_1545, _147_1544)))
in FStar_Syntax_Syntax.Error (_147_1546))
in (Prims.raise _147_1547))
end
| Some (g) -> begin
(
# 2184 "FStar.TypeChecker.Rel.fst"
let _62_3199 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1550 = (FStar_Syntax_Print.term_to_string t1)
in (let _147_1549 = (FStar_Syntax_Print.term_to_string t2)
in (let _147_1548 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _147_1550 _147_1549 _147_1548))))
end else begin
()
end
in g)
end))

# 2189 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2192 "FStar.TypeChecker.Rel.fst"
let _62_3204 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1558 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _147_1557 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _147_1558 _147_1557)))
end else begin
()
end
in (
# 2194 "FStar.TypeChecker.Rel.fst"
let _62_3208 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_62_3208) with
| (prob, x) -> begin
(
# 2195 "FStar.TypeChecker.Rel.fst"
let g = (let _147_1560 = (solve_and_commit env (singleton env prob) (fun _62_3209 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1560))
in (
# 2196 "FStar.TypeChecker.Rel.fst"
let _62_3212 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _147_1564 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _147_1563 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _147_1562 = (let _147_1561 = (FStar_Util.must g)
in (guard_to_string env _147_1561))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _147_1564 _147_1563 _147_1562))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2202 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _147_1571 = (let _147_1570 = (let _147_1569 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _147_1568 = (FStar_TypeChecker_Env.get_range env)
in (_147_1569, _147_1568)))
in FStar_Syntax_Syntax.Error (_147_1570))
in (Prims.raise _147_1571)))

# 2205 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2209 "FStar.TypeChecker.Rel.fst"
let _62_3220 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1579 = (FStar_Syntax_Print.comp_to_string c1)
in (let _147_1578 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _147_1579 _147_1578)))
end else begin
()
end
in (
# 2211 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2212 "FStar.TypeChecker.Rel.fst"
let prob = (let _147_1582 = (let _147_1581 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _147_1581 "sub_comp"))
in (FStar_All.pipe_left (fun _147_1580 -> FStar_TypeChecker_Common.CProb (_147_1580)) _147_1582))
in (let _147_1584 = (solve_and_commit env (singleton env prob) (fun _62_3224 -> None))
in (FStar_All.pipe_left (with_guard env prob) _147_1584))))))

# 2213 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2217 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2218 "FStar.TypeChecker.Rel.fst"
let _62_3233 = (FStar_Unionfind.rollback tx)
in (
# 2219 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _147_1602 = (let _147_1601 = (let _147_1600 = (let _147_1598 = (FStar_Syntax_Print.univ_to_string u1)
in (let _147_1597 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _147_1598 _147_1597 msg)))
in (let _147_1599 = (FStar_TypeChecker_Env.get_range env)
in (_147_1600, _147_1599)))
in FStar_Syntax_Syntax.Error (_147_1601))
in (Prims.raise _147_1602)))))
in (
# 2228 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2231 "FStar.TypeChecker.Rel.fst"
let _62_3249 = hd
in (match (_62_3249) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _147_1609 = (insert uv u1 tl)
in (hd)::_147_1609)
end
end))
end))
in (
# 2236 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2239 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2242 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _147_1614 = (insert uv u1 out)
in (group_by _147_1614 rest))
end)
end
| _62_3264 -> begin
None
end))
end))
in (
# 2249 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _62_3266 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _62_3269 -> begin
(
# 2254 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2254 "FStar.TypeChecker.Rel.fst"
let _62_3270 = (empty_worklist env)
in {attempting = _62_3270.attempting; wl_deferred = _62_3270.wl_deferred; ctr = _62_3270.ctr; defer_ok = true; smt_ok = _62_3270.smt_ok; tcenv = _62_3270.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _62_3275 -> (match (_62_3275) with
| (u1, u2) -> begin
(
# 2256 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2257 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _62_3280 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2263 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _62_3290 -> begin
(u1)::[]
end)
in (
# 2266 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _62_3295 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _62_28 -> (match (_62_28) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2272 "FStar.TypeChecker.Rel.fst"
let _62_3302 = (FStar_Syntax_Util.univ_kernel u)
in (match (_62_3302) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2274 "FStar.TypeChecker.Rel.fst"
let _62_3306 = (FStar_Syntax_Util.univ_kernel u')
in (match (_62_3306) with
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
| USolved (_62_3308) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2284 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2284 "FStar.TypeChecker.Rel.fst"
let _62_3312 = (empty_worklist env)
in {attempting = _62_3312.attempting; wl_deferred = _62_3312.wl_deferred; ctr = _62_3312.ctr; defer_ok = false; smt_ok = _62_3312.smt_ok; tcenv = _62_3312.tcenv})
in (
# 2285 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _62_3327 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2295 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2298 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2299 "FStar.TypeChecker.Rel.fst"
let _62_3332 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2300 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2303 "FStar.TypeChecker.Rel.fst"
let fail = (fun _62_3339 -> (match (_62_3339) with
| (d, s) -> begin
(
# 2304 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2306 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2307 "FStar.TypeChecker.Rel.fst"
let _62_3342 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1635 = (wl_to_string wl)
in (let _147_1634 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _147_1635 _147_1634)))
end else begin
()
end
in (
# 2309 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2310 "FStar.TypeChecker.Rel.fst"
let _62_3346 = g
in {FStar_TypeChecker_Env.guard_f = _62_3346.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _62_3346.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3346.FStar_TypeChecker_Env.implicits})
end
| _62_3349 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2312 "FStar.TypeChecker.Rel.fst"
let _62_3351 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2313 "FStar.TypeChecker.Rel.fst"
let _62_3353 = g
in {FStar_TypeChecker_Env.guard_f = _62_3353.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _62_3353.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _62_3353.FStar_TypeChecker_Env.implicits})))))))

# 2313 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2316 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2317 "FStar.TypeChecker.Rel.fst"
let _62_3368 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2321 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2325 "FStar.TypeChecker.Rel.fst"
let _62_3366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _147_1652 = (FStar_TypeChecker_Env.get_range env)
in (let _147_1651 = (let _147_1650 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _147_1650))
in (FStar_TypeChecker_Errors.diag _147_1652 _147_1651)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2330 "FStar.TypeChecker.Rel.fst"
let _62_3370 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_3370.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3370.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3370.FStar_TypeChecker_Env.implicits}))))

# 2330 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2332 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2335 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _62_3379 -> begin
false
end))
in (
# 2338 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _62_3383 implicits -> (match (_62_3383) with
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
# 2342 "FStar.TypeChecker.Rel.fst"
let _62_3394 = hd
in (match (_62_3394) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2345 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2346 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2347 "FStar.TypeChecker.Rel.fst"
let _62_3397 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _147_1668 = (FStar_Syntax_Print.uvar_to_string u)
in (let _147_1667 = (FStar_Syntax_Print.term_to_string tm)
in (let _147_1666 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _147_1668 _147_1667 _147_1666))))
end else begin
()
end
in (
# 2350 "FStar.TypeChecker.Rel.fst"
let _62_3404 = (env.FStar_TypeChecker_Env.type_of (
# 2350 "FStar.TypeChecker.Rel.fst"
let _62_3399 = env
in {FStar_TypeChecker_Env.solver = _62_3399.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _62_3399.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _62_3399.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _62_3399.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _62_3399.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _62_3399.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _62_3399.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _62_3399.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _62_3399.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _62_3399.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _62_3399.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _62_3399.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _62_3399.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _62_3399.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _62_3399.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _62_3399.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _62_3399.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _62_3399.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _62_3399.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _62_3399.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _62_3399.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_62_3404) with
| (_62_3402, g) -> begin
(
# 2351 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2352 "FStar.TypeChecker.Rel.fst"
let _62_3405 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _62_3405.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3405.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _62_3405.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2354 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _62_3408 -> (match (()) with
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
# 2356 "FStar.TypeChecker.Rel.fst"
let _62_3410 = g
in (let _147_1672 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _62_3410.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _62_3410.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _62_3410.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _147_1672})))))

# 2356 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2359 "FStar.TypeChecker.Rel.fst"
let g = (let _147_1677 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _147_1677 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _147_1678 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _147_1678))
end
| (_62_3419, _62_3421, _62_3423, _62_3425, r)::_62_3417 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2362 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2366 "FStar.TypeChecker.Rel.fst"
let _62_3431 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _62_3431.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _62_3431.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _62_3431.FStar_TypeChecker_Env.implicits}))





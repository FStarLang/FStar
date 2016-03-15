
open Prims
# 65 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _145_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _145_8 Prims.op_Negation)))))
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
| _61_38 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _145_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _145_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _145_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_145_10, uv)))))
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
let ___TERM____0 : uvi  ->  ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_61_44) -> begin
_61_44
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_61_47) -> begin
_61_47
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
let ___Success____0 : solution  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| Success (_61_57) -> begin
_61_57
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_61_60) -> begin
_61_60
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
let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _61_1 -> (match (_61_1) with
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
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _61_2 -> (match (_61_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _145_109 = (let _145_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _145_107 = (let _145_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _145_105 = (let _145_104 = (let _145_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _145_102 = (let _145_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _145_100 = (let _145_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _145_98 = (let _145_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_145_97)::[])
in (_145_99)::_145_98))
in (_145_101)::_145_100))
in (_145_103)::_145_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_145_104)
in (_145_106)::_145_105))
in (_145_108)::_145_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _145_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _145_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _145_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _145_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_110)))
end))

# 140 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _61_3 -> (match (_61_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _145_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_116 FStar_Util.string_of_int))
end
in (let _145_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _145_117)))
end
| TERM ((u, _61_84), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _145_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _145_118 FStar_Util.string_of_int))
end
in (let _145_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _145_119)))
end))

# 148 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _145_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _145_124 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _145_134 = (let _145_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _145_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _145_134 (FStar_String.concat ", "))))

# 150 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _145_137 = (FStar_All.pipe_right args (FStar_List.map (fun _61_97 -> (match (_61_97) with
| (x, _61_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _145_137 (FStar_String.concat " "))))

# 159 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 167 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _61_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _61_101.wl_deferred; ctr = _61_101.ctr; defer_ok = _61_101.defer_ok; smt_ok = _61_101.smt_ok; tcenv = _61_101.tcenv}))

# 168 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _61_105 = (empty_worklist env)
in (let _145_146 = (FStar_List.map Prims.snd g)
in {attempting = _145_146; wl_deferred = _61_105.wl_deferred; ctr = _61_105.ctr; defer_ok = false; smt_ok = _61_105.smt_ok; tcenv = _61_105.tcenv})))

# 169 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _61_110 = wl
in {attempting = _61_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _61_110.ctr; defer_ok = _61_110.defer_ok; smt_ok = _61_110.smt_ok; tcenv = _61_110.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _61_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _61_114.wl_deferred; ctr = _61_114.ctr; defer_ok = _61_114.defer_ok; smt_ok = _61_114.smt_ok; tcenv = _61_114.tcenv}))

# 172 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _61_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _145_163))
end else begin
()
end
in Failed ((prob, reason))))

# 183 "FStar.TypeChecker.Rel.fst"
let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _61_4 -> (match (_61_4) with
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
let _61_126 = p
in {FStar_TypeChecker_Common.pid = _61_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _61_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_126.FStar_TypeChecker_Common.rank}))

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 189 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _61_5 -> (match (_61_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _145_170 -> FStar_TypeChecker_Common.TProb (_145_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _145_171 -> FStar_TypeChecker_Common.CProb (_145_171)))
end))

# 192 "FStar.TypeChecker.Rel.fst"
let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _61_6 -> (match (_61_6) with
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
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _61_7 -> (match (_61_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 199 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _61_8 -> (match (_61_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 202 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _61_9 -> (match (_61_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 205 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _61_10 -> (match (_61_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 208 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _61_11 -> (match (_61_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 211 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _61_12 -> (match (_61_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 214 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _61_13 -> (match (_61_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _145_190 -> FStar_TypeChecker_Common.TProb (_145_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _145_191 -> FStar_TypeChecker_Common.CProb (_145_191)) (invert p))
end))

# 217 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 218 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _61_176 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _61_177 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 222 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _145_204 = (next_pid ())
in (let _145_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _145_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 234 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _145_214 = (next_pid ())
in (let _145_213 = (let _145_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _145_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _145_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _145_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 248 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _145_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _145_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 260 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 264 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _145_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _145_232 = (prob_to_string env d)
in (let _145_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _145_233 _145_232 _145_231 s)))))

# 278 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _61_14 -> (match (_61_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _61_218 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _61_221), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 286 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _61_15 -> (match (_61_15) with
| UNIV (_61_230) -> begin
None
end
| TERM ((u, _61_234), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 290 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _61_16 -> (match (_61_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _61_247 -> begin
None
end))))

# 302 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_252 = (let _145_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _145_251))
in (FStar_Syntax_Subst.compress _145_252)))

# 303 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _145_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _145_257)))

# 304 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _145_260 = (sn env (Prims.fst t))
in (_145_260, (Prims.snd t))))

# 305 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _61_258 -> (match (_61_258) with
| (x, imp) -> begin
(let _145_267 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _61_259 = x
in (let _145_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _61_259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_266}))
in (_145_267, imp))
end)))))

# 312 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _145_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_145_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _145_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_145_275))
end
| _61_271 -> begin
u
end)))
in (let _145_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _145_276))))

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
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _61_291; FStar_Syntax_Syntax.pos = _61_289; FStar_Syntax_Syntax.vars = _61_287} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _145_290 = (let _145_289 = (FStar_Syntax_Print.term_to_string tt)
in (let _145_288 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _145_289 _145_288)))
in (FStar_All.failwith _145_290))
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
in (match ((let _145_291 = (FStar_Syntax_Subst.compress t1')
in _145_291.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_61_309) -> begin
(aux true t1')
end
| _61_312 -> begin
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
(let _145_294 = (let _145_293 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_292 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _145_293 _145_292)))
in (FStar_All.failwith _145_294))
end))
in (let _145_295 = (whnf env t1)
in (aux false _145_295))))

# 367 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _145_300 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _145_300 Prims.fst)))

# 369 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _145_303 = (FStar_Syntax_Syntax.null_bv t)
in (_145_303, FStar_Syntax_Util.t_true)))

# 371 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _61_358 = (base_and_refinement env wl t)
in (match (_61_358) with
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
let force_refinement = (fun _61_366 -> (match (_61_366) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _61_374 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_61_374) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 391 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _61_17 -> (match (_61_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _145_316 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_315 = (let _145_312 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _145_312))
in (let _145_314 = (let _145_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _145_313))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_316 _145_315 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_314))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _145_319 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _145_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_317 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _145_319 _145_318 (rel_to_string p.FStar_TypeChecker_Common.relation) _145_317))))
end))

# 406 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _145_325 = (let _145_324 = (let _145_323 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _61_387 -> (match (_61_387) with
| (_61_383, _61_385, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _145_323))
in (FStar_List.map (wl_prob_to_string wl) _145_324))
in (FStar_All.pipe_right _145_325 (FStar_String.concat "\n\t"))))

# 416 "FStar.TypeChecker.Rel.fst"
let u_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun x y -> (FStar_Syntax_Util.abs x y None))

# 418 "FStar.TypeChecker.Rel.fst"
let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (
# 419 "FStar.TypeChecker.Rel.fst"
let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (
# 422 "FStar.TypeChecker.Rel.fst"
let _61_402 = (p_guard prob)
in (match (_61_402) with
| (_61_400, uv) -> begin
(
# 423 "FStar.TypeChecker.Rel.fst"
let _61_415 = (match ((let _145_340 = (FStar_Syntax_Subst.compress uv)
in _145_340.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 425 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 426 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _145_342 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _145_342 Prims.op_Negation)))))
in (
# 427 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs bs phi)
in (
# 428 "FStar.TypeChecker.Rel.fst"
let _61_411 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _145_345 = (FStar_Util.string_of_int (p_pid prob))
in (let _145_344 = (FStar_Syntax_Print.term_to_string uv)
in (let _145_343 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _145_345 _145_344 _145_343))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _61_414 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 435 "FStar.TypeChecker.Rel.fst"
let _61_417 = (commit uvis)
in (
# 436 "FStar.TypeChecker.Rel.fst"
let _61_419 = wl
in {attempting = _61_419.attempting; wl_deferred = _61_419.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _61_419.defer_ok; smt_ok = _61_419.smt_ok; tcenv = _61_419.tcenv})))
end))))

# 438 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 439 "FStar.TypeChecker.Rel.fst"
let _61_424 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_354 = (FStar_Util.string_of_int pid)
in (let _145_353 = (let _145_352 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _145_352 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_354 _145_353)))
end else begin
()
end
in (
# 441 "FStar.TypeChecker.Rel.fst"
let _61_426 = (commit sol)
in (
# 442 "FStar.TypeChecker.Rel.fst"
let _61_428 = wl
in {attempting = _61_428.attempting; wl_deferred = _61_428.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _61_428.defer_ok; smt_ok = _61_428.smt_ok; tcenv = _61_428.tcenv}))))

# 444 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 445 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_61_438, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _145_367 = (FStar_Syntax_Util.mk_conj t f)
in Some (_145_367))
end))
in (
# 449 "FStar.TypeChecker.Rel.fst"
let _61_450 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_370 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _145_369 = (let _145_368 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _145_368 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _145_370 _145_369)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 461 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _145_380 = (let _145_378 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _145_378 FStar_Util.set_elements))
in (FStar_All.pipe_right _145_380 (FStar_Util.for_some (fun _61_459 -> (match (_61_459) with
| (uv, _61_458) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 467 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 468 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 469 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _145_387 = (let _145_386 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _145_385 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _145_386 _145_385)))
in Some (_145_387))
end
in (occurs_ok, msg))))

# 476 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 477 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 478 "FStar.TypeChecker.Rel.fst"
let _61_474 = (occurs_check env wl uk t)
in (match (_61_474) with
| (occurs_ok, msg) -> begin
(let _145_419 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _145_419, (msg, fvs, fvs_t)))
end))))

# 481 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 482 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 484 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 485 "FStar.TypeChecker.Rel.fst"
let _61_492 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _61_484 _61_487 -> (match ((_61_484, _61_487)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _145_428 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _145_428)) then begin
(isect, isect_set)
end else begin
(
# 491 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _145_429 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _145_429))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_61_492) with
| (isect, _61_491) -> begin
(FStar_List.rev isect)
end)))))

# 498 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _61_498 _61_502 -> (match ((_61_498, _61_502)) with
| ((a, _61_497), (b, _61_501)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 502 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 503 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _61_512 -> (match (_61_512) with
| (b, _61_511) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _61_514 -> begin
None
end)))

# 512 "FStar.TypeChecker.Rel.fst"
let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 516 "FStar.TypeChecker.Rel.fst"
let _61_523 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_444 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _145_444))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 520 "FStar.TypeChecker.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _61_537; FStar_Syntax_Syntax.pos = _61_535; FStar_Syntax_Syntax.vars = _61_533}, args) -> begin
(t, uv, k, args)
end
| _61_547 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 525 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 526 "FStar.TypeChecker.Rel.fst"
let _61_554 = (destruct_flex_t t)
in (match (_61_554) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _61_558 -> begin
((t, uv, k, args), None)
end)
end)))

# 600 "FStar.TypeChecker.Rel.fst"
type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch

# 601 "FStar.TypeChecker.Rel.fst"
let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 602 "FStar.TypeChecker.Rel.fst"
let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 603 "FStar.TypeChecker.Rel.fst"
let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 601 "FStar.TypeChecker.Rel.fst"
let ___MisMatch____0 : match_result  ->  (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option) = (fun projectee -> (match (projectee) with
| MisMatch (_61_561) -> begin
_61_561
end))

# 605 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _61_18 -> (match (_61_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _61_568 -> begin
HeadMatch
end))

# 609 "FStar.TypeChecker.Rel.fst"
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

# 616 "FStar.TypeChecker.Rel.fst"
let rec delta_depth_of_term : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth Prims.option = (fun env t -> (
# 617 "FStar.TypeChecker.Rel.fst"
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

# 638 "FStar.TypeChecker.Rel.fst"
let rec head_matches : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun env t1 t2 -> (
# 639 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Util.unmeta t1)
in (
# 640 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _61_654), FStar_Syntax_Syntax.Tm_uinst (g, _61_659)) -> begin
(let _145_480 = (head_matches env f g)
in (FStar_All.pipe_right _145_480 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _61_670), FStar_Syntax_Syntax.Tm_uvar (uv', _61_675)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _61_681), FStar_Syntax_Syntax.Tm_refine (y, _61_686)) -> begin
(let _145_481 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_481 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _61_692), _61_696) -> begin
(let _145_482 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _145_482 head_match))
end
| (_61_699, FStar_Syntax_Syntax.Tm_refine (x, _61_702)) -> begin
(let _145_483 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _145_483 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _61_722), FStar_Syntax_Syntax.Tm_app (head', _61_727)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _61_733), _61_737) -> begin
(head_matches env head t2)
end
| (_61_740, FStar_Syntax_Syntax.Tm_app (head, _61_743)) -> begin
(head_matches env t1 head)
end
| _61_748 -> begin
(let _145_486 = (let _145_485 = (delta_depth_of_term env t1)
in (let _145_484 = (delta_depth_of_term env t2)
in (_145_485, _145_484)))
in MisMatch (_145_486))
end))))

# 663 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 664 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 665 "FStar.TypeChecker.Rel.fst"
let fail = (fun r -> (r, None))
in (
# 666 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun n_delta t1 t2 -> (
# 667 "FStar.TypeChecker.Rel.fst"
let r = (head_matches env t1 t2)
in (match (r) with
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(
# 675 "FStar.TypeChecker.Rel.fst"
let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (
# 676 "FStar.TypeChecker.Rel.fst"
let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(
# 685 "FStar.TypeChecker.Rel.fst"
let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (
# 686 "FStar.TypeChecker.Rel.fst"
let _61_799 = if d1_greater_than_d2 then begin
(
# 687 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 689 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _145_507 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _145_507)))
end
in (match (_61_799) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_61_801) -> begin
(fail r)
end
| _61_804 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 698 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 699 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 700 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 699 "FStar.TypeChecker.Rel.fst"
let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_61_807) -> begin
_61_807
end))

# 700 "FStar.TypeChecker.Rel.fst"
let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_61_810) -> begin
_61_810
end))

# 701 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 703 "FStar.TypeChecker.Rel.fst"
let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (
# 704 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 705 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_61_817) -> begin
false
end
| _61_820 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 710 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 711 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_61_830, imp), T (t)) -> begin
(t, imp)
end
| _61_837 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 716 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _61_842 -> (match (_61_842) with
| (t, _61_841) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 722 "FStar.TypeChecker.Rel.fst"
let fail = (fun _61_849 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 723 "FStar.TypeChecker.Rel.fst"
let _61_852 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_61_852) with
| (bs, c) -> begin
(
# 725 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 726 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 727 "FStar.TypeChecker.Rel.fst"
let _61_869 = x
in {FStar_Syntax_Syntax.ppname = _61_869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _61_877 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 732 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _61_19 -> (match (_61_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 735 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _145_589 = (decompose [] bs)
in (rebuild, matches, _145_589))))
end)))
end
| _61_887 -> begin
(
# 743 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _61_20 -> (match (_61_20) with
| [] -> begin
t
end
| _61_891 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 749 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _61_21 -> (match (_61_21) with
| T (t) -> begin
t
end
| _61_898 -> begin
(FStar_All.failwith "Impossible")
end))

# 753 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _61_22 -> (match (_61_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _61_903 -> begin
(FStar_All.failwith "Impossible")
end))

# 757 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 762 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 763 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 764 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_61_916, variance, T (ti)) -> begin
(
# 767 "FStar.TypeChecker.Rel.fst"
let k = (
# 768 "FStar.TypeChecker.Rel.fst"
let _61_924 = (FStar_Syntax_Util.type_u ())
in (match (_61_924) with
| (t, _61_923) -> begin
(let _145_611 = (new_uvar r scope t)
in (Prims.fst _145_611))
end))
in (
# 770 "FStar.TypeChecker.Rel.fst"
let _61_928 = (new_uvar r scope k)
in (match (_61_928) with
| (gi_xs, gi) -> begin
(
# 771 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _61_931 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _145_614 = (let _145_613 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _145_612 -> FStar_TypeChecker_Common.TProb (_145_612)) _145_613))
in (T (gi_xs), _145_614)))
end)))
end
| (_61_934, _61_936, C (_61_938)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 779 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 783 "FStar.TypeChecker.Rel.fst"
let _61_1016 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _61_956; FStar_Syntax_Syntax.pos = _61_954; FStar_Syntax_Syntax.vars = _61_952})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _145_623 = (let _145_622 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _145_621 -> C (_145_621)) _145_622))
in (_145_623, (prob)::[]))
end
| _61_967 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _61_975; FStar_Syntax_Syntax.pos = _61_973; FStar_Syntax_Syntax.vars = _61_971})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _145_626 = (let _145_625 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _145_624 -> C (_145_624)) _145_625))
in (_145_626, (prob)::[]))
end
| _61_986 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_61_988, _61_990, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _61_996; FStar_Syntax_Syntax.pos = _61_994; FStar_Syntax_Syntax.vars = _61_992})) -> begin
(
# 797 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 798 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 799 "FStar.TypeChecker.Rel.fst"
let _61_1007 = (let _145_628 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _145_628 FStar_List.unzip))
in (match (_61_1007) with
| (tcs, sub_probs) -> begin
(
# 800 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _145_633 = (let _145_632 = (let _145_629 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _145_629 un_T))
in (let _145_631 = (let _145_630 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _145_630 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_632; FStar_Syntax_Syntax.effect_args = _145_631; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _145_633))
in (C (gi_xs), sub_probs))
end))))
end
| _61_1010 -> begin
(
# 809 "FStar.TypeChecker.Rel.fst"
let _61_1013 = (sub_prob scope args q)
in (match (_61_1013) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_61_1016) with
| (tc, probs) -> begin
(
# 812 "FStar.TypeChecker.Rel.fst"
let _61_1029 = (match (q) with
| (Some (b), _61_1020, _61_1022) -> begin
(let _145_635 = (let _145_634 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_145_634)::args)
in (Some (b), (b)::scope, _145_635))
end
| _61_1025 -> begin
(None, scope, args)
end)
in (match (_61_1029) with
| (bopt, scope, args) -> begin
(
# 816 "FStar.TypeChecker.Rel.fst"
let _61_1033 = (aux scope args qs)
in (match (_61_1033) with
| (sub_probs, tcs, f) -> begin
(
# 817 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _145_638 = (let _145_637 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_145_637)
in (FStar_Syntax_Util.mk_conj_l _145_638))
end
| Some (b) -> begin
(let _145_642 = (let _145_641 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _145_640 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_145_641)::_145_640))
in (FStar_Syntax_Util.mk_conj_l _145_642))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 832 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 833 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 834 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _61_1061), FStar_Syntax_Syntax.Tm_uvar (u2, _61_1066)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _61_1080 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _61_1086 _61_1090 -> (match ((_61_1086, _61_1090)) with
| ((a1, _61_1085), (a2, _61_1089)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 851 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 852 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 854 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 855 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 856 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 857 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 858 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 859 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 860 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 861 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 862 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 862 "FStar.TypeChecker.Rel.fst"
let _61_1093 = p
in (let _145_664 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _145_663 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _61_1093.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_664; FStar_TypeChecker_Common.relation = _61_1093.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_663; FStar_TypeChecker_Common.element = _61_1093.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1093.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1093.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1093.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1093.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_1093.FStar_TypeChecker_Common.rank}))))

# 864 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _145_670 = (compress_tprob wl p)
in (FStar_All.pipe_right _145_670 (fun _145_669 -> FStar_TypeChecker_Common.TProb (_145_669))))
end
| FStar_TypeChecker_Common.CProb (_61_1100) -> begin
p
end))

# 869 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 872 "FStar.TypeChecker.Rel.fst"
let prob = (let _145_675 = (compress_prob wl pr)
in (FStar_All.pipe_right _145_675 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 875 "FStar.TypeChecker.Rel.fst"
let _61_1110 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_61_1110) with
| (lh, _61_1109) -> begin
(
# 876 "FStar.TypeChecker.Rel.fst"
let _61_1114 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_61_1114) with
| (rh, _61_1113) -> begin
(
# 877 "FStar.TypeChecker.Rel.fst"
let _61_1170 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_61_1116), FStar_Syntax_Syntax.Tm_uvar (_61_1119)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_61_1135), _61_1138) -> begin
(
# 884 "FStar.TypeChecker.Rel.fst"
let _61_1142 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_61_1142) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _61_1145 -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _145_677 = (
# 892 "FStar.TypeChecker.Rel.fst"
let _61_1147 = tp
in (let _145_676 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _61_1147.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_1147.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_1147.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_676; FStar_TypeChecker_Common.element = _61_1147.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1147.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1147.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1147.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1147.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_1147.FStar_TypeChecker_Common.rank}))
in (rank, _145_677)))
end)
end))
end
| (_61_1150, FStar_Syntax_Syntax.Tm_uvar (_61_1152)) -> begin
(
# 896 "FStar.TypeChecker.Rel.fst"
let _61_1157 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_61_1157) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _61_1160 -> begin
(let _145_679 = (
# 899 "FStar.TypeChecker.Rel.fst"
let _61_1161 = tp
in (let _145_678 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _61_1161.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_678; FStar_TypeChecker_Common.relation = _61_1161.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_1161.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_1161.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1161.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1161.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1161.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1161.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_1161.FStar_TypeChecker_Common.rank}))
in (refine_flex, _145_679))
end)
end))
end
| (_61_1164, _61_1166) -> begin
(rigid_rigid, tp)
end)
in (match (_61_1170) with
| (rank, tp) -> begin
(let _145_681 = (FStar_All.pipe_right (
# 904 "FStar.TypeChecker.Rel.fst"
let _61_1171 = tp
in {FStar_TypeChecker_Common.pid = _61_1171.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_1171.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_1171.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_1171.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_1171.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1171.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1171.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1171.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1171.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _145_680 -> FStar_TypeChecker_Common.TProb (_145_680)))
in (rank, _145_681))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _145_683 = (FStar_All.pipe_right (
# 906 "FStar.TypeChecker.Rel.fst"
let _61_1175 = cp
in {FStar_TypeChecker_Common.pid = _61_1175.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_1175.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_1175.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_1175.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_1175.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1175.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1175.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1175.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1175.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _145_682 -> FStar_TypeChecker_Common.CProb (_145_682)))
in (rigid_rigid, _145_683))
end)))

# 908 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 912 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _61_1182 probs -> (match (_61_1182) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 915 "FStar.TypeChecker.Rel.fst"
let _61_1190 = (rank wl hd)
in (match (_61_1190) with
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

# 928 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 930 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 931 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 932 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 933 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 931 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_61_1200) -> begin
_61_1200
end))

# 932 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_61_1203) -> begin
_61_1203
end))

# 933 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_61_1206) -> begin
_61_1206
end))

# 935 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 936 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 937 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 938 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 941 "FStar.TypeChecker.Rel.fst"
let _61_1222 = (FStar_Syntax_Util.univ_kernel u)
in (match (_61_1222) with
| (k, _61_1221) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _61_1226 -> begin
false
end)
end)))))
end
| _61_1228 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 947 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_61_1234), FStar_Syntax_Syntax.U_max (_61_1237)) -> begin
(let _145_755 = (let _145_754 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_753 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _145_754 _145_753)))
in UFailed (_145_755))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 954 "FStar.TypeChecker.Rel.fst"
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
| _61_1257 -> begin
(let _145_762 = (let _145_761 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_760 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _145_761 _145_760 msg)))
in UFailed (_145_762))
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
# 975 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 980 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _145_765 = (let _145_764 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _145_763 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _145_764 _145_763)))
in (try_umax_components u1 u2 _145_765))
end else begin
(let _145_766 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_145_766))
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
# 1005 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1006 "FStar.TypeChecker.Rel.fst"
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

# 1018 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1020 "FStar.TypeChecker.Rel.fst"
let _61_1352 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_809 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _145_809))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1024 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1024 "FStar.TypeChecker.Rel.fst"
let _61_1359 = probs
in {attempting = tl; wl_deferred = _61_1359.wl_deferred; ctr = _61_1359.ctr; defer_ok = _61_1359.defer_ok; smt_ok = _61_1359.smt_ok; tcenv = _61_1359.tcenv})
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
(solve_t' env (maybe_invert tp) probs)
end
end))
end
| (None, _61_1371, _61_1373) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _61_1377 -> begin
(
# 1046 "FStar.TypeChecker.Rel.fst"
let _61_1386 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _61_1383 -> (match (_61_1383) with
| (c, _61_1380, _61_1382) -> begin
(c < probs.ctr)
end))))
in (match (_61_1386) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _145_812 = (FStar_List.map (fun _61_1392 -> (match (_61_1392) with
| (_61_1389, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_145_812))
end
| _61_1394 -> begin
(let _145_815 = (
# 1052 "FStar.TypeChecker.Rel.fst"
let _61_1395 = probs
in (let _145_814 = (FStar_All.pipe_right attempt (FStar_List.map (fun _61_1402 -> (match (_61_1402) with
| (_61_1398, _61_1400, y) -> begin
y
end))))
in {attempting = _145_814; wl_deferred = rest; ctr = _61_1395.ctr; defer_ok = _61_1395.defer_ok; smt_ok = _61_1395.smt_ok; tcenv = _61_1395.tcenv}))
in (solve env _145_815))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _145_821 = (solve_prob orig None [] wl)
in (solve env _145_821))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1066 "FStar.TypeChecker.Rel.fst"
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
| _61_1437 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _145_836 = (let _145_833 = (whnf env t1)
in _145_833.FStar_Syntax_Syntax.n)
in (let _145_835 = (let _145_834 = (whnf env t2)
in _145_834.FStar_Syntax_Syntax.n)
in (_145_836, _145_835)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _61_1443; FStar_Syntax_Syntax.pos = _61_1441; FStar_Syntax_Syntax.vars = _61_1439}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _61_1455; FStar_Syntax_Syntax.pos = _61_1453; FStar_Syntax_Syntax.vars = _61_1451}, us2)) -> begin
(
# 1081 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1082 "FStar.TypeChecker.Rel.fst"
let _61_1464 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _61_1479 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1095 "FStar.TypeChecker.Rel.fst"
let _61_1484 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_841 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _145_841 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1105 "FStar.TypeChecker.Rel.fst"
let _61_1489 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_845 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _145_845))
end else begin
()
end
in (
# 1107 "FStar.TypeChecker.Rel.fst"
let _61_1493 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_61_1493) with
| (u, args) -> begin
(
# 1108 "FStar.TypeChecker.Rel.fst"
let _61_1499 = (0, 1, 2, 3, 4)
in (match (_61_1499) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1109 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1111 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1112 "FStar.TypeChecker.Rel.fst"
let _61_1508 = (FStar_Syntax_Util.head_and_args t1)
in (match (_61_1508) with
| (h1, args1) -> begin
(
# 1113 "FStar.TypeChecker.Rel.fst"
let _61_1512 = (FStar_Syntax_Util.head_and_args t2)
in (match (_61_1512) with
| (h2, _61_1511) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _145_857 = (let _145_856 = (let _145_855 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _145_854 -> FStar_TypeChecker_Common.TProb (_145_854)) _145_855))
in (_145_856)::[])
in Some (_145_857))
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
| _61_1524 -> begin
None
end)
end))
end)))
in (
# 1129 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1131 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1135 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1136 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1137 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1138 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _145_864 = (let _145_863 = (let _145_862 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _145_862))
in (_145_863, m))
in Some (_145_864))))))
end))
end
| (_61_1546, FStar_Syntax_Syntax.Tm_refine (y, _61_1549)) -> begin
(
# 1143 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _61_1559), _61_1563) -> begin
(
# 1150 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _61_1570 -> begin
(
# 1157 "FStar.TypeChecker.Rel.fst"
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
# 1163 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _61_1578) -> begin
(
# 1167 "FStar.TypeChecker.Rel.fst"
let _61_1603 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _61_23 -> (match (_61_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1171 "FStar.TypeChecker.Rel.fst"
let _61_1589 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_61_1589) with
| (u', _61_1588) -> begin
(match ((let _145_866 = (whnf env u')
in _145_866.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _61_1592) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _61_1596 -> begin
false
end)
end))
end
| _61_1598 -> begin
false
end)
end
| _61_1600 -> begin
false
end))))
in (match (_61_1603) with
| (upper_bounds, rest) -> begin
(
# 1180 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _61_1607 tps -> (match (_61_1607) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _145_871 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _145_871))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _61_1620 -> begin
None
end)
end))
in (match ((let _145_873 = (let _145_872 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_145_872, []))
in (make_upper_bound _145_873 upper_bounds))) with
| None -> begin
(
# 1191 "FStar.TypeChecker.Rel.fst"
let _61_1622 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1204 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1205 "FStar.TypeChecker.Rel.fst"
let _61_1632 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1206 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1206 "FStar.TypeChecker.Rel.fst"
let _61_1629 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _61_1629.wl_deferred; ctr = _61_1629.ctr; defer_ok = _61_1629.defer_ok; smt_ok = _61_1629.smt_ok; tcenv = _61_1629.tcenv})
in (let _145_874 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _145_874)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1208 "FStar.TypeChecker.Rel.fst"
let _61_1634 = wl
in {attempting = sub_probs; wl_deferred = _61_1634.wl_deferred; ctr = _61_1634.ctr; defer_ok = _61_1634.defer_ok; smt_ok = _61_1634.smt_ok; tcenv = _61_1634.tcenv}))) with
| Success (_61_1637) -> begin
(
# 1210 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1210 "FStar.TypeChecker.Rel.fst"
let _61_1639 = wl
in {attempting = rest; wl_deferred = _61_1639.wl_deferred; ctr = _61_1639.ctr; defer_ok = _61_1639.defer_ok; smt_ok = _61_1639.smt_ok; tcenv = _61_1639.tcenv})
in (
# 1211 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1212 "FStar.TypeChecker.Rel.fst"
let _61_1645 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _61_1648 -> begin
None
end)))
end))
end))
end
| _61_1650 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1222 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1225 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1226 "FStar.TypeChecker.Rel.fst"
let _61_1667 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_902 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _145_902))
end else begin
()
end
in (
# 1228 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1232 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1232 "FStar.TypeChecker.Rel.fst"
let _61_1681 = hd1
in (let _145_903 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _61_1681.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_1681.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_903}))
in (
# 1233 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1233 "FStar.TypeChecker.Rel.fst"
let _61_1684 = hd2
in (let _145_904 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _61_1684.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_1684.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_904}))
in (
# 1234 "FStar.TypeChecker.Rel.fst"
let prob = (let _145_907 = (let _145_906 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _145_906 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _145_905 -> FStar_TypeChecker_Common.TProb (_145_905)) _145_907))
in (
# 1235 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1236 "FStar.TypeChecker.Rel.fst"
let subst = (let _145_908 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_145_908)
in (
# 1237 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1240 "FStar.TypeChecker.Rel.fst"
let phi = (let _145_910 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _145_909 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _145_910 _145_909)))
in (
# 1241 "FStar.TypeChecker.Rel.fst"
let _61_1696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_912 = (FStar_Syntax_Print.term_to_string phi)
in (let _145_911 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _145_912 _145_911)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _61_1700 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1250 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1254 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _145_916 = (compress_tprob wl problem)
in (solve_t' env _145_916 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1261 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1264 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1265 "FStar.TypeChecker.Rel.fst"
let _61_1728 = (head_matches_delta env wl t1 t2)
in (match (_61_1728) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_61_1730), _61_1733) -> begin
(
# 1268 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _61_1746 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1274 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1277 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1281 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _145_945 = (let _145_944 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _145_944 t2))
in (FStar_Syntax_Util.mk_forall x _145_945)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _145_946 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _145_946)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_61_1756, Some (t1, t2)) -> begin
(solve_t env (
# 1290 "FStar.TypeChecker.Rel.fst"
let _61_1762 = problem
in {FStar_TypeChecker_Common.pid = _61_1762.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _61_1762.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _61_1762.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1762.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1762.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1762.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1762.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_1762.FStar_TypeChecker_Common.rank}) wl)
end
| (_61_1765, None) -> begin
(
# 1293 "FStar.TypeChecker.Rel.fst"
let _61_1768 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_950 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_949 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_948 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_947 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _145_950 _145_949 _145_948 _145_947)))))
end else begin
()
end
in (
# 1297 "FStar.TypeChecker.Rel.fst"
let _61_1772 = (FStar_Syntax_Util.head_and_args t1)
in (match (_61_1772) with
| (head, args) -> begin
(
# 1298 "FStar.TypeChecker.Rel.fst"
let _61_1775 = (FStar_Syntax_Util.head_and_args t2)
in (match (_61_1775) with
| (head', args') -> begin
(
# 1299 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _145_955 = (let _145_954 = (FStar_Syntax_Print.term_to_string head)
in (let _145_953 = (args_to_string args)
in (let _145_952 = (FStar_Syntax_Print.term_to_string head')
in (let _145_951 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _145_954 _145_953 _145_952 _145_951)))))
in (giveup env _145_955 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _145_956 = (solve_prob orig None [] wl)
in (solve env _145_956))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1320 "FStar.TypeChecker.Rel.fst"
let _61_1785 = (base_and_refinement env wl t1)
in (match (_61_1785) with
| (base1, refinement1) -> begin
(
# 1321 "FStar.TypeChecker.Rel.fst"
let _61_1788 = (base_and_refinement env wl t2)
in (match (_61_1788) with
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
# 1328 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _61_1801 _61_1805 -> (match ((_61_1801, _61_1805)) with
| ((a, _61_1800), (a', _61_1804)) -> begin
(let _145_960 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _145_959 -> FStar_TypeChecker_Common.TProb (_145_959)) _145_960))
end)) args args')
in (
# 1329 "FStar.TypeChecker.Rel.fst"
let formula = (let _145_962 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _145_962))
in (
# 1330 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _61_1811 -> begin
(
# 1335 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1336 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1337 "FStar.TypeChecker.Rel.fst"
let _61_1814 = problem
in {FStar_TypeChecker_Common.pid = _61_1814.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _61_1814.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _61_1814.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_1814.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_1814.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_1814.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_1814.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_1814.FStar_TypeChecker_Common.rank}) wl)))
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
# 1343 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1344 "FStar.TypeChecker.Rel.fst"
let _61_1831 = p
in (match (_61_1831) with
| ((u, k), ps, xs, (h, _61_1828, qs)) -> begin
(
# 1345 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1350 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1351 "FStar.TypeChecker.Rel.fst"
let _61_1837 = (imitation_sub_probs orig env xs ps qs)
in (match (_61_1837) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1352 "FStar.TypeChecker.Rel.fst"
let im = (let _145_973 = (h gs_xs)
in (u_abs xs _145_973))
in (
# 1353 "FStar.TypeChecker.Rel.fst"
let _61_1839 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_978 = (FStar_Syntax_Print.term_to_string im)
in (let _145_977 = (FStar_Syntax_Print.tag_of_term im)
in (let _145_976 = (let _145_974 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _145_974 (FStar_String.concat ", ")))
in (let _145_975 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _145_978 _145_977 _145_976 _145_975)))))
end else begin
()
end
in (
# 1358 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1363 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1364 "FStar.TypeChecker.Rel.fst"
let _61_1855 = p
in (match (_61_1855) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1368 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1369 "FStar.TypeChecker.Rel.fst"
let _61_1860 = (FStar_List.nth ps i)
in (match (_61_1860) with
| (pi, _61_1859) -> begin
(
# 1370 "FStar.TypeChecker.Rel.fst"
let _61_1864 = (FStar_List.nth xs i)
in (match (_61_1864) with
| (xi, _61_1863) -> begin
(
# 1372 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1373 "FStar.TypeChecker.Rel.fst"
let _61_1869 = (FStar_Syntax_Util.arrow_formals k)
in (match (_61_1869) with
| (bs, k) -> begin
(
# 1374 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _61_1877)::tl -> begin
(
# 1377 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1378 "FStar.TypeChecker.Rel.fst"
let _61_1883 = (new_uvar r xs k_a)
in (match (_61_1883) with
| (gi_xs, gi) -> begin
(
# 1379 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1380 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1381 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1382 "FStar.TypeChecker.Rel.fst"
let _61_1889 = (aux subst tl)
in (match (_61_1889) with
| (gi_xs', gi_ps') -> begin
(let _145_1000 = (let _145_997 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_145_997)::gi_xs')
in (let _145_999 = (let _145_998 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_145_998)::gi_ps')
in (_145_1000, _145_999)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _145_1001 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _145_1001)) then begin
None
end else begin
(
# 1388 "FStar.TypeChecker.Rel.fst"
let _61_1893 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_61_1893) with
| (g_xs, _61_1892) -> begin
(
# 1389 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1390 "FStar.TypeChecker.Rel.fst"
let proj = (let _145_1002 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _145_1002))
in (
# 1391 "FStar.TypeChecker.Rel.fst"
let sub = (let _145_1008 = (let _145_1007 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _145_1006 = (let _145_1005 = (FStar_List.map (fun _61_1901 -> (match (_61_1901) with
| (_61_1897, _61_1899, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _145_1005))
in (mk_problem (p_scope orig) orig _145_1007 (p_rel orig) _145_1006 None "projection")))
in (FStar_All.pipe_left (fun _145_1003 -> FStar_TypeChecker_Common.TProb (_145_1003)) _145_1008))
in (
# 1392 "FStar.TypeChecker.Rel.fst"
let _61_1903 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1010 = (FStar_Syntax_Print.term_to_string proj)
in (let _145_1009 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _145_1010 _145_1009)))
end else begin
()
end
in (
# 1393 "FStar.TypeChecker.Rel.fst"
let wl = (let _145_1012 = (let _145_1011 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_145_1011))
in (solve_prob orig _145_1012 ((TERM ((u, proj)))::[]) wl))
in (let _145_1014 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _145_1013 -> Some (_145_1013)) _145_1014)))))))
end))
end)
end))
end)))
end)))
in (
# 1398 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1399 "FStar.TypeChecker.Rel.fst"
let _61_1917 = lhs
in (match (_61_1917) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1400 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1401 "FStar.TypeChecker.Rel.fst"
let xs = (let _145_1041 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _145_1041 Prims.fst))
in (let _145_1046 = (decompose env t2)
in ((uv, k), ps, xs, _145_1046))))
in (
# 1404 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1407 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_61_1927) -> begin
(
# 1411 "FStar.TypeChecker.Rel.fst"
let _61_1929 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1418 "FStar.TypeChecker.Rel.fst"
let _61_1937 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1422 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1423 "FStar.TypeChecker.Rel.fst"
let _61_1947 = (FStar_Syntax_Util.head_and_args t2)
in (match (_61_1947) with
| (hd, _61_1946) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _61_1958 -> begin
(
# 1429 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1432 "FStar.TypeChecker.Rel.fst"
let _61_1960 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1057 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _145_1057))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1435 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1436 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _145_1061 = (let _145_1060 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1060 Prims.fst))
in (FStar_All.pipe_right _145_1061 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1443 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1444 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1445 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1446 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1447 "FStar.TypeChecker.Rel.fst"
let _61_1973 = (occurs_check env wl (uv, k) t2)
in (match (_61_1973) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _145_1063 = (let _145_1062 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _145_1062))
in (giveup_or_defer orig _145_1063))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _145_1064 = (subterms args_lhs)
in (imitate orig env wl _145_1064))
end else begin
(
# 1454 "FStar.TypeChecker.Rel.fst"
let _61_1974 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1067 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1066 = (names_to_string fvs1)
in (let _145_1065 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _145_1067 _145_1066 _145_1065))))
end else begin
()
end
in (
# 1459 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _61_1978 -> begin
(let _145_1068 = (sn_binders env vars)
in (u_abs _145_1068 t2))
end)
in (
# 1462 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1467 "FStar.TypeChecker.Rel.fst"
let _61_1981 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1071 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1070 = (names_to_string fvs1)
in (let _145_1069 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _145_1071 _145_1070 _145_1069))))
end else begin
()
end
in (let _145_1072 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1072 (- (1)))))
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
if (let _145_1073 = (FStar_Syntax_Free.names t1)
in (check_head _145_1073 t2)) then begin
(
# 1479 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1480 "FStar.TypeChecker.Rel.fst"
let _61_1985 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1074 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _145_1074 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _145_1075 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _145_1075 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1505 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1508 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _61_1997 -> (match (_61_1997) with
| (t, u, k, args) -> begin
(
# 1511 "FStar.TypeChecker.Rel.fst"
let _61_2001 = (FStar_Syntax_Util.arrow_formals k)
in (match (_61_2001) with
| (all_formals, _61_2000) -> begin
(
# 1512 "FStar.TypeChecker.Rel.fst"
let _61_2002 = ()
in (
# 1514 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1522 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _61_2015 -> (match (_61_2015) with
| (x, imp) -> begin
(let _145_1097 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_1097, imp))
end))))
in (
# 1523 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1524 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1525 "FStar.TypeChecker.Rel.fst"
let _61_2021 = (FStar_Syntax_Util.type_u ())
in (match (_61_2021) with
| (t, _61_2020) -> begin
(let _145_1098 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _145_1098))
end))
in (
# 1527 "FStar.TypeChecker.Rel.fst"
let _61_2025 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_61_2025) with
| (t', tm_u1) -> begin
(
# 1528 "FStar.TypeChecker.Rel.fst"
let _61_2032 = (destruct_flex_t t')
in (match (_61_2032) with
| (_61_2027, u1, k1, _61_2031) -> begin
(
# 1529 "FStar.TypeChecker.Rel.fst"
let sol = (let _145_1100 = (let _145_1099 = (u_abs all_formals t')
in ((u, k), _145_1099))
in TERM (_145_1100))
in (
# 1530 "FStar.TypeChecker.Rel.fst"
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
# 1539 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _61_2051 -> (match (_61_2051) with
| (x, _61_2050) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1546 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _145_1102 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _145_1102 formals tl))
end)
end)
end)
end
| _61_2055 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _145_1103 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _145_1103 all_formals args))))
end))
end))
in (
# 1558 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _61_2061 _61_2065 r -> (match ((_61_2061, _61_2065)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _145_1112 = (solve_prob orig None [] wl)
in (solve env _145_1112))
end else begin
(
# 1566 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1567 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1568 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1569 "FStar.TypeChecker.Rel.fst"
let _61_2070 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1115 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _145_1114 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _145_1113 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _145_1115 _145_1114 _145_1113))))
end else begin
()
end
in (
# 1572 "FStar.TypeChecker.Rel.fst"
let _61_2083 = (
# 1573 "FStar.TypeChecker.Rel.fst"
let _61_2075 = (FStar_Syntax_Util.type_u ())
in (match (_61_2075) with
| (t, _61_2074) -> begin
(
# 1574 "FStar.TypeChecker.Rel.fst"
let _61_2079 = (new_uvar r zs t)
in (match (_61_2079) with
| (k, _61_2078) -> begin
(new_uvar r zs k)
end))
end))
in (match (_61_2083) with
| (u_zs, _61_2082) -> begin
(
# 1576 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs xs u_zs)
in (
# 1577 "FStar.TypeChecker.Rel.fst"
let _61_2087 = (occurs_check env wl (u1, k1) sub1)
in (match (_61_2087) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1580 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1582 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1584 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs ys u_zs)
in (
# 1585 "FStar.TypeChecker.Rel.fst"
let _61_2093 = (occurs_check env wl (u2, k2) sub2)
in (match (_61_2093) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1588 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1589 "FStar.TypeChecker.Rel.fst"
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
# 1592 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _61_2101 _61_2106 -> (match ((_61_2101, _61_2106)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1594 "FStar.TypeChecker.Rel.fst"
let _61_2107 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1121 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1120 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _145_1121 _145_1120)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1597 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _61_2112 _61_2116 -> (match ((_61_2112, _61_2116)) with
| ((a, _61_2111), (t2, _61_2115)) -> begin
(let _145_1126 = (let _145_1124 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _145_1124 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _145_1126 (fun _145_1125 -> FStar_TypeChecker_Common.TProb (_145_1125))))
end)) xs args2)
in (
# 1600 "FStar.TypeChecker.Rel.fst"
let guard = (let _145_1128 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1128))
in (
# 1601 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1604 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1605 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1606 "FStar.TypeChecker.Rel.fst"
let _61_2126 = (occurs_check env wl (u1, k1) t2)
in (match (_61_2126) with
| (occurs_ok, _61_2125) -> begin
(
# 1607 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1610 "FStar.TypeChecker.Rel.fst"
let sol = (let _145_1130 = (let _145_1129 = (u_abs xs t2)
in ((u1, k1), _145_1129))
in TERM (_145_1130))
in (
# 1611 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1614 "FStar.TypeChecker.Rel.fst"
let _61_2137 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_61_2137) with
| (sol, (_61_2132, u2, k2, ys)) -> begin
(
# 1615 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1616 "FStar.TypeChecker.Rel.fst"
let _61_2139 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1131 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _145_1131))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _61_2144 -> begin
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
# 1624 "FStar.TypeChecker.Rel.fst"
let _61_2149 = lhs
in (match (_61_2149) with
| (t1, u1, k1, args1) -> begin
(
# 1625 "FStar.TypeChecker.Rel.fst"
let _61_2154 = rhs
in (match (_61_2154) with
| (t2, u2, k2, args2) -> begin
(
# 1626 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1627 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1628 "FStar.TypeChecker.Rel.fst"
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
| _61_2172 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1637 "FStar.TypeChecker.Rel.fst"
let _61_2176 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_61_2176) with
| (sol, _61_2175) -> begin
(
# 1638 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1639 "FStar.TypeChecker.Rel.fst"
let _61_2178 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _145_1132 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _145_1132))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _61_2183 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1646 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _145_1133 = (solve_prob orig None [] wl)
in (solve env _145_1133))
end else begin
(
# 1648 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1649 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _145_1134 = (solve_prob orig None [] wl)
in (solve env _145_1134))
end else begin
(
# 1651 "FStar.TypeChecker.Rel.fst"
let _61_2187 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1135 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _145_1135))
end else begin
()
end
in (
# 1654 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1656 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _61_2192 _61_2195 -> (match ((_61_2192, _61_2195)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1658 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1659 "FStar.TypeChecker.Rel.fst"
let _61_2202 = (FStar_Util.first_N n bs)
in (match (_61_2202) with
| (bs, rest) -> begin
(let _145_1165 = (mk_cod rest)
in (bs, _145_1165))
end)))
in (
# 1662 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1663 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _145_1169 = (let _145_1166 = (mk_cod1 [])
in (bs1, _145_1166))
in (let _145_1168 = (let _145_1167 = (mk_cod2 [])
in (bs2, _145_1167))
in (_145_1169, _145_1168)))
end else begin
if (l1 > l2) then begin
(let _145_1172 = (curry l2 bs1 mk_cod1)
in (let _145_1171 = (let _145_1170 = (mk_cod2 [])
in (bs2, _145_1170))
in (_145_1172, _145_1171)))
end else begin
(let _145_1175 = (let _145_1173 = (mk_cod1 [])
in (bs1, _145_1173))
in (let _145_1174 = (curry l1 bs2 mk_cod2)
in (_145_1175, _145_1174)))
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
# 1681 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _61_24 -> (match (_61_24) with
| [] -> begin
c
end
| bs -> begin
(let _145_1180 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _145_1180))
end))
in (
# 1685 "FStar.TypeChecker.Rel.fst"
let _61_2245 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_61_2245) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1690 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1691 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1692 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _145_1187 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _145_1186 -> FStar_TypeChecker_Common.CProb (_145_1186)) _145_1187)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _61_2255), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _61_2261)) -> begin
(
# 1696 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _61_25 -> (match (_61_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1699 "FStar.TypeChecker.Rel.fst"
let _61_2276 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_61_2276) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _145_1200 = (let _145_1199 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _145_1198 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _145_1199 problem.FStar_TypeChecker_Common.relation _145_1198 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _145_1197 -> FStar_TypeChecker_Common.TProb (_145_1197)) _145_1200))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_61_2281), FStar_Syntax_Syntax.Tm_refine (_61_2284)) -> begin
(
# 1708 "FStar.TypeChecker.Rel.fst"
let _61_2289 = (as_refinement env wl t1)
in (match (_61_2289) with
| (x1, phi1) -> begin
(
# 1709 "FStar.TypeChecker.Rel.fst"
let _61_2292 = (as_refinement env wl t2)
in (match (_61_2292) with
| (x2, phi2) -> begin
(
# 1710 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _145_1202 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _145_1201 -> FStar_TypeChecker_Common.TProb (_145_1201)) _145_1202))
in (
# 1711 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1712 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1713 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1714 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1715 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1716 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _145_1219 = (imp phi1 phi2)
in (FStar_All.pipe_right _145_1219 (guard_on_element problem x1))))
in (
# 1717 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _61_2304 -> (match (()) with
| () -> begin
(
# 1718 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1722 "FStar.TypeChecker.Rel.fst"
let guard = (let _145_1222 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1222 impl))
in (
# 1723 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1726 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _145_1226 = (let _145_1225 = (let _145_1224 = (FStar_Syntax_Syntax.mk_binder x1)
in (_145_1224)::(p_scope orig))
in (mk_problem _145_1225 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _145_1223 -> FStar_TypeChecker_Common.TProb (_145_1223)) _145_1226))
in (match ((solve env (
# 1727 "FStar.TypeChecker.Rel.fst"
let _61_2309 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _61_2309.ctr; defer_ok = false; smt_ok = _61_2309.smt_ok; tcenv = _61_2309.tcenv}))) with
| Failed (_61_2312) -> begin
(fallback ())
end
| Success (_61_2315) -> begin
(
# 1730 "FStar.TypeChecker.Rel.fst"
let guard = (let _145_1229 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _145_1228 = (let _145_1227 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _145_1227 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _145_1229 _145_1228)))
in (
# 1731 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1732 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1732 "FStar.TypeChecker.Rel.fst"
let _61_2319 = wl
in {attempting = _61_2319.attempting; wl_deferred = _61_2319.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _61_2319.defer_ok; smt_ok = _61_2319.smt_ok; tcenv = _61_2319.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _145_1231 = (destruct_flex_t t1)
in (let _145_1230 = (destruct_flex_t t2)
in (flex_flex orig _145_1231 _145_1230)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _145_1232 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _145_1232 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1760 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _145_1233 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _145_1233)) then begin
(let _145_1236 = (FStar_All.pipe_left (fun _145_1234 -> FStar_TypeChecker_Common.TProb (_145_1234)) (
# 1762 "FStar.TypeChecker.Rel.fst"
let _61_2464 = problem
in {FStar_TypeChecker_Common.pid = _61_2464.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_2464.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _61_2464.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2464.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2464.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2464.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2464.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2464.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2464.FStar_TypeChecker_Common.rank}))
in (let _145_1235 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1236 _145_1235 t2 wl)))
end else begin
(
# 1763 "FStar.TypeChecker.Rel.fst"
let _61_2468 = (base_and_refinement env wl t2)
in (match (_61_2468) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _145_1239 = (FStar_All.pipe_left (fun _145_1237 -> FStar_TypeChecker_Common.TProb (_145_1237)) (
# 1766 "FStar.TypeChecker.Rel.fst"
let _61_2470 = problem
in {FStar_TypeChecker_Common.pid = _61_2470.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_2470.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _61_2470.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2470.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2470.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2470.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2470.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2470.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2470.FStar_TypeChecker_Common.rank}))
in (let _145_1238 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _145_1239 _145_1238 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1769 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1769 "FStar.TypeChecker.Rel.fst"
let _61_2476 = y
in {FStar_Syntax_Syntax.ppname = _61_2476.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _61_2476.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1770 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1771 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _145_1241 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _145_1240 -> FStar_TypeChecker_Common.TProb (_145_1240)) _145_1241))
in (
# 1773 "FStar.TypeChecker.Rel.fst"
let guard = (let _145_1242 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1242 impl))
in (
# 1774 "FStar.TypeChecker.Rel.fst"
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
# 1783 "FStar.TypeChecker.Rel.fst"
let _61_2509 = (base_and_refinement env wl t1)
in (match (_61_2509) with
| (t_base, _61_2508) -> begin
(solve_t env (
# 1784 "FStar.TypeChecker.Rel.fst"
let _61_2510 = problem
in {FStar_TypeChecker_Common.pid = _61_2510.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _61_2510.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2510.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2510.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2510.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2510.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2510.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2510.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_61_2513), _61_2516) -> begin
(
# 1787 "FStar.TypeChecker.Rel.fst"
let t2 = (let _145_1243 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _145_1243))
in (solve_t env (
# 1788 "FStar.TypeChecker.Rel.fst"
let _61_2519 = problem
in {FStar_TypeChecker_Common.pid = _61_2519.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_2519.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_2519.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _61_2519.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2519.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2519.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2519.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2519.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2519.FStar_TypeChecker_Common.rank}) wl))
end
| (_61_2522, FStar_Syntax_Syntax.Tm_refine (_61_2524)) -> begin
(
# 1791 "FStar.TypeChecker.Rel.fst"
let t1 = (let _145_1244 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _145_1244))
in (solve_t env (
# 1792 "FStar.TypeChecker.Rel.fst"
let _61_2528 = problem
in {FStar_TypeChecker_Common.pid = _61_2528.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _61_2528.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_2528.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2528.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2528.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2528.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2528.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2528.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2528.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1796 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_61_2545) -> begin
t
end
| _61_2548 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _145_1249 = (
# 1799 "FStar.TypeChecker.Rel.fst"
let _61_2549 = problem
in (let _145_1248 = (maybe_eta t1)
in (let _145_1247 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _61_2549.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1248; FStar_TypeChecker_Common.relation = _61_2549.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1247; FStar_TypeChecker_Common.element = _61_2549.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2549.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2549.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2549.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2549.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2549.FStar_TypeChecker_Common.rank})))
in (solve_t env _145_1249 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1813 "FStar.TypeChecker.Rel.fst"
let head1 = (let _145_1250 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _145_1250 Prims.fst))
in (
# 1814 "FStar.TypeChecker.Rel.fst"
let head2 = (let _145_1251 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _145_1251 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1819 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1820 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1822 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _145_1253 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _145_1252 -> Some (_145_1252)) _145_1253))
end
in (let _145_1254 = (solve_prob orig guard [] wl)
in (solve env _145_1254)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _61_2630, _61_2632), _61_2636) -> begin
(solve_t' env (
# 1830 "FStar.TypeChecker.Rel.fst"
let _61_2638 = problem
in {FStar_TypeChecker_Common.pid = _61_2638.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _61_2638.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_2638.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2638.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2638.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2638.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2638.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2638.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2638.FStar_TypeChecker_Common.rank}) wl)
end
| (_61_2641, FStar_Syntax_Syntax.Tm_ascribed (t2, _61_2644, _61_2646)) -> begin
(solve_t' env (
# 1833 "FStar.TypeChecker.Rel.fst"
let _61_2650 = problem
in {FStar_TypeChecker_Common.pid = _61_2650.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_2650.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_2650.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _61_2650.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2650.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2650.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2650.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2650.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2650.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _145_1257 = (let _145_1256 = (FStar_Syntax_Print.tag_of_term t1)
in (let _145_1255 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _145_1256 _145_1255)))
in (FStar_All.failwith _145_1257))
end
| _61_2689 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1845 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1846 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1847 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1848 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1850 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1851 "FStar.TypeChecker.Rel.fst"
let _61_2706 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1853 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _61_2711 _61_2715 -> (match ((_61_2711, _61_2715)) with
| ((a1, _61_2710), (a2, _61_2714)) -> begin
(let _145_1272 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _145_1271 -> FStar_TypeChecker_Common.TProb (_145_1271)) _145_1272))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1856 "FStar.TypeChecker.Rel.fst"
let guard = (let _145_1274 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _145_1274))
in (
# 1857 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _145_1275 = (solve_prob orig None [] wl)
in (solve env _145_1275))
end else begin
(
# 1861 "FStar.TypeChecker.Rel.fst"
let _61_2720 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1277 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1276 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _145_1277 (rel_to_string problem.FStar_TypeChecker_Common.relation) _145_1276)))
end else begin
()
end
in (
# 1866 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1867 "FStar.TypeChecker.Rel.fst"
let _61_2725 = (c1, c2)
in (match (_61_2725) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_61_2727), FStar_Syntax_Syntax.Total (_61_2730)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _145_1278 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _145_1278 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _145_1280 = (
# 1879 "FStar.TypeChecker.Rel.fst"
let _61_2758 = problem
in (let _145_1279 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _61_2758.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _145_1279; FStar_TypeChecker_Common.relation = _61_2758.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _61_2758.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _61_2758.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2758.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2758.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2758.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2758.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2758.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1280 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _145_1282 = (
# 1883 "FStar.TypeChecker.Rel.fst"
let _61_2774 = problem
in (let _145_1281 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _61_2774.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _61_2774.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _61_2774.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _145_1281; FStar_TypeChecker_Common.element = _61_2774.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _61_2774.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _61_2774.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _61_2774.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _61_2774.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _61_2774.FStar_TypeChecker_Common.rank}))
in (solve_c env _145_1282 wl))
end
| (FStar_Syntax_Syntax.Comp (_61_2777), FStar_Syntax_Syntax.Comp (_61_2780)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _145_1283 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _145_1283 wl))
end else begin
(
# 1889 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1890 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 1894 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 1895 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 1896 "FStar.TypeChecker.Rel.fst"
let _61_2787 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _145_1286 = (let _145_1285 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1284 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _145_1285 _145_1284)))
in (giveup env _145_1286 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1903 "FStar.TypeChecker.Rel.fst"
let _61_2805 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _61_2798)::(wlp1, _61_2794)::[] -> begin
(wp1, wlp1)
end
| _61_2802 -> begin
(let _145_1288 = (let _145_1287 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _145_1287))
in (FStar_All.failwith _145_1288))
end)
in (match (_61_2805) with
| (wp, wlp) -> begin
(
# 1906 "FStar.TypeChecker.Rel.fst"
let c1 = (let _145_1294 = (let _145_1293 = (let _145_1289 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _145_1289))
in (let _145_1292 = (let _145_1291 = (let _145_1290 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _145_1290))
in (_145_1291)::[])
in (_145_1293)::_145_1292))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _145_1294; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 1913 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _61_26 -> (match (_61_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _61_2812 -> begin
false
end))))
in (
# 1914 "FStar.TypeChecker.Rel.fst"
let _61_2833 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _61_2818)::_61_2815, (wp2, _61_2825)::_61_2822) -> begin
(wp1, wp2)
end
| _61_2830 -> begin
(let _145_1298 = (let _145_1297 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _145_1296 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _145_1297 _145_1296)))
in (FStar_All.failwith _145_1298))
end)
in (match (_61_2833) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _145_1299 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _145_1299 wl))
end else begin
(
# 1921 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 1922 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 1924 "FStar.TypeChecker.Rel.fst"
let _61_2835 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _145_1309 = (let _145_1308 = (let _145_1307 = (let _145_1301 = (let _145_1300 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_145_1300)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1301 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _145_1306 = (let _145_1305 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _145_1304 = (let _145_1303 = (let _145_1302 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1302))
in (_145_1303)::[])
in (_145_1305)::_145_1304))
in (_145_1307, _145_1306)))
in FStar_Syntax_Syntax.Tm_app (_145_1308))
in (FStar_Syntax_Syntax.mk _145_1309 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 1928 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _145_1325 = (let _145_1324 = (let _145_1323 = (let _145_1311 = (let _145_1310 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_145_1310)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1311 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _145_1322 = (let _145_1321 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _145_1320 = (let _145_1319 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _145_1318 = (let _145_1317 = (let _145_1313 = (let _145_1312 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _145_1312 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1313))
in (let _145_1316 = (let _145_1315 = (let _145_1314 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_1314))
in (_145_1315)::[])
in (_145_1317)::_145_1316))
in (_145_1319)::_145_1318))
in (_145_1321)::_145_1320))
in (_145_1323, _145_1322)))
in FStar_Syntax_Syntax.Tm_app (_145_1324))
in (FStar_Syntax_Syntax.mk _145_1325 None r))
in (let _145_1334 = (let _145_1333 = (let _145_1332 = (let _145_1327 = (let _145_1326 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_145_1326)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _145_1327 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _145_1331 = (let _145_1330 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _145_1329 = (let _145_1328 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_145_1328)::[])
in (_145_1330)::_145_1329))
in (_145_1332, _145_1331)))
in FStar_Syntax_Syntax.Tm_app (_145_1333))
in (FStar_Syntax_Syntax.mk _145_1334 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 1935 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _145_1336 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _145_1335 -> FStar_TypeChecker_Common.TProb (_145_1335)) _145_1336))
in (
# 1936 "FStar.TypeChecker.Rel.fst"
let wl = (let _145_1340 = (let _145_1339 = (let _145_1338 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _145_1338 g))
in (FStar_All.pipe_left (fun _145_1337 -> Some (_145_1337)) _145_1339))
in (solve_prob orig _145_1340 [] wl))
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

# 1943 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _145_1344 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _61_2851 -> (match (_61_2851) with
| (_61_2843, u, _61_2846, _61_2848, _61_2850) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _145_1344 (FStar_String.concat ", "))))

# 1945 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _61_2858 -> begin
(
# 1949 "FStar.TypeChecker.Rel.fst"
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
# 1956 "FStar.TypeChecker.Rel.fst"
let carry = (let _145_1350 = (FStar_List.map (fun _61_2866 -> (match (_61_2866) with
| (_61_2864, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _145_1350 (FStar_String.concat ",\n")))
in (
# 1957 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1963 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1965 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1967 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _61_2875; FStar_TypeChecker_Env.implicits = _61_2873} -> begin
true
end
| _61_2880 -> begin
false
end))

# 1971 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 1973 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 1977 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _61_2898 -> begin
(FStar_All.failwith "impossible")
end)
in (let _145_1366 = (
# 1980 "FStar.TypeChecker.Rel.fst"
let _61_2900 = g
in (let _145_1365 = (let _145_1364 = (let _145_1363 = (let _145_1362 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_1362)::[])
in (u_abs _145_1363 f))
in (FStar_All.pipe_left (fun _145_1361 -> FStar_TypeChecker_Common.NonTrivial (_145_1361)) _145_1364))
in {FStar_TypeChecker_Env.guard_f = _145_1365; FStar_TypeChecker_Env.deferred = _61_2900.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_2900.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_2900.FStar_TypeChecker_Env.implicits}))
in Some (_145_1366)))
end))

# 1982 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1984 "FStar.TypeChecker.Rel.fst"
let _61_2907 = g
in (let _145_1377 = (let _145_1376 = (let _145_1375 = (let _145_1374 = (let _145_1373 = (let _145_1372 = (FStar_Syntax_Syntax.as_arg e)
in (_145_1372)::[])
in (f, _145_1373))
in FStar_Syntax_Syntax.Tm_app (_145_1374))
in (FStar_Syntax_Syntax.mk _145_1375 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _145_1371 -> FStar_TypeChecker_Common.NonTrivial (_145_1371)) _145_1376))
in {FStar_TypeChecker_Env.guard_f = _145_1377; FStar_TypeChecker_Env.deferred = _61_2907.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_2907.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_2907.FStar_TypeChecker_Env.implicits}))
end))

# 1986 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_61_2912) -> begin
(FStar_All.failwith "impossible")
end))

# 1990 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _145_1384 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_145_1384))
end))

# 1995 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _61_2930 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 1999 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2003 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2005 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _145_1407 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _145_1407; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2009 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2010 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2012 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2014 "FStar.TypeChecker.Rel.fst"
let _61_2957 = g
in (let _145_1422 = (let _145_1421 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _145_1421 (fun _145_1420 -> FStar_TypeChecker_Common.NonTrivial (_145_1420))))
in {FStar_TypeChecker_Env.guard_f = _145_1422; FStar_TypeChecker_Env.deferred = _61_2957.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_2957.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_2957.FStar_TypeChecker_Env.implicits}))
end))

# 2019 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2020 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_1430 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _145_1429 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _145_1430 (rel_to_string rel) _145_1429)))
end else begin
"TOP"
end
in (
# 2025 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2028 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2029 "FStar.TypeChecker.Rel.fst"
let x = (let _145_1441 = (let _145_1440 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _145_1439 -> Some (_145_1439)) _145_1440))
in (FStar_Syntax_Syntax.new_bv _145_1441 t1))
in (
# 2030 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2031 "FStar.TypeChecker.Rel.fst"
let p = (let _145_1445 = (let _145_1443 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _145_1442 -> Some (_145_1442)) _145_1443))
in (let _145_1444 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _145_1445 _145_1444)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2034 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2035 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2035 "FStar.TypeChecker.Rel.fst"
let _61_2977 = probs
in {attempting = _61_2977.attempting; wl_deferred = _61_2977.wl_deferred; ctr = _61_2977.ctr; defer_ok = false; smt_ok = _61_2977.smt_ok; tcenv = _61_2977.tcenv})
end else begin
probs
end
in (
# 2036 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2037 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2040 "FStar.TypeChecker.Rel.fst"
let _61_2984 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2043 "FStar.TypeChecker.Rel.fst"
let _61_2990 = (FStar_Unionfind.rollback tx)
in (
# 2044 "FStar.TypeChecker.Rel.fst"
let _61_2992 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _145_1457 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _145_1457))
end else begin
()
end
in (err (d, s))))
end)))))

# 2048 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2051 "FStar.TypeChecker.Rel.fst"
let _61_2999 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1462 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _145_1462))
end else begin
()
end
in (
# 2052 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2053 "FStar.TypeChecker.Rel.fst"
let _61_3002 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _145_1463 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _145_1463))
end else begin
()
end
in (
# 2054 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _145_1464 = (FStar_Syntax_Util.unmeta f)
in _145_1464.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _61_3007 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2057 "FStar.TypeChecker.Rel.fst"
let _61_3009 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _61_3009.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_3009.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_3009.FStar_TypeChecker_Env.implicits})))))
end))

# 2059 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _145_1476 = (let _145_1475 = (let _145_1474 = (let _145_1473 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _145_1473 (fun _145_1472 -> FStar_TypeChecker_Common.NonTrivial (_145_1472))))
in {FStar_TypeChecker_Env.guard_f = _145_1474; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _145_1475))
in (FStar_All.pipe_left (fun _145_1471 -> Some (_145_1471)) _145_1476))
end))

# 2064 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2065 "FStar.TypeChecker.Rel.fst"
let _61_3020 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1484 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1483 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _145_1484 _145_1483)))
end else begin
()
end
in (
# 2067 "FStar.TypeChecker.Rel.fst"
let prob = (let _145_1487 = (let _145_1486 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _145_1486))
in (FStar_All.pipe_left (fun _145_1485 -> FStar_TypeChecker_Common.TProb (_145_1485)) _145_1487))
in (
# 2068 "FStar.TypeChecker.Rel.fst"
let g = (let _145_1489 = (solve_and_commit env (singleton env prob) (fun _61_3023 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1489))
in g))))

# 2071 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _145_1499 = (let _145_1498 = (let _145_1497 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1496 = (FStar_TypeChecker_Env.get_range env)
in (_145_1497, _145_1496)))
in FStar_Syntax_Syntax.Error (_145_1498))
in (Prims.raise _145_1499))
end
| Some (g) -> begin
(
# 2075 "FStar.TypeChecker.Rel.fst"
let _61_3032 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1502 = (FStar_Syntax_Print.term_to_string t1)
in (let _145_1501 = (FStar_Syntax_Print.term_to_string t2)
in (let _145_1500 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _145_1502 _145_1501 _145_1500))))
end else begin
()
end
in g)
end))

# 2082 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2083 "FStar.TypeChecker.Rel.fst"
let _61_3037 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1510 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1509 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _145_1510 _145_1509)))
end else begin
()
end
in (
# 2085 "FStar.TypeChecker.Rel.fst"
let _61_3041 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_61_3041) with
| (prob, x) -> begin
(
# 2086 "FStar.TypeChecker.Rel.fst"
let g = (let _145_1512 = (solve_and_commit env (singleton env prob) (fun _61_3042 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1512))
in (
# 2087 "FStar.TypeChecker.Rel.fst"
let _61_3045 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _145_1516 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _145_1515 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _145_1514 = (let _145_1513 = (FStar_Util.must g)
in (guard_to_string env _145_1513))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _145_1516 _145_1515 _145_1514))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2095 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _145_1523 = (let _145_1522 = (let _145_1521 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _145_1520 = (FStar_TypeChecker_Env.get_range env)
in (_145_1521, _145_1520)))
in FStar_Syntax_Syntax.Error (_145_1522))
in (Prims.raise _145_1523)))

# 2099 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2100 "FStar.TypeChecker.Rel.fst"
let _61_3053 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1531 = (FStar_Syntax_Print.comp_to_string c1)
in (let _145_1530 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _145_1531 _145_1530)))
end else begin
()
end
in (
# 2102 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2103 "FStar.TypeChecker.Rel.fst"
let prob = (let _145_1534 = (let _145_1533 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _145_1533 "sub_comp"))
in (FStar_All.pipe_left (fun _145_1532 -> FStar_TypeChecker_Common.CProb (_145_1532)) _145_1534))
in (let _145_1536 = (solve_and_commit env (singleton env prob) (fun _61_3057 -> None))
in (FStar_All.pipe_left (with_guard env prob) _145_1536))))))

# 2107 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2108 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2109 "FStar.TypeChecker.Rel.fst"
let _61_3066 = (FStar_Unionfind.rollback tx)
in (
# 2110 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _145_1554 = (let _145_1553 = (let _145_1552 = (let _145_1550 = (FStar_Syntax_Print.univ_to_string u1)
in (let _145_1549 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _145_1550 _145_1549 msg)))
in (let _145_1551 = (FStar_TypeChecker_Env.get_range env)
in (_145_1552, _145_1551)))
in FStar_Syntax_Syntax.Error (_145_1553))
in (Prims.raise _145_1554)))))
in (
# 2119 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2122 "FStar.TypeChecker.Rel.fst"
let _61_3082 = hd
in (match (_61_3082) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _145_1561 = (insert uv u1 tl)
in (hd)::_145_1561)
end
end))
end))
in (
# 2127 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2130 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2133 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _145_1566 = (insert uv u1 out)
in (group_by _145_1566 rest))
end)
end
| _61_3097 -> begin
None
end))
end))
in (
# 2140 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _61_3099 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _61_3102 -> begin
(
# 2145 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2145 "FStar.TypeChecker.Rel.fst"
let _61_3103 = (empty_worklist env)
in {attempting = _61_3103.attempting; wl_deferred = _61_3103.wl_deferred; ctr = _61_3103.ctr; defer_ok = true; smt_ok = _61_3103.smt_ok; tcenv = _61_3103.tcenv})
in (
# 2146 "FStar.TypeChecker.Rel.fst"
let _61_3143 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _61_3108 -> (match (_61_3108) with
| (u1, u2) -> begin
(
# 2147 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2148 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _61_3113 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2154 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _61_3123 -> begin
(u1)::[]
end)
in (
# 2157 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _61_3128 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _61_27 -> (match (_61_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2163 "FStar.TypeChecker.Rel.fst"
let _61_3135 = (FStar_Syntax_Util.univ_kernel u)
in (match (_61_3135) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2165 "FStar.TypeChecker.Rel.fst"
let _61_3139 = (FStar_Syntax_Util.univ_kernel u')
in (match (_61_3139) with
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
| USolved (_61_3141) -> begin
()
end)
end)))
end))))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange "Universe inequality check not fully implemented")))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2176 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2176 "FStar.TypeChecker.Rel.fst"
let _61_3147 = (empty_worklist env)
in {attempting = _61_3147.attempting; wl_deferred = _61_3147.wl_deferred; ctr = _61_3147.ctr; defer_ok = false; smt_ok = _61_3147.smt_ok; tcenv = _61_3147.tcenv})
in (
# 2177 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _61_3162 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2189 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2190 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2191 "FStar.TypeChecker.Rel.fst"
let _61_3167 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2194 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2195 "FStar.TypeChecker.Rel.fst"
let fail = (fun _61_3174 -> (match (_61_3174) with
| (d, s) -> begin
(
# 2196 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2198 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2199 "FStar.TypeChecker.Rel.fst"
let _61_3177 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1587 = (wl_to_string wl)
in (let _145_1586 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _145_1587 _145_1586)))
end else begin
()
end
in (
# 2201 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2202 "FStar.TypeChecker.Rel.fst"
let _61_3181 = g
in {FStar_TypeChecker_Env.guard_f = _61_3181.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _61_3181.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_3181.FStar_TypeChecker_Env.implicits})
end
| _61_3184 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2204 "FStar.TypeChecker.Rel.fst"
let _61_3186 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2205 "FStar.TypeChecker.Rel.fst"
let _61_3188 = g
in {FStar_TypeChecker_Env.guard_f = _61_3188.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _61_3188.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _61_3188.FStar_TypeChecker_Env.implicits})))))))

# 2207 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2208 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2209 "FStar.TypeChecker.Rel.fst"
let _61_3203 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2213 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2217 "FStar.TypeChecker.Rel.fst"
let _61_3201 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _145_1604 = (FStar_TypeChecker_Env.get_range env)
in (let _145_1603 = (let _145_1602 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _145_1602))
in (FStar_TypeChecker_Errors.diag _145_1604 _145_1603)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2222 "FStar.TypeChecker.Rel.fst"
let _61_3205 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _61_3205.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_3205.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_3205.FStar_TypeChecker_Env.implicits}))))

# 2224 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2226 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2227 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _61_3214 -> begin
false
end))
in (
# 2230 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _61_3218 implicits -> (match (_61_3218) with
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
# 2234 "FStar.TypeChecker.Rel.fst"
let _61_3229 = hd
in (match (_61_3229) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2237 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2238 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2239 "FStar.TypeChecker.Rel.fst"
let _61_3232 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _145_1620 = (FStar_Syntax_Print.uvar_to_string u)
in (let _145_1619 = (FStar_Syntax_Print.term_to_string tm)
in (let _145_1618 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _145_1620 _145_1619 _145_1618))))
end else begin
()
end
in (
# 2242 "FStar.TypeChecker.Rel.fst"
let _61_3239 = (env.FStar_TypeChecker_Env.type_of (
# 2242 "FStar.TypeChecker.Rel.fst"
let _61_3234 = env
in {FStar_TypeChecker_Env.solver = _61_3234.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _61_3234.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _61_3234.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _61_3234.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _61_3234.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _61_3234.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _61_3234.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _61_3234.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _61_3234.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _61_3234.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _61_3234.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _61_3234.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _61_3234.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _61_3234.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _61_3234.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _61_3234.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _61_3234.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _61_3234.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _61_3234.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _61_3234.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _61_3234.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_61_3239) with
| (_61_3237, g) -> begin
(
# 2243 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2244 "FStar.TypeChecker.Rel.fst"
let _61_3240 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _61_3240.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_3240.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _61_3240.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2246 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _61_3243 -> (match (()) with
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
# 2248 "FStar.TypeChecker.Rel.fst"
let _61_3245 = g
in (let _145_1624 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _61_3245.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _61_3245.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _61_3245.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _145_1624})))))

# 2250 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2251 "FStar.TypeChecker.Rel.fst"
let g = (let _145_1629 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _145_1629 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _145_1630 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _145_1630))
end
| (_61_3254, _61_3256, _61_3258, _61_3260, r)::_61_3252 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2256 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2258 "FStar.TypeChecker.Rel.fst"
let _61_3266 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _61_3266.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _61_3266.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _61_3266.FStar_TypeChecker_Env.implicits}))





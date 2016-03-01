
open Prims
# 60 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _149_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _149_8 Prims.op_Negation)))))
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
| _68_38 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _149_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _149_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _149_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_149_10, uv)))))
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
let ___TERM____0 : uvi  ->  ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_68_44) -> begin
_68_44
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_68_47) -> begin
_68_47
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
let ___Success____0 : solution  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| Success (_68_57) -> begin
_68_57
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_68_60) -> begin
_68_60
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
let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _68_1 -> (match (_68_1) with
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
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _68_2 -> (match (_68_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_109 = (let _149_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _149_107 = (let _149_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _149_105 = (let _149_104 = (let _149_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _149_102 = (let _149_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _149_100 = (let _149_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _149_98 = (let _149_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_149_97)::[])
in (_149_99)::_149_98))
in (_149_101)::_149_100))
in (_149_103)::_149_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_149_104)
in (_149_106)::_149_105))
in (_149_108)::_149_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _149_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _149_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _149_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _149_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_110)))
end))

# 138 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _68_3 -> (match (_68_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _149_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _149_116 FStar_Util.string_of_int))
end
in (let _149_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _149_117)))
end
| TERM ((u, _68_84), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _149_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _149_118 FStar_Util.string_of_int))
end
in (let _149_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _149_119)))
end))

# 147 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _149_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _149_124 (FStar_String.concat ", "))))

# 148 "FStar.TypeChecker.Rel.fst"
let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _149_134 = (let _149_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _149_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _149_134 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _149_137 = (FStar_All.pipe_right args (FStar_List.map (fun _68_97 -> (match (_68_97) with
| (x, _68_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _149_137 (FStar_String.concat " "))))

# 150 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 166 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _68_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _68_101.wl_deferred; ctr = _68_101.ctr; defer_ok = _68_101.defer_ok; smt_ok = _68_101.smt_ok; tcenv = _68_101.tcenv}))

# 167 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _68_105 = (empty_worklist env)
in (let _149_146 = (FStar_List.map Prims.snd g)
in {attempting = _149_146; wl_deferred = _68_105.wl_deferred; ctr = _68_105.ctr; defer_ok = false; smt_ok = _68_105.smt_ok; tcenv = _68_105.tcenv})))

# 168 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _68_110 = wl
in {attempting = _68_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _68_110.ctr; defer_ok = _68_110.defer_ok; smt_ok = _68_110.smt_ok; tcenv = _68_110.tcenv}))

# 169 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _68_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _68_114.wl_deferred; ctr = _68_114.ctr; defer_ok = _68_114.defer_ok; smt_ok = _68_114.smt_ok; tcenv = _68_114.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _68_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _149_163))
end else begin
()
end
in Failed ((prob, reason))))

# 175 "FStar.TypeChecker.Rel.fst"
let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _68_4 -> (match (_68_4) with
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
let _68_126 = p
in {FStar_TypeChecker_Common.pid = _68_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _68_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_126.FStar_TypeChecker_Common.rank}))

# 187 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _68_5 -> (match (_68_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_170 -> FStar_TypeChecker_Common.TProb (_149_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_171 -> FStar_TypeChecker_Common.CProb (_149_171)))
end))

# 191 "FStar.TypeChecker.Rel.fst"
let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _68_6 -> (match (_68_6) with
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
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _68_7 -> (match (_68_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 198 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _68_8 -> (match (_68_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 201 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _68_9 -> (match (_68_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 204 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _68_10 -> (match (_68_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 207 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _68_11 -> (match (_68_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 210 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _68_12 -> (match (_68_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 213 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _68_13 -> (match (_68_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _149_190 -> FStar_TypeChecker_Common.TProb (_149_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _149_191 -> FStar_TypeChecker_Common.CProb (_149_191)) (invert p))
end))

# 216 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 217 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _68_176 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _68_177 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 220 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _149_204 = (next_pid ())
in (let _149_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _149_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 233 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _149_214 = (next_pid ())
in (let _149_213 = (let _149_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _149_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _149_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 247 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _149_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _149_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 259 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 263 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _149_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _149_232 = (prob_to_string env d)
in (let _149_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _149_233 _149_232 _149_231 s)))))

# 269 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _68_14 -> (match (_68_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _68_218 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _68_221), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 284 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _68_15 -> (match (_68_15) with
| UNIV (_68_230) -> begin
None
end
| TERM ((u, _68_234), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 288 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _68_16 -> (match (_68_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _68_247 -> begin
None
end))))

# 292 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_252 = (let _149_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _149_251))
in (FStar_Syntax_Subst.compress _149_252)))

# 302 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _149_257)))

# 303 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _149_260 = (sn env (Prims.fst t))
in (_149_260, (Prims.snd t))))

# 304 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _68_258 -> (match (_68_258) with
| (x, imp) -> begin
(let _149_267 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _68_259 = x
in (let _149_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_266}))
in (_149_267, imp))
end)))))

# 306 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _149_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_149_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _149_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_149_275))
end
| _68_271 -> begin
u
end)))
in (let _149_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _149_276))))

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
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _68_291; FStar_Syntax_Syntax.pos = _68_289; FStar_Syntax_Syntax.vars = _68_287} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _149_290 = (let _149_289 = (FStar_Syntax_Print.term_to_string tt)
in (let _149_288 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _149_289 _149_288)))
in (FStar_All.failwith _149_290))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(
# 343 "FStar.TypeChecker.Rel.fst"
let _68_309 = (let _149_291 = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (aux true _149_291))
in (match (_68_309) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _68_312 -> begin
(t2', refinement)
end)
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
(let _149_294 = (let _149_293 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_292 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _149_293 _149_292)))
in (FStar_All.failwith _149_294))
end))
in (let _149_295 = (whnf env t1)
in (aux false _149_295))))

# 365 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _149_300 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _149_300 Prims.fst)))

# 367 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _149_303 = (FStar_Syntax_Syntax.null_bv t)
in (_149_303, FStar_Syntax_Util.t_true)))

# 369 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _68_358 = (base_and_refinement env wl t)
in (match (_68_358) with
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
let force_refinement = (fun _68_366 -> (match (_68_366) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _68_374 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_68_374) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 381 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _68_17 -> (match (_68_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_316 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _149_315 = (let _149_312 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _149_312))
in (let _149_314 = (let _149_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _149_313))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _149_316 _149_315 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_314))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _149_319 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _149_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_317 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _149_319 _149_318 (rel_to_string p.FStar_TypeChecker_Common.relation) _149_317))))
end))

# 404 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _149_325 = (let _149_324 = (let _149_323 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _68_387 -> (match (_68_387) with
| (_68_383, _68_385, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _149_323))
in (FStar_List.map (wl_prob_to_string wl) _149_324))
in (FStar_All.pipe_right _149_325 (FStar_String.concat "\n\t"))))

# 407 "FStar.TypeChecker.Rel.fst"
let u_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun x y -> (FStar_Syntax_Util.abs x y None))

# 416 "FStar.TypeChecker.Rel.fst"
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
let _68_402 = (p_guard prob)
in (match (_68_402) with
| (_68_400, uv) -> begin
(
# 423 "FStar.TypeChecker.Rel.fst"
let _68_415 = (match ((let _149_340 = (FStar_Syntax_Subst.compress uv)
in _149_340.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 425 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 426 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _149_342 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _149_342 Prims.op_Negation)))))
in (
# 427 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs bs phi)
in (
# 428 "FStar.TypeChecker.Rel.fst"
let _68_411 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _149_345 = (FStar_Util.string_of_int (p_pid prob))
in (let _149_344 = (FStar_Syntax_Print.term_to_string uv)
in (let _149_343 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _149_345 _149_344 _149_343))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _68_414 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 435 "FStar.TypeChecker.Rel.fst"
let _68_417 = (commit uvis)
in (
# 436 "FStar.TypeChecker.Rel.fst"
let _68_419 = wl
in {attempting = _68_419.attempting; wl_deferred = _68_419.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _68_419.defer_ok; smt_ok = _68_419.smt_ok; tcenv = _68_419.tcenv})))
end))))

# 436 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 439 "FStar.TypeChecker.Rel.fst"
let _68_424 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_354 = (FStar_Util.string_of_int pid)
in (let _149_353 = (let _149_352 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _149_352 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _149_354 _149_353)))
end else begin
()
end
in (
# 441 "FStar.TypeChecker.Rel.fst"
let _68_426 = (commit sol)
in (
# 442 "FStar.TypeChecker.Rel.fst"
let _68_428 = wl
in {attempting = _68_428.attempting; wl_deferred = _68_428.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _68_428.defer_ok; smt_ok = _68_428.smt_ok; tcenv = _68_428.tcenv}))))

# 442 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 445 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_68_438, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _149_367 = (FStar_Syntax_Util.mk_conj t f)
in Some (_149_367))
end))
in (
# 449 "FStar.TypeChecker.Rel.fst"
let _68_450 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_370 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _149_369 = (let _149_368 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _149_368 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _149_370 _149_369)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 451 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _149_380 = (let _149_378 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _149_378 FStar_Util.set_elements))
in (FStar_All.pipe_right _149_380 (FStar_Util.for_some (fun _68_459 -> (match (_68_459) with
| (uv, _68_458) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 465 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 468 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 469 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _149_387 = (let _149_386 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _149_385 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _149_386 _149_385)))
in Some (_149_387))
end
in (occurs_ok, msg))))

# 474 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 477 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 478 "FStar.TypeChecker.Rel.fst"
let _68_474 = (occurs_check env wl uk t)
in (match (_68_474) with
| (occurs_ok, msg) -> begin
(let _149_419 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _149_419, (msg, fvs, fvs_t)))
end))))

# 479 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 482 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 484 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 485 "FStar.TypeChecker.Rel.fst"
let _68_492 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _68_484 _68_487 -> (match ((_68_484, _68_487)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _149_428 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _149_428)) then begin
(isect, isect_set)
end else begin
(
# 491 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _149_429 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _149_429))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_68_492) with
| (isect, _68_491) -> begin
(FStar_List.rev isect)
end)))))

# 496 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _68_498 _68_502 -> (match ((_68_498, _68_502)) with
| ((a, _68_497), (b, _68_501)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 500 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 503 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _68_512 -> (match (_68_512) with
| (b, _68_511) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _68_514 -> begin
None
end)))

# 510 "FStar.TypeChecker.Rel.fst"
let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 516 "FStar.TypeChecker.Rel.fst"
let _68_523 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_444 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _149_444))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 518 "FStar.TypeChecker.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _68_537; FStar_Syntax_Syntax.pos = _68_535; FStar_Syntax_Syntax.vars = _68_533}, args) -> begin
(t, uv, k, args)
end
| _68_547 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 523 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 526 "FStar.TypeChecker.Rel.fst"
let _68_554 = (destruct_flex_t t)
in (match (_68_554) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _68_558 -> begin
((t, uv, k, args), None)
end)
end)))

# 529 "FStar.TypeChecker.Rel.fst"
type match_result =
| MisMatch
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

# 603 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _68_18 -> (match (_68_18) with
| MisMatch -> begin
MisMatch
end
| _68_562 -> begin
HeadMatch
end))

# 607 "FStar.TypeChecker.Rel.fst"
let rec head_matches : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun t1 t2 -> (match ((let _149_460 = (let _149_457 = (FStar_Syntax_Util.unmeta t1)
in _149_457.FStar_Syntax_Syntax.n)
in (let _149_459 = (let _149_458 = (FStar_Syntax_Util.unmeta t2)
in _149_458.FStar_Syntax_Syntax.n)
in (_149_460, _149_459)))) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _68_577), FStar_Syntax_Syntax.Tm_uinst (g, _68_582)) -> begin
(let _149_461 = (head_matches f g)
in (FStar_All.pipe_right _149_461 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _68_593), FStar_Syntax_Syntax.Tm_uvar (uv', _68_598)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_604), FStar_Syntax_Syntax.Tm_refine (y, _68_609)) -> begin
(let _149_462 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_462 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_615), _68_619) -> begin
(let _149_463 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _149_463 head_match))
end
| (_68_622, FStar_Syntax_Syntax.Tm_refine (x, _68_625)) -> begin
(let _149_464 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_464 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_645), FStar_Syntax_Syntax.Tm_app (head', _68_650)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_656), _68_660) -> begin
(head_matches head t2)
end
| (_68_663, FStar_Syntax_Syntax.Tm_app (head, _68_666)) -> begin
(head_matches t1 head)
end
| _68_671 -> begin
MisMatch
end))

# 629 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 633 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 634 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_682 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (
# 635 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 3) then begin
(fail ())
end else begin
(
# 639 "FStar.TypeChecker.Rel.fst"
let steps = if (d = 0) then begin
(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.WHNF)::[]
end else begin
if (d = 1) then begin
(FStar_TypeChecker_Normalize.Unfold)::(FStar_TypeChecker_Normalize.WHNF)::[]
end else begin
(FStar_TypeChecker_Normalize.Unfold)::[]
end
end
in (
# 645 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement steps env wl t1)
in (
# 646 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement steps env wl t2)
in (aux (d + 1) t1' t2'))))
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux 0 t1 t2)))))

# 649 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 652 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 653 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 652 "FStar.TypeChecker.Rel.fst"
let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_68_694) -> begin
_68_694
end))

# 653 "FStar.TypeChecker.Rel.fst"
let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_68_697) -> begin
_68_697
end))

# 653 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 654 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun env t -> (
# 657 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 658 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 661 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 662 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_68_712, imp), T (t)) -> begin
(t, imp)
end
| _68_719 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 667 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _68_724 -> (match (_68_724) with
| (t, _68_723) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 673 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_731 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 674 "FStar.TypeChecker.Rel.fst"
let _68_734 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_734) with
| (bs, c) -> begin
(
# 676 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 677 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 678 "FStar.TypeChecker.Rel.fst"
let _68_751 = x
in {FStar_Syntax_Syntax.ppname = _68_751.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_751.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _68_759 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 683 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _68_19 -> (match (_68_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 686 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _149_558 = (decompose [] bs)
in (rebuild, matches, _149_558))))
end)))
end
| _68_769 -> begin
(
# 694 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _68_20 -> (match (_68_20) with
| [] -> begin
t
end
| _68_773 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 698 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _68_21 -> (match (_68_21) with
| T (t) -> begin
t
end
| _68_780 -> begin
(FStar_All.failwith "Impossible")
end))

# 702 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _68_22 -> (match (_68_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _68_785 -> begin
(FStar_All.failwith "Impossible")
end))

# 706 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 713 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 714 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 715 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_68_798, variance, T (ti)) -> begin
(
# 718 "FStar.TypeChecker.Rel.fst"
let k = (
# 719 "FStar.TypeChecker.Rel.fst"
let _68_806 = (FStar_Syntax_Util.type_u ())
in (match (_68_806) with
| (t, _68_805) -> begin
(let _149_580 = (new_uvar r scope t)
in (Prims.fst _149_580))
end))
in (
# 721 "FStar.TypeChecker.Rel.fst"
let _68_810 = (new_uvar r scope k)
in (match (_68_810) with
| (gi_xs, gi) -> begin
(
# 722 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _68_813 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _149_583 = (let _149_582 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _149_581 -> FStar_TypeChecker_Common.TProb (_149_581)) _149_582))
in (T (gi_xs), _149_583)))
end)))
end
| (_68_816, _68_818, C (_68_820)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 730 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 734 "FStar.TypeChecker.Rel.fst"
let _68_898 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _68_838; FStar_Syntax_Syntax.pos = _68_836; FStar_Syntax_Syntax.vars = _68_834})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_592 = (let _149_591 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _149_590 -> C (_149_590)) _149_591))
in (_149_592, (prob)::[]))
end
| _68_849 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _68_857; FStar_Syntax_Syntax.pos = _68_855; FStar_Syntax_Syntax.vars = _68_853})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_595 = (let _149_594 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _149_593 -> C (_149_593)) _149_594))
in (_149_595, (prob)::[]))
end
| _68_868 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_68_870, _68_872, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _68_878; FStar_Syntax_Syntax.pos = _68_876; FStar_Syntax_Syntax.vars = _68_874})) -> begin
(
# 748 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 749 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 750 "FStar.TypeChecker.Rel.fst"
let _68_889 = (let _149_597 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _149_597 FStar_List.unzip))
in (match (_68_889) with
| (tcs, sub_probs) -> begin
(
# 751 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _149_602 = (let _149_601 = (let _149_598 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _149_598 un_T))
in (let _149_600 = (let _149_599 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _149_599 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _149_601; FStar_Syntax_Syntax.effect_args = _149_600; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_602))
in (C (gi_xs), sub_probs))
end))))
end
| _68_892 -> begin
(
# 760 "FStar.TypeChecker.Rel.fst"
let _68_895 = (sub_prob scope args q)
in (match (_68_895) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_68_898) with
| (tc, probs) -> begin
(
# 763 "FStar.TypeChecker.Rel.fst"
let _68_911 = (match (q) with
| (Some (b), _68_902, _68_904) -> begin
(let _149_604 = (let _149_603 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_149_603)::args)
in (Some (b), (b)::scope, _149_604))
end
| _68_907 -> begin
(None, scope, args)
end)
in (match (_68_911) with
| (bopt, scope, args) -> begin
(
# 767 "FStar.TypeChecker.Rel.fst"
let _68_915 = (aux scope args qs)
in (match (_68_915) with
| (sub_probs, tcs, f) -> begin
(
# 768 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _149_607 = (let _149_606 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_149_606)
in (FStar_Syntax_Util.mk_conj_l _149_607))
end
| Some (b) -> begin
(let _149_611 = (let _149_610 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _149_609 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_149_610)::_149_609))
in (FStar_Syntax_Util.mk_conj_l _149_611))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 774 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 784 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 785 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _68_943), FStar_Syntax_Syntax.Tm_uvar (u2, _68_948)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _68_962 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _68_968 _68_972 -> (match ((_68_968, _68_972)) with
| ((a1, _68_967), (a2, _68_971)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 797 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 802 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 803 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 805 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 806 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 807 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 808 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 809 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 810 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 811 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 812 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 813 "FStar.TypeChecker.Rel.fst"
let _68_975 = p
in (let _149_633 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_632 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _68_975.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_633; FStar_TypeChecker_Common.relation = _68_975.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_632; FStar_TypeChecker_Common.element = _68_975.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_975.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_975.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_975.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_975.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_975.FStar_TypeChecker_Common.rank}))))

# 813 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_639 = (compress_tprob wl p)
in (FStar_All.pipe_right _149_639 (fun _149_638 -> FStar_TypeChecker_Common.TProb (_149_638))))
end
| FStar_TypeChecker_Common.CProb (_68_982) -> begin
p
end))

# 817 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 823 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_644 = (compress_prob wl pr)
in (FStar_All.pipe_right _149_644 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 826 "FStar.TypeChecker.Rel.fst"
let _68_992 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_992) with
| (lh, _68_991) -> begin
(
# 827 "FStar.TypeChecker.Rel.fst"
let _68_996 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_68_996) with
| (rh, _68_995) -> begin
(
# 828 "FStar.TypeChecker.Rel.fst"
let _68_1052 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_68_998), FStar_Syntax_Syntax.Tm_uvar (_68_1001)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_68_1017), _68_1020) -> begin
(
# 835 "FStar.TypeChecker.Rel.fst"
let _68_1024 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_68_1024) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _68_1027 -> begin
(
# 839 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _149_646 = (
# 843 "FStar.TypeChecker.Rel.fst"
let _68_1029 = tp
in (let _149_645 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1029.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1029.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1029.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_645; FStar_TypeChecker_Common.element = _68_1029.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1029.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1029.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1029.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1029.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1029.FStar_TypeChecker_Common.rank}))
in (rank, _149_646)))
end)
end))
end
| (_68_1032, FStar_Syntax_Syntax.Tm_uvar (_68_1034)) -> begin
(
# 847 "FStar.TypeChecker.Rel.fst"
let _68_1039 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1039) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _68_1042 -> begin
(let _149_648 = (
# 850 "FStar.TypeChecker.Rel.fst"
let _68_1043 = tp
in (let _149_647 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1043.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_647; FStar_TypeChecker_Common.relation = _68_1043.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1043.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1043.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1043.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1043.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1043.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1043.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1043.FStar_TypeChecker_Common.rank}))
in (refine_flex, _149_648))
end)
end))
end
| (_68_1046, _68_1048) -> begin
(rigid_rigid, tp)
end)
in (match (_68_1052) with
| (rank, tp) -> begin
(let _149_650 = (FStar_All.pipe_right (
# 855 "FStar.TypeChecker.Rel.fst"
let _68_1053 = tp
in {FStar_TypeChecker_Common.pid = _68_1053.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1053.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1053.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1053.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1053.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1053.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1053.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1053.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1053.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _149_649 -> FStar_TypeChecker_Common.TProb (_149_649)))
in (rank, _149_650))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _149_652 = (FStar_All.pipe_right (
# 857 "FStar.TypeChecker.Rel.fst"
let _68_1057 = cp
in {FStar_TypeChecker_Common.pid = _68_1057.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1057.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1057.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1057.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1057.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1057.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1057.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1057.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1057.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _149_651 -> FStar_TypeChecker_Common.CProb (_149_651)))
in (rigid_rigid, _149_652))
end)))

# 857 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 863 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _68_1064 probs -> (match (_68_1064) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 866 "FStar.TypeChecker.Rel.fst"
let _68_1072 = (rank wl hd)
in (match (_68_1072) with
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

# 877 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 879 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 882 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 883 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 884 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 882 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_68_1082) -> begin
_68_1082
end))

# 883 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_68_1085) -> begin
_68_1085
end))

# 884 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_68_1088) -> begin
_68_1088
end))

# 884 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 887 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 888 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 889 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 892 "FStar.TypeChecker.Rel.fst"
let _68_1104 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_1104) with
| (k, _68_1103) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _68_1108 -> begin
false
end)
end)))))
end
| _68_1110 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 898 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_68_1116), FStar_Syntax_Syntax.U_max (_68_1119)) -> begin
(let _149_724 = (let _149_723 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_722 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _149_723 _149_722)))
in UFailed (_149_724))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 905 "FStar.TypeChecker.Rel.fst"
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
| _68_1139 -> begin
(let _149_731 = (let _149_730 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_729 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _149_730 _149_729 msg)))
in UFailed (_149_731))
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
# 926 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 931 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _149_734 = (let _149_733 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _149_732 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _149_733 _149_732)))
in (try_umax_components u1 u2 _149_734))
end else begin
(let _149_735 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_149_735))
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
# 956 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 957 "FStar.TypeChecker.Rel.fst"
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

# 964 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 971 "FStar.TypeChecker.Rel.fst"
let _68_1234 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_778 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _149_778))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 975 "FStar.TypeChecker.Rel.fst"
let probs = (
# 975 "FStar.TypeChecker.Rel.fst"
let _68_1241 = probs
in {attempting = tl; wl_deferred = _68_1241.wl_deferred; ctr = _68_1241.ctr; defer_ok = _68_1241.defer_ok; smt_ok = _68_1241.smt_ok; tcenv = _68_1241.tcenv})
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
| (None, _68_1253, _68_1255) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _68_1259 -> begin
(
# 997 "FStar.TypeChecker.Rel.fst"
let _68_1268 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _68_1265 -> (match (_68_1265) with
| (c, _68_1262, _68_1264) -> begin
(c < probs.ctr)
end))))
in (match (_68_1268) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _149_781 = (FStar_List.map (fun _68_1274 -> (match (_68_1274) with
| (_68_1271, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_149_781))
end
| _68_1276 -> begin
(let _149_784 = (
# 1003 "FStar.TypeChecker.Rel.fst"
let _68_1277 = probs
in (let _149_783 = (FStar_All.pipe_right attempt (FStar_List.map (fun _68_1284 -> (match (_68_1284) with
| (_68_1280, _68_1282, y) -> begin
y
end))))
in {attempting = _149_783; wl_deferred = rest; ctr = _68_1277.ctr; defer_ok = _68_1277.defer_ok; smt_ok = _68_1277.smt_ok; tcenv = _68_1277.tcenv}))
in (solve env _149_784))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _149_790 = (solve_prob orig None [] wl)
in (solve env _149_790))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1017 "FStar.TypeChecker.Rel.fst"
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
| _68_1319 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _149_805 = (let _149_802 = (whnf env t1)
in _149_802.FStar_Syntax_Syntax.n)
in (let _149_804 = (let _149_803 = (whnf env t2)
in _149_803.FStar_Syntax_Syntax.n)
in (_149_805, _149_804)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _68_1325; FStar_Syntax_Syntax.pos = _68_1323; FStar_Syntax_Syntax.vars = _68_1321}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _68_1337; FStar_Syntax_Syntax.pos = _68_1335; FStar_Syntax_Syntax.vars = _68_1333}, us2)) -> begin
(
# 1032 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1033 "FStar.TypeChecker.Rel.fst"
let _68_1346 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _68_1361 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1046 "FStar.TypeChecker.Rel.fst"
let _68_1366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_810 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _149_810 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1056 "FStar.TypeChecker.Rel.fst"
let _68_1371 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_814 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _149_814))
end else begin
()
end
in (
# 1058 "FStar.TypeChecker.Rel.fst"
let _68_1375 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1375) with
| (u, args) -> begin
(
# 1059 "FStar.TypeChecker.Rel.fst"
let _68_1381 = (0, 1, 2, 3, 4)
in (match (_68_1381) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1060 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1062 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1063 "FStar.TypeChecker.Rel.fst"
let _68_1390 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1390) with
| (h1, args1) -> begin
(
# 1064 "FStar.TypeChecker.Rel.fst"
let _68_1394 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1394) with
| (h2, _68_1393) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _149_826 = (let _149_825 = (let _149_824 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _149_823 -> FStar_TypeChecker_Common.TProb (_149_823)) _149_824))
in (_149_825)::[])
in Some (_149_826))
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
| _68_1406 -> begin
None
end)
end))
end)))
in (
# 1080 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1082 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1086 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1087 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1088 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1089 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _149_833 = (let _149_832 = (let _149_831 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _149_831))
in (_149_832, m))
in Some (_149_833))))))
end))
end
| (_68_1428, FStar_Syntax_Syntax.Tm_refine (y, _68_1431)) -> begin
(
# 1094 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_1441), _68_1445) -> begin
(
# 1101 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _68_1452 -> begin
(
# 1108 "FStar.TypeChecker.Rel.fst"
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
# 1114 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _68_1460) -> begin
(
# 1118 "FStar.TypeChecker.Rel.fst"
let _68_1485 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _68_23 -> (match (_68_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1122 "FStar.TypeChecker.Rel.fst"
let _68_1471 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1471) with
| (u', _68_1470) -> begin
(match ((let _149_835 = (whnf env u')
in _149_835.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _68_1474) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _68_1478 -> begin
false
end)
end))
end
| _68_1480 -> begin
false
end)
end
| _68_1482 -> begin
false
end))))
in (match (_68_1485) with
| (upper_bounds, rest) -> begin
(
# 1131 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _68_1489 tps -> (match (_68_1489) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _149_840 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _149_840))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _68_1502 -> begin
None
end)
end))
in (match ((let _149_842 = (let _149_841 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_149_841, []))
in (make_upper_bound _149_842 upper_bounds))) with
| None -> begin
(
# 1142 "FStar.TypeChecker.Rel.fst"
let _68_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1155 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1156 "FStar.TypeChecker.Rel.fst"
let _68_1514 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1157 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1157 "FStar.TypeChecker.Rel.fst"
let _68_1511 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _68_1511.wl_deferred; ctr = _68_1511.ctr; defer_ok = _68_1511.defer_ok; smt_ok = _68_1511.smt_ok; tcenv = _68_1511.tcenv})
in (let _149_843 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _149_843)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1159 "FStar.TypeChecker.Rel.fst"
let _68_1516 = wl
in {attempting = sub_probs; wl_deferred = _68_1516.wl_deferred; ctr = _68_1516.ctr; defer_ok = _68_1516.defer_ok; smt_ok = _68_1516.smt_ok; tcenv = _68_1516.tcenv}))) with
| Success (_68_1519) -> begin
(
# 1161 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1161 "FStar.TypeChecker.Rel.fst"
let _68_1521 = wl
in {attempting = rest; wl_deferred = _68_1521.wl_deferred; ctr = _68_1521.ctr; defer_ok = _68_1521.defer_ok; smt_ok = _68_1521.smt_ok; tcenv = _68_1521.tcenv})
in (
# 1162 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1163 "FStar.TypeChecker.Rel.fst"
let _68_1527 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _68_1530 -> begin
None
end)))
end))
end))
end
| _68_1532 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1173 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1176 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1177 "FStar.TypeChecker.Rel.fst"
let _68_1549 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_871 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _149_871))
end else begin
()
end
in (
# 1179 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1183 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1183 "FStar.TypeChecker.Rel.fst"
let _68_1563 = hd1
in (let _149_872 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_872}))
in (
# 1184 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1184 "FStar.TypeChecker.Rel.fst"
let _68_1566 = hd2
in (let _149_873 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_873}))
in (
# 1185 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_876 = (let _149_875 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _149_875 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _149_874 -> FStar_TypeChecker_Common.TProb (_149_874)) _149_876))
in (
# 1186 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1187 "FStar.TypeChecker.Rel.fst"
let subst = (let _149_877 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_149_877)
in (
# 1188 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1191 "FStar.TypeChecker.Rel.fst"
let phi = (let _149_879 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _149_878 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _149_879 _149_878)))
in (
# 1192 "FStar.TypeChecker.Rel.fst"
let _68_1578 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_881 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_880 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _149_881 _149_880)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _68_1582 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1201 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1205 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _149_885 = (compress_tprob wl problem)
in (solve_t' env _149_885 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1212 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1215 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1216 "FStar.TypeChecker.Rel.fst"
let _68_1610 = (head_matches_delta env wl t1 t2)
in (match (_68_1610) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _68_1613) -> begin
(
# 1219 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_68_1618) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _68_1622) -> begin
(FStar_TypeChecker_Env.is_projector env tc.FStar_Syntax_Syntax.v)
end
| _68_1626 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1224 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1227 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1231 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _149_914 = (let _149_913 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _149_913 t2))
in (FStar_Syntax_Util.mk_forall x _149_914)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _149_915 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _149_915)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_68_1636, Some (t1, t2)) -> begin
(solve_t env (
# 1240 "FStar.TypeChecker.Rel.fst"
let _68_1642 = problem
in {FStar_TypeChecker_Common.pid = _68_1642.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_1642.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_1642.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1642.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1642.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1642.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1642.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1642.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_1645, None) -> begin
(
# 1243 "FStar.TypeChecker.Rel.fst"
let _68_1648 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_919 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_918 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_917 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_916 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _149_919 _149_918 _149_917 _149_916)))))
end else begin
()
end
in (
# 1247 "FStar.TypeChecker.Rel.fst"
let _68_1652 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1652) with
| (head, args) -> begin
(
# 1248 "FStar.TypeChecker.Rel.fst"
let _68_1655 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1655) with
| (head', args') -> begin
(
# 1249 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _149_924 = (let _149_923 = (FStar_Syntax_Print.term_to_string head)
in (let _149_922 = (args_to_string args)
in (let _149_921 = (FStar_Syntax_Print.term_to_string head')
in (let _149_920 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _149_923 _149_922 _149_921 _149_920)))))
in (giveup env _149_924 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _149_925 = (solve_prob orig None [] wl)
in (solve env _149_925))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1270 "FStar.TypeChecker.Rel.fst"
let _68_1665 = (base_and_refinement env wl t1)
in (match (_68_1665) with
| (base1, refinement1) -> begin
(
# 1271 "FStar.TypeChecker.Rel.fst"
let _68_1668 = (base_and_refinement env wl t2)
in (match (_68_1668) with
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
# 1278 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _68_1681 _68_1685 -> (match ((_68_1681, _68_1685)) with
| ((a, _68_1680), (a', _68_1684)) -> begin
(let _149_929 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _149_928 -> FStar_TypeChecker_Common.TProb (_149_928)) _149_929))
end)) args args')
in (
# 1279 "FStar.TypeChecker.Rel.fst"
let formula = (let _149_931 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _149_931))
in (
# 1280 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _68_1691 -> begin
(
# 1285 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1286 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1287 "FStar.TypeChecker.Rel.fst"
let _68_1694 = problem
in {FStar_TypeChecker_Common.pid = _68_1694.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _68_1694.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _68_1694.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1694.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1694.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1694.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1694.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1694.FStar_TypeChecker_Common.rank}) wl)))
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
# 1293 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1294 "FStar.TypeChecker.Rel.fst"
let _68_1711 = p
in (match (_68_1711) with
| ((u, k), ps, xs, (h, _68_1708, qs)) -> begin
(
# 1295 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1300 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1301 "FStar.TypeChecker.Rel.fst"
let _68_1717 = (imitation_sub_probs orig env xs ps qs)
in (match (_68_1717) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1302 "FStar.TypeChecker.Rel.fst"
let im = (let _149_942 = (h gs_xs)
in (u_abs xs _149_942))
in (
# 1303 "FStar.TypeChecker.Rel.fst"
let _68_1719 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_947 = (FStar_Syntax_Print.term_to_string im)
in (let _149_946 = (FStar_Syntax_Print.tag_of_term im)
in (let _149_945 = (let _149_943 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _149_943 (FStar_String.concat ", ")))
in (let _149_944 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _149_947 _149_946 _149_945 _149_944)))))
end else begin
()
end
in (
# 1308 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1313 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1314 "FStar.TypeChecker.Rel.fst"
let _68_1735 = p
in (match (_68_1735) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1318 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1319 "FStar.TypeChecker.Rel.fst"
let _68_1740 = (FStar_List.nth ps i)
in (match (_68_1740) with
| (pi, _68_1739) -> begin
(
# 1320 "FStar.TypeChecker.Rel.fst"
let _68_1744 = (FStar_List.nth xs i)
in (match (_68_1744) with
| (xi, _68_1743) -> begin
(
# 1322 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1323 "FStar.TypeChecker.Rel.fst"
let _68_1749 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1749) with
| (bs, k) -> begin
(
# 1324 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _68_1757)::tl -> begin
(
# 1327 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1328 "FStar.TypeChecker.Rel.fst"
let _68_1763 = (new_uvar r xs k_a)
in (match (_68_1763) with
| (gi_xs, gi) -> begin
(
# 1329 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1330 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1331 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1332 "FStar.TypeChecker.Rel.fst"
let _68_1769 = (aux subst tl)
in (match (_68_1769) with
| (gi_xs', gi_ps') -> begin
(let _149_969 = (let _149_966 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_149_966)::gi_xs')
in (let _149_968 = (let _149_967 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_149_967)::gi_ps')
in (_149_969, _149_968)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _149_970 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _149_970)) then begin
None
end else begin
(
# 1338 "FStar.TypeChecker.Rel.fst"
let _68_1773 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_68_1773) with
| (g_xs, _68_1772) -> begin
(
# 1339 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1340 "FStar.TypeChecker.Rel.fst"
let proj = (let _149_971 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _149_971))
in (
# 1341 "FStar.TypeChecker.Rel.fst"
let sub = (let _149_977 = (let _149_976 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _149_975 = (let _149_974 = (FStar_List.map (fun _68_1781 -> (match (_68_1781) with
| (_68_1777, _68_1779, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _149_974))
in (mk_problem (p_scope orig) orig _149_976 (p_rel orig) _149_975 None "projection")))
in (FStar_All.pipe_left (fun _149_972 -> FStar_TypeChecker_Common.TProb (_149_972)) _149_977))
in (
# 1342 "FStar.TypeChecker.Rel.fst"
let _68_1783 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_979 = (FStar_Syntax_Print.term_to_string proj)
in (let _149_978 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _149_979 _149_978)))
end else begin
()
end
in (
# 1343 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_981 = (let _149_980 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_149_980))
in (solve_prob orig _149_981 ((TERM ((u, proj)))::[]) wl))
in (let _149_983 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _149_982 -> Some (_149_982)) _149_983)))))))
end))
end)
end))
end)))
end)))
in (
# 1348 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1349 "FStar.TypeChecker.Rel.fst"
let _68_1797 = lhs
in (match (_68_1797) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1350 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1351 "FStar.TypeChecker.Rel.fst"
let xs = (let _149_1010 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _149_1010 Prims.fst))
in (let _149_1015 = (decompose env t2)
in ((uv, k), ps, xs, _149_1015))))
in (
# 1354 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1357 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_68_1807) -> begin
(
# 1361 "FStar.TypeChecker.Rel.fst"
let _68_1809 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1368 "FStar.TypeChecker.Rel.fst"
let _68_1817 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1372 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1373 "FStar.TypeChecker.Rel.fst"
let _68_1827 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1827) with
| (hd, _68_1826) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _68_1838 -> begin
(
# 1379 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1382 "FStar.TypeChecker.Rel.fst"
let _68_1840 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1026 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _149_1026))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1385 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1386 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _149_1030 = (let _149_1029 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1029 Prims.fst))
in (FStar_All.pipe_right _149_1030 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1393 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1394 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1395 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1396 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1397 "FStar.TypeChecker.Rel.fst"
let _68_1853 = (occurs_check env wl (uv, k) t2)
in (match (_68_1853) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _149_1032 = (let _149_1031 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _149_1031))
in (giveup_or_defer orig _149_1032))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _149_1033 = (subterms args_lhs)
in (imitate orig env wl _149_1033))
end else begin
(
# 1404 "FStar.TypeChecker.Rel.fst"
let _68_1854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1036 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1035 = (names_to_string fvs1)
in (let _149_1034 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _149_1036 _149_1035 _149_1034))))
end else begin
()
end
in (
# 1409 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _68_1858 -> begin
(let _149_1037 = (sn_binders env vars)
in (u_abs _149_1037 t2))
end)
in (
# 1412 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1417 "FStar.TypeChecker.Rel.fst"
let _68_1861 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1040 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1039 = (names_to_string fvs1)
in (let _149_1038 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _149_1040 _149_1039 _149_1038))))
end else begin
()
end
in (let _149_1041 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1041 (- (1)))))
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
if (let _149_1042 = (FStar_Syntax_Free.names t1)
in (check_head _149_1042 t2)) then begin
(
# 1429 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1430 "FStar.TypeChecker.Rel.fst"
let _68_1865 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1043 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _149_1043 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _149_1044 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1044 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1455 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1458 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _68_1877 -> (match (_68_1877) with
| (t, u, k, args) -> begin
(
# 1461 "FStar.TypeChecker.Rel.fst"
let _68_1881 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1881) with
| (all_formals, _68_1880) -> begin
(
# 1462 "FStar.TypeChecker.Rel.fst"
let _68_1882 = ()
in (
# 1464 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1472 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _68_1895 -> (match (_68_1895) with
| (x, imp) -> begin
(let _149_1066 = (FStar_Syntax_Syntax.bv_to_name x)
in (_149_1066, imp))
end))))
in (
# 1473 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1474 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1475 "FStar.TypeChecker.Rel.fst"
let _68_1901 = (FStar_Syntax_Util.type_u ())
in (match (_68_1901) with
| (t, _68_1900) -> begin
(let _149_1067 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _149_1067))
end))
in (
# 1477 "FStar.TypeChecker.Rel.fst"
let _68_1905 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_68_1905) with
| (t', tm_u1) -> begin
(
# 1478 "FStar.TypeChecker.Rel.fst"
let _68_1912 = (destruct_flex_t t')
in (match (_68_1912) with
| (_68_1907, u1, k1, _68_1911) -> begin
(
# 1479 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1069 = (let _149_1068 = (u_abs all_formals t')
in ((u, k), _149_1068))
in TERM (_149_1069))
in (
# 1480 "FStar.TypeChecker.Rel.fst"
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
# 1489 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _68_1931 -> (match (_68_1931) with
| (x, _68_1930) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1496 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _149_1071 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _149_1071 formals tl))
end)
end)
end)
end
| _68_1935 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _149_1072 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _149_1072 all_formals args))))
end))
end))
in (
# 1508 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _68_1941 _68_1945 r -> (match ((_68_1941, _68_1945)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _149_1081 = (solve_prob orig None [] wl)
in (solve env _149_1081))
end else begin
(
# 1516 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1517 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1518 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1519 "FStar.TypeChecker.Rel.fst"
let _68_1950 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1084 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1083 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _149_1082 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _149_1084 _149_1083 _149_1082))))
end else begin
()
end
in (
# 1522 "FStar.TypeChecker.Rel.fst"
let _68_1963 = (
# 1523 "FStar.TypeChecker.Rel.fst"
let _68_1955 = (FStar_Syntax_Util.type_u ())
in (match (_68_1955) with
| (t, _68_1954) -> begin
(
# 1524 "FStar.TypeChecker.Rel.fst"
let _68_1959 = (new_uvar r zs t)
in (match (_68_1959) with
| (k, _68_1958) -> begin
(new_uvar r zs k)
end))
end))
in (match (_68_1963) with
| (u_zs, _68_1962) -> begin
(
# 1526 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs xs u_zs)
in (
# 1527 "FStar.TypeChecker.Rel.fst"
let _68_1967 = (occurs_check env wl (u1, k1) sub1)
in (match (_68_1967) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1530 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1532 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1534 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs ys u_zs)
in (
# 1535 "FStar.TypeChecker.Rel.fst"
let _68_1973 = (occurs_check env wl (u2, k2) sub2)
in (match (_68_1973) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1538 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1539 "FStar.TypeChecker.Rel.fst"
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
# 1542 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _68_1981 _68_1986 -> (match ((_68_1981, _68_1986)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1544 "FStar.TypeChecker.Rel.fst"
let _68_1987 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1090 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1089 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _149_1090 _149_1089)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1547 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_1992 _68_1996 -> (match ((_68_1992, _68_1996)) with
| ((a, _68_1991), (t2, _68_1995)) -> begin
(let _149_1095 = (let _149_1093 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _149_1093 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _149_1095 (fun _149_1094 -> FStar_TypeChecker_Common.TProb (_149_1094))))
end)) xs args2)
in (
# 1550 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1097 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1097))
in (
# 1551 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1554 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1555 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1556 "FStar.TypeChecker.Rel.fst"
let _68_2006 = (occurs_check env wl (u1, k1) t2)
in (match (_68_2006) with
| (occurs_ok, _68_2005) -> begin
(
# 1557 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1560 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1099 = (let _149_1098 = (u_abs xs t2)
in ((u1, k1), _149_1098))
in TERM (_149_1099))
in (
# 1561 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1564 "FStar.TypeChecker.Rel.fst"
let _68_2017 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_68_2017) with
| (sol, (_68_2012, u2, k2, ys)) -> begin
(
# 1565 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1566 "FStar.TypeChecker.Rel.fst"
let _68_2019 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1100 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _149_1100))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2024 -> begin
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
# 1574 "FStar.TypeChecker.Rel.fst"
let _68_2029 = lhs
in (match (_68_2029) with
| (t1, u1, k1, args1) -> begin
(
# 1575 "FStar.TypeChecker.Rel.fst"
let _68_2034 = rhs
in (match (_68_2034) with
| (t2, u2, k2, args2) -> begin
(
# 1576 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1577 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1578 "FStar.TypeChecker.Rel.fst"
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
| _68_2052 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1587 "FStar.TypeChecker.Rel.fst"
let _68_2056 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_68_2056) with
| (sol, _68_2055) -> begin
(
# 1588 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1589 "FStar.TypeChecker.Rel.fst"
let _68_2058 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1101 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _149_1101))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2063 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1596 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _149_1102 = (solve_prob orig None [] wl)
in (solve env _149_1102))
end else begin
(
# 1598 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1599 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _149_1103 = (solve_prob orig None [] wl)
in (solve env _149_1103))
end else begin
(
# 1601 "FStar.TypeChecker.Rel.fst"
let _68_2067 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1104 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _149_1104))
end else begin
()
end
in (
# 1604 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1606 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _68_2072 _68_2075 -> (match ((_68_2072, _68_2075)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1608 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1609 "FStar.TypeChecker.Rel.fst"
let _68_2082 = (FStar_Util.first_N n bs)
in (match (_68_2082) with
| (bs, rest) -> begin
(let _149_1134 = (mk_cod rest)
in (bs, _149_1134))
end)))
in (
# 1612 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1613 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _149_1138 = (let _149_1135 = (mk_cod1 [])
in (bs1, _149_1135))
in (let _149_1137 = (let _149_1136 = (mk_cod2 [])
in (bs2, _149_1136))
in (_149_1138, _149_1137)))
end else begin
if (l1 > l2) then begin
(let _149_1141 = (curry l2 bs1 mk_cod1)
in (let _149_1140 = (let _149_1139 = (mk_cod2 [])
in (bs2, _149_1139))
in (_149_1141, _149_1140)))
end else begin
(let _149_1144 = (let _149_1142 = (mk_cod1 [])
in (bs1, _149_1142))
in (let _149_1143 = (curry l1 bs2 mk_cod2)
in (_149_1144, _149_1143)))
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
# 1631 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _68_24 -> (match (_68_24) with
| [] -> begin
c
end
| bs -> begin
(let _149_1149 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _149_1149))
end))
in (
# 1635 "FStar.TypeChecker.Rel.fst"
let _68_2125 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_68_2125) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1640 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1641 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1642 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _149_1156 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _149_1155 -> FStar_TypeChecker_Common.CProb (_149_1155)) _149_1156)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _68_2135), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _68_2141)) -> begin
(
# 1646 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _68_25 -> (match (_68_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1649 "FStar.TypeChecker.Rel.fst"
let _68_2156 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_68_2156) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _149_1169 = (let _149_1168 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _149_1167 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _149_1168 problem.FStar_TypeChecker_Common.relation _149_1167 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _149_1166 -> FStar_TypeChecker_Common.TProb (_149_1166)) _149_1169))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2161), FStar_Syntax_Syntax.Tm_refine (_68_2164)) -> begin
(
# 1658 "FStar.TypeChecker.Rel.fst"
let _68_2169 = (as_refinement env wl t1)
in (match (_68_2169) with
| (x1, phi1) -> begin
(
# 1659 "FStar.TypeChecker.Rel.fst"
let _68_2172 = (as_refinement env wl t2)
in (match (_68_2172) with
| (x2, phi2) -> begin
(
# 1660 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1171 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _149_1170 -> FStar_TypeChecker_Common.TProb (_149_1170)) _149_1171))
in (
# 1661 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1662 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1663 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1664 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1665 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1666 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _149_1188 = (imp phi1 phi2)
in (FStar_All.pipe_right _149_1188 (guard_on_element problem x1))))
in (
# 1667 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _68_2184 -> (match (()) with
| () -> begin
(
# 1668 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1672 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1191 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1191 impl))
in (
# 1673 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1676 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _149_1195 = (let _149_1194 = (let _149_1193 = (FStar_Syntax_Syntax.mk_binder x1)
in (_149_1193)::(p_scope orig))
in (mk_problem _149_1194 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _149_1192 -> FStar_TypeChecker_Common.TProb (_149_1192)) _149_1195))
in (match ((solve env (
# 1677 "FStar.TypeChecker.Rel.fst"
let _68_2189 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _68_2189.ctr; defer_ok = false; smt_ok = _68_2189.smt_ok; tcenv = _68_2189.tcenv}))) with
| Failed (_68_2192) -> begin
(fallback ())
end
| Success (_68_2195) -> begin
(
# 1680 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1198 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _149_1197 = (let _149_1196 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _149_1196 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _149_1198 _149_1197)))
in (
# 1681 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1682 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1682 "FStar.TypeChecker.Rel.fst"
let _68_2199 = wl
in {attempting = _68_2199.attempting; wl_deferred = _68_2199.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _68_2199.defer_ok; smt_ok = _68_2199.smt_ok; tcenv = _68_2199.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _149_1200 = (destruct_flex_t t1)
in (let _149_1199 = (destruct_flex_t t2)
in (flex_flex orig _149_1200 _149_1199)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _149_1201 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _149_1201 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1710 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _149_1202 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _149_1202)) then begin
(let _149_1205 = (FStar_All.pipe_left (fun _149_1203 -> FStar_TypeChecker_Common.TProb (_149_1203)) (
# 1712 "FStar.TypeChecker.Rel.fst"
let _68_2344 = problem
in {FStar_TypeChecker_Common.pid = _68_2344.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2344.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2344.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2344.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2344.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2344.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2344.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2344.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2344.FStar_TypeChecker_Common.rank}))
in (let _149_1204 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1205 _149_1204 t2 wl)))
end else begin
(
# 1713 "FStar.TypeChecker.Rel.fst"
let _68_2348 = (base_and_refinement env wl t2)
in (match (_68_2348) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _149_1208 = (FStar_All.pipe_left (fun _149_1206 -> FStar_TypeChecker_Common.TProb (_149_1206)) (
# 1716 "FStar.TypeChecker.Rel.fst"
let _68_2350 = problem
in {FStar_TypeChecker_Common.pid = _68_2350.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2350.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2350.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2350.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2350.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2350.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2350.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2350.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2350.FStar_TypeChecker_Common.rank}))
in (let _149_1207 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1208 _149_1207 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1719 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1719 "FStar.TypeChecker.Rel.fst"
let _68_2356 = y
in {FStar_Syntax_Syntax.ppname = _68_2356.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_2356.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1720 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1721 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1210 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _149_1209 -> FStar_TypeChecker_Common.TProb (_149_1209)) _149_1210))
in (
# 1723 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1211 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1211 impl))
in (
# 1724 "FStar.TypeChecker.Rel.fst"
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
# 1733 "FStar.TypeChecker.Rel.fst"
let _68_2389 = (base_and_refinement env wl t1)
in (match (_68_2389) with
| (t_base, _68_2388) -> begin
(solve_t env (
# 1734 "FStar.TypeChecker.Rel.fst"
let _68_2390 = problem
in {FStar_TypeChecker_Common.pid = _68_2390.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _68_2390.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2390.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2390.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2390.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2390.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2390.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2390.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2393), _68_2396) -> begin
(
# 1737 "FStar.TypeChecker.Rel.fst"
let t2 = (let _149_1212 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _149_1212))
in (solve_t env (
# 1738 "FStar.TypeChecker.Rel.fst"
let _68_2399 = problem
in {FStar_TypeChecker_Common.pid = _68_2399.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2399.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2399.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2399.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2399.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2399.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2399.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2399.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2399.FStar_TypeChecker_Common.rank}) wl))
end
| (_68_2402, FStar_Syntax_Syntax.Tm_refine (_68_2404)) -> begin
(
# 1741 "FStar.TypeChecker.Rel.fst"
let t1 = (let _149_1213 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _149_1213))
in (solve_t env (
# 1742 "FStar.TypeChecker.Rel.fst"
let _68_2408 = problem
in {FStar_TypeChecker_Common.pid = _68_2408.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2408.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2408.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2408.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2408.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2408.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2408.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2408.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2408.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1746 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_68_2425) -> begin
t
end
| _68_2428 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _149_1218 = (
# 1749 "FStar.TypeChecker.Rel.fst"
let _68_2429 = problem
in (let _149_1217 = (maybe_eta t1)
in (let _149_1216 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _68_2429.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1217; FStar_TypeChecker_Common.relation = _68_2429.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1216; FStar_TypeChecker_Common.element = _68_2429.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2429.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2429.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2429.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2429.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2429.FStar_TypeChecker_Common.rank})))
in (solve_t env _149_1218 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1761 "FStar.TypeChecker.Rel.fst"
let head1 = (let _149_1219 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _149_1219 Prims.fst))
in (
# 1762 "FStar.TypeChecker.Rel.fst"
let head2 = (let _149_1220 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1220 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1767 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1768 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1770 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _149_1222 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _149_1221 -> Some (_149_1221)) _149_1222))
end
in (let _149_1223 = (solve_prob orig guard [] wl)
in (solve env _149_1223)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _68_2498, _68_2500), _68_2504) -> begin
(solve_t' env (
# 1778 "FStar.TypeChecker.Rel.fst"
let _68_2506 = problem
in {FStar_TypeChecker_Common.pid = _68_2506.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2506.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2506.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2506.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2506.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2506.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2506.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2506.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2506.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_2509, FStar_Syntax_Syntax.Tm_ascribed (t2, _68_2512, _68_2514)) -> begin
(solve_t' env (
# 1781 "FStar.TypeChecker.Rel.fst"
let _68_2518 = problem
in {FStar_TypeChecker_Common.pid = _68_2518.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2518.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2518.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2518.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2518.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2518.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2518.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2518.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2518.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _149_1226 = (let _149_1225 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_1224 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _149_1225 _149_1224)))
in (FStar_All.failwith _149_1226))
end
| _68_2557 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1793 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1794 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1795 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1796 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1798 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1799 "FStar.TypeChecker.Rel.fst"
let _68_2574 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1801 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_2579 _68_2583 -> (match ((_68_2579, _68_2583)) with
| ((a1, _68_2578), (a2, _68_2582)) -> begin
(let _149_1241 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _149_1240 -> FStar_TypeChecker_Common.TProb (_149_1240)) _149_1241))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1804 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1243 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1243))
in (
# 1805 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _149_1244 = (solve_prob orig None [] wl)
in (solve env _149_1244))
end else begin
(
# 1809 "FStar.TypeChecker.Rel.fst"
let _68_2588 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1246 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1245 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _149_1246 (rel_to_string problem.FStar_TypeChecker_Common.relation) _149_1245)))
end else begin
()
end
in (
# 1814 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1815 "FStar.TypeChecker.Rel.fst"
let _68_2593 = (c1, c2)
in (match (_68_2593) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_68_2595), FStar_Syntax_Syntax.Total (_68_2598)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _149_1247 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _149_1247 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _149_1249 = (
# 1827 "FStar.TypeChecker.Rel.fst"
let _68_2626 = problem
in (let _149_1248 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _68_2626.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1248; FStar_TypeChecker_Common.relation = _68_2626.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2626.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2626.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2626.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2626.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2626.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2626.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2626.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1249 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _149_1251 = (
# 1831 "FStar.TypeChecker.Rel.fst"
let _68_2642 = problem
in (let _149_1250 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _68_2642.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2642.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2642.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1250; FStar_TypeChecker_Common.element = _68_2642.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2642.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2642.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2642.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2642.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2642.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1251 wl))
end
| (FStar_Syntax_Syntax.Comp (_68_2645), FStar_Syntax_Syntax.Comp (_68_2648)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _149_1252 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _149_1252 wl))
end else begin
(
# 1837 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1838 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 1842 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 1843 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 1844 "FStar.TypeChecker.Rel.fst"
let _68_2655 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _149_1255 = (let _149_1254 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1253 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _149_1254 _149_1253)))
in (giveup env _149_1255 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1851 "FStar.TypeChecker.Rel.fst"
let _68_2673 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _68_2666)::(wlp1, _68_2662)::[] -> begin
(wp1, wlp1)
end
| _68_2670 -> begin
(let _149_1257 = (let _149_1256 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _149_1256))
in (FStar_All.failwith _149_1257))
end)
in (match (_68_2673) with
| (wp, wlp) -> begin
(
# 1854 "FStar.TypeChecker.Rel.fst"
let c1 = (let _149_1263 = (let _149_1262 = (let _149_1258 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _149_1258))
in (let _149_1261 = (let _149_1260 = (let _149_1259 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _149_1259))
in (_149_1260)::[])
in (_149_1262)::_149_1261))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _149_1263; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 1861 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _68_26 -> (match (_68_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _68_2680 -> begin
false
end))))
in (
# 1862 "FStar.TypeChecker.Rel.fst"
let _68_2701 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _68_2686)::_68_2683, (wp2, _68_2693)::_68_2690) -> begin
(wp1, wp2)
end
| _68_2698 -> begin
(let _149_1267 = (let _149_1266 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1265 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _149_1266 _149_1265)))
in (FStar_All.failwith _149_1267))
end)
in (match (_68_2701) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _149_1268 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _149_1268 wl))
end else begin
(
# 1869 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 1870 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 1872 "FStar.TypeChecker.Rel.fst"
let _68_2703 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _149_1278 = (let _149_1277 = (let _149_1276 = (let _149_1270 = (let _149_1269 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_149_1269)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1270 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _149_1275 = (let _149_1274 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _149_1273 = (let _149_1272 = (let _149_1271 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1271))
in (_149_1272)::[])
in (_149_1274)::_149_1273))
in (_149_1276, _149_1275)))
in FStar_Syntax_Syntax.Tm_app (_149_1277))
in (FStar_Syntax_Syntax.mk _149_1278 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 1876 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _149_1293 = (let _149_1292 = (let _149_1291 = (let _149_1280 = (let _149_1279 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1279)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1280 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _149_1290 = (let _149_1289 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1288 = (let _149_1287 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _149_1286 = (let _149_1285 = (let _149_1281 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid r)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1281))
in (let _149_1284 = (let _149_1283 = (let _149_1282 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1282))
in (_149_1283)::[])
in (_149_1285)::_149_1284))
in (_149_1287)::_149_1286))
in (_149_1289)::_149_1288))
in (_149_1291, _149_1290)))
in FStar_Syntax_Syntax.Tm_app (_149_1292))
in (FStar_Syntax_Syntax.mk _149_1293 None r))
in (let _149_1302 = (let _149_1301 = (let _149_1300 = (let _149_1295 = (let _149_1294 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1294)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1295 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _149_1299 = (let _149_1298 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1297 = (let _149_1296 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_149_1296)::[])
in (_149_1298)::_149_1297))
in (_149_1300, _149_1299)))
in FStar_Syntax_Syntax.Tm_app (_149_1301))
in (FStar_Syntax_Syntax.mk _149_1302 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 1883 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1304 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _149_1303 -> FStar_TypeChecker_Common.TProb (_149_1303)) _149_1304))
in (
# 1884 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_1308 = (let _149_1307 = (let _149_1306 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1306 g))
in (FStar_All.pipe_left (fun _149_1305 -> Some (_149_1305)) _149_1307))
in (solve_prob orig _149_1308 [] wl))
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

# 1886 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _149_1312 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _68_2719 -> (match (_68_2719) with
| (_68_2711, u, _68_2714, _68_2716, _68_2718) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_1312 (FStar_String.concat ", "))))

# 1891 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _68_2726 -> begin
(
# 1897 "FStar.TypeChecker.Rel.fst"
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
# 1904 "FStar.TypeChecker.Rel.fst"
let carry = (let _149_1318 = (FStar_List.map (fun _68_2734 -> (match (_68_2734) with
| (_68_2732, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _149_1318 (FStar_String.concat ",\n")))
in (
# 1905 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1906 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1911 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1913 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_2743; FStar_TypeChecker_Env.implicits = _68_2741} -> begin
true
end
| _68_2748 -> begin
false
end))

# 1917 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 1919 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 1925 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _68_2766 -> begin
(FStar_All.failwith "impossible")
end)
in (let _149_1334 = (
# 1928 "FStar.TypeChecker.Rel.fst"
let _68_2768 = g
in (let _149_1333 = (let _149_1332 = (let _149_1331 = (let _149_1330 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_1330)::[])
in (u_abs _149_1331 f))
in (FStar_All.pipe_left (fun _149_1329 -> FStar_TypeChecker_Common.NonTrivial (_149_1329)) _149_1332))
in {FStar_TypeChecker_Env.guard_f = _149_1333; FStar_TypeChecker_Env.deferred = _68_2768.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2768.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2768.FStar_TypeChecker_Env.implicits}))
in Some (_149_1334)))
end))

# 1928 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1932 "FStar.TypeChecker.Rel.fst"
let _68_2775 = g
in (let _149_1345 = (let _149_1344 = (let _149_1343 = (let _149_1342 = (let _149_1341 = (let _149_1340 = (FStar_Syntax_Syntax.as_arg e)
in (_149_1340)::[])
in (f, _149_1341))
in FStar_Syntax_Syntax.Tm_app (_149_1342))
in (FStar_Syntax_Syntax.mk _149_1343 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _149_1339 -> FStar_TypeChecker_Common.NonTrivial (_149_1339)) _149_1344))
in {FStar_TypeChecker_Env.guard_f = _149_1345; FStar_TypeChecker_Env.deferred = _68_2775.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2775.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2775.FStar_TypeChecker_Env.implicits}))
end))

# 1932 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_68_2780) -> begin
(FStar_All.failwith "impossible")
end))

# 1936 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _149_1352 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_149_1352))
end))

# 1941 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _68_2797) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2801 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 1945 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 1951 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 1951 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _149_1375 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _149_1375; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 1956 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 1957 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 1958 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1962 "FStar.TypeChecker.Rel.fst"
let _68_2828 = g
in (let _149_1390 = (let _149_1389 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _149_1389 (fun _149_1388 -> FStar_TypeChecker_Common.NonTrivial (_149_1388))))
in {FStar_TypeChecker_Env.guard_f = _149_1390; FStar_TypeChecker_Env.deferred = _68_2828.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2828.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2828.FStar_TypeChecker_Env.implicits}))
end))

# 1962 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 1968 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1398 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _149_1397 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _149_1398 (rel_to_string rel) _149_1397)))
end else begin
"TOP"
end
in (
# 1973 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 1974 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 1977 "FStar.TypeChecker.Rel.fst"
let x = (let _149_1409 = (let _149_1408 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _149_1407 -> Some (_149_1407)) _149_1408))
in (FStar_Syntax_Syntax.new_bv _149_1409 t1))
in (
# 1978 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 1979 "FStar.TypeChecker.Rel.fst"
let p = (let _149_1413 = (let _149_1411 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _149_1410 -> Some (_149_1410)) _149_1411))
in (let _149_1412 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _149_1413 _149_1412)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 1980 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 1983 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 1983 "FStar.TypeChecker.Rel.fst"
let _68_2848 = probs
in {attempting = _68_2848.attempting; wl_deferred = _68_2848.wl_deferred; ctr = _68_2848.ctr; defer_ok = false; smt_ok = _68_2848.smt_ok; tcenv = _68_2848.tcenv})
end else begin
probs
end
in (
# 1984 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 1985 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 1988 "FStar.TypeChecker.Rel.fst"
let _68_2855 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 1991 "FStar.TypeChecker.Rel.fst"
let _68_2861 = (FStar_Unionfind.rollback tx)
in (
# 1992 "FStar.TypeChecker.Rel.fst"
let _68_2863 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1425 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _149_1425))
end else begin
()
end
in (err (d, s))))
end)))))

# 1994 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1999 "FStar.TypeChecker.Rel.fst"
let _68_2870 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1430 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _149_1430))
end else begin
()
end
in (
# 2000 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2001 "FStar.TypeChecker.Rel.fst"
let _68_2873 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1431 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _149_1431))
end else begin
()
end
in (
# 2002 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _149_1432 = (FStar_Syntax_Util.unmeta f)
in _149_1432.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _68_2877) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2881 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2005 "FStar.TypeChecker.Rel.fst"
let _68_2883 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _68_2883.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2883.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2883.FStar_TypeChecker_Env.implicits})))))
end))

# 2005 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _149_1444 = (let _149_1443 = (let _149_1442 = (let _149_1441 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _149_1441 (fun _149_1440 -> FStar_TypeChecker_Common.NonTrivial (_149_1440))))
in {FStar_TypeChecker_Env.guard_f = _149_1442; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _149_1443))
in (FStar_All.pipe_left (fun _149_1439 -> Some (_149_1439)) _149_1444))
end))

# 2010 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2013 "FStar.TypeChecker.Rel.fst"
let _68_2894 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1452 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1451 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _149_1452 _149_1451)))
end else begin
()
end
in (
# 2015 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1455 = (let _149_1454 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _149_1454))
in (FStar_All.pipe_left (fun _149_1453 -> FStar_TypeChecker_Common.TProb (_149_1453)) _149_1455))
in (
# 2016 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1457 = (solve_and_commit env (singleton env prob) (fun _68_2897 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1457))
in g))))

# 2017 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _149_1467 = (let _149_1466 = (let _149_1465 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1464 = (FStar_TypeChecker_Env.get_range env)
in (_149_1465, _149_1464)))
in FStar_Syntax_Syntax.Error (_149_1466))
in (Prims.raise _149_1467))
end
| Some (g) -> begin
(
# 2023 "FStar.TypeChecker.Rel.fst"
let _68_2906 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1470 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1469 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_1468 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _149_1470 _149_1469 _149_1468))))
end else begin
()
end
in g)
end))

# 2028 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2031 "FStar.TypeChecker.Rel.fst"
let _68_2911 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1478 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1477 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _149_1478 _149_1477)))
end else begin
()
end
in (
# 2033 "FStar.TypeChecker.Rel.fst"
let _68_2915 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_68_2915) with
| (prob, x) -> begin
(
# 2034 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1480 = (solve_and_commit env (singleton env prob) (fun _68_2916 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1480))
in (
# 2035 "FStar.TypeChecker.Rel.fst"
let _68_2919 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _149_1484 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1483 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _149_1482 = (let _149_1481 = (FStar_Util.must g)
in (guard_to_string env _149_1481))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _149_1484 _149_1483 _149_1482))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2041 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _149_1491 = (let _149_1490 = (let _149_1489 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1488 = (FStar_TypeChecker_Env.get_range env)
in (_149_1489, _149_1488)))
in FStar_Syntax_Syntax.Error (_149_1490))
in (Prims.raise _149_1491)))

# 2044 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2048 "FStar.TypeChecker.Rel.fst"
let _68_2927 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1499 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1498 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _149_1499 _149_1498)))
end else begin
()
end
in (
# 2050 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2051 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1502 = (let _149_1501 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _149_1501 "sub_comp"))
in (FStar_All.pipe_left (fun _149_1500 -> FStar_TypeChecker_Common.CProb (_149_1500)) _149_1502))
in (let _149_1504 = (solve_and_commit env (singleton env prob) (fun _68_2931 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1504))))))

# 2052 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2056 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2057 "FStar.TypeChecker.Rel.fst"
let _68_2940 = (FStar_Unionfind.rollback tx)
in (
# 2058 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _149_1522 = (let _149_1521 = (let _149_1520 = (let _149_1518 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_1517 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _149_1518 _149_1517 msg)))
in (let _149_1519 = (FStar_TypeChecker_Env.get_range env)
in (_149_1520, _149_1519)))
in FStar_Syntax_Syntax.Error (_149_1521))
in (Prims.raise _149_1522)))))
in (
# 2067 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2070 "FStar.TypeChecker.Rel.fst"
let _68_2956 = hd
in (match (_68_2956) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _149_1529 = (insert uv u1 tl)
in (hd)::_149_1529)
end
end))
end))
in (
# 2075 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2078 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2081 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _149_1534 = (insert uv u1 out)
in (group_by _149_1534 rest))
end)
end
| _68_2971 -> begin
None
end))
end))
in (
# 2088 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _68_2973 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _68_2976 -> begin
(
# 2093 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2093 "FStar.TypeChecker.Rel.fst"
let _68_2977 = (empty_worklist env)
in {attempting = _68_2977.attempting; wl_deferred = _68_2977.wl_deferred; ctr = _68_2977.ctr; defer_ok = true; smt_ok = _68_2977.smt_ok; tcenv = _68_2977.tcenv})
in (
# 2094 "FStar.TypeChecker.Rel.fst"
let _68_3017 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _68_2982 -> (match (_68_2982) with
| (u1, u2) -> begin
(
# 2095 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2096 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _68_2987 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2102 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _68_2997 -> begin
(u1)::[]
end)
in (
# 2105 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _68_3002 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _68_27 -> (match (_68_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2111 "FStar.TypeChecker.Rel.fst"
let _68_3009 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_3009) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2113 "FStar.TypeChecker.Rel.fst"
let _68_3013 = (FStar_Syntax_Util.univ_kernel u')
in (match (_68_3013) with
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
| USolved (_68_3015) -> begin
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
# 2124 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2124 "FStar.TypeChecker.Rel.fst"
let _68_3021 = (empty_worklist env)
in {attempting = _68_3021.attempting; wl_deferred = _68_3021.wl_deferred; ctr = _68_3021.ctr; defer_ok = false; smt_ok = _68_3021.smt_ok; tcenv = _68_3021.tcenv})
in (
# 2125 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _68_3036 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2135 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2138 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2139 "FStar.TypeChecker.Rel.fst"
let _68_3041 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2140 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2143 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_3048 -> (match (_68_3048) with
| (d, s) -> begin
(
# 2144 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2146 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2147 "FStar.TypeChecker.Rel.fst"
let _68_3051 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1555 = (wl_to_string wl)
in (let _149_1554 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _149_1555 _149_1554)))
end else begin
()
end
in (
# 2149 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2150 "FStar.TypeChecker.Rel.fst"
let _68_3055 = g
in {FStar_TypeChecker_Env.guard_f = _68_3055.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_3055.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3055.FStar_TypeChecker_Env.implicits})
end
| _68_3058 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2152 "FStar.TypeChecker.Rel.fst"
let _68_3060 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2153 "FStar.TypeChecker.Rel.fst"
let _68_3062 = g
in {FStar_TypeChecker_Env.guard_f = _68_3062.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3062.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _68_3062.FStar_TypeChecker_Env.implicits})))))))

# 2153 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2156 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2157 "FStar.TypeChecker.Rel.fst"
let _68_3076 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2161 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2165 "FStar.TypeChecker.Rel.fst"
let _68_3074 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1562 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1561 = (let _149_1560 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _149_1560))
in (FStar_TypeChecker_Errors.diag _149_1562 _149_1561)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (
# 2170 "FStar.TypeChecker.Rel.fst"
let _68_3078 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_3078.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3078.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3078.FStar_TypeChecker_Env.implicits}))))

# 2170 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2173 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _68_3085 -> begin
false
end))
in (
# 2176 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _68_3089 implicits -> (match (_68_3089) with
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
# 2180 "FStar.TypeChecker.Rel.fst"
let _68_3100 = hd
in (match (_68_3100) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2183 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2184 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2185 "FStar.TypeChecker.Rel.fst"
let _68_3103 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1573 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_1572 = (FStar_Syntax_Print.term_to_string tm)
in (let _149_1571 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _149_1573 _149_1572 _149_1571))))
end else begin
()
end
in (
# 2188 "FStar.TypeChecker.Rel.fst"
let _68_3110 = (env.FStar_TypeChecker_Env.type_of (
# 2188 "FStar.TypeChecker.Rel.fst"
let _68_3105 = env
in {FStar_TypeChecker_Env.solver = _68_3105.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3105.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3105.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3105.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3105.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3105.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3105.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3105.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3105.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3105.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3105.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3105.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3105.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_3105.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_3105.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3105.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3105.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3105.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_3105.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3105.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3105.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_68_3110) with
| (_68_3108, g) -> begin
(
# 2189 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl))
end)))))
end
end))
end)
end))
in (
# 2191 "FStar.TypeChecker.Rel.fst"
let _68_3112 = g
in (let _149_1574 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _68_3112.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3112.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3112.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _149_1574})))))

# 2191 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2194 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1579 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _149_1579 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _149_1580 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _149_1580))
end
| (_68_3121, _68_3123, _68_3125, _68_3127, r)::_68_3119 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2197 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2201 "FStar.TypeChecker.Rel.fst"
let _68_3133 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_3133.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3133.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _68_3133.FStar_TypeChecker_Env.implicits}))





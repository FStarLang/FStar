
open Prims
# 65 "FStar.TypeChecker.Rel.fst"
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
| TERM (_68_44) -> begin
_68_44
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_68_47) -> begin
_68_47
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
| Success (_68_57) -> begin
_68_57
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_68_60) -> begin
_68_60
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

# 122 "FStar.TypeChecker.Rel.fst"
let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

# 124 "FStar.TypeChecker.Rel.fst"
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

# 140 "FStar.TypeChecker.Rel.fst"
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

# 148 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _149_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _149_124 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _149_134 = (let _149_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _149_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _149_134 (FStar_String.concat ", "))))

# 150 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _149_137 = (FStar_All.pipe_right args (FStar_List.map (fun _68_97 -> (match (_68_97) with
| (x, _68_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _149_137 (FStar_String.concat " "))))

# 159 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 167 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _68_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _68_101.wl_deferred; ctr = _68_101.ctr; defer_ok = _68_101.defer_ok; smt_ok = _68_101.smt_ok; tcenv = _68_101.tcenv}))

# 168 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _68_105 = (empty_worklist env)
in (let _149_146 = (FStar_List.map Prims.snd g)
in {attempting = _149_146; wl_deferred = _68_105.wl_deferred; ctr = _68_105.ctr; defer_ok = false; smt_ok = _68_105.smt_ok; tcenv = _68_105.tcenv})))

# 169 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _68_110 = wl
in {attempting = _68_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _68_110.ctr; defer_ok = _68_110.defer_ok; smt_ok = _68_110.smt_ok; tcenv = _68_110.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _68_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _68_114.wl_deferred; ctr = _68_114.ctr; defer_ok = _68_114.defer_ok; smt_ok = _68_114.smt_ok; tcenv = _68_114.tcenv}))

# 172 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _68_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _149_163))
end else begin
()
end
in Failed ((prob, reason))))

# 183 "FStar.TypeChecker.Rel.fst"
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

# 187 "FStar.TypeChecker.Rel.fst"
let invert = (fun p -> (
# 187 "FStar.TypeChecker.Rel.fst"
let _68_126 = p
in {FStar_TypeChecker_Common.pid = _68_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _68_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_126.FStar_TypeChecker_Common.rank}))

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 189 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _68_5 -> (match (_68_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_170 -> FStar_TypeChecker_Common.TProb (_149_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _149_171 -> FStar_TypeChecker_Common.CProb (_149_171)))
end))

# 192 "FStar.TypeChecker.Rel.fst"
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

# 196 "FStar.TypeChecker.Rel.fst"
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _68_7 -> (match (_68_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 199 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _68_8 -> (match (_68_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 202 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _68_9 -> (match (_68_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 205 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _68_10 -> (match (_68_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 208 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _68_11 -> (match (_68_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 211 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _68_12 -> (match (_68_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 214 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _68_13 -> (match (_68_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _149_190 -> FStar_TypeChecker_Common.TProb (_149_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _149_191 -> FStar_TypeChecker_Common.CProb (_149_191)) (invert p))
end))

# 217 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 218 "FStar.TypeChecker.Rel.fst"
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

# 222 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _149_204 = (next_pid ())
in (let _149_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _149_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 234 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _149_214 = (next_pid ())
in (let _149_213 = (let _149_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _149_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _149_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _149_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 248 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _149_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _149_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 260 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 264 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _149_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _149_232 = (prob_to_string env d)
in (let _149_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _149_233 _149_232 _149_231 s)))))

# 278 "FStar.TypeChecker.Rel.fst"
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

# 286 "FStar.TypeChecker.Rel.fst"
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

# 290 "FStar.TypeChecker.Rel.fst"
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

# 302 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_252 = (let _149_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _149_251))
in (FStar_Syntax_Subst.compress _149_252)))

# 303 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _149_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _149_257)))

# 304 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _149_260 = (sn env (Prims.fst t))
in (_149_260, (Prims.snd t))))

# 305 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _68_258 -> (match (_68_258) with
| (x, imp) -> begin
(let _149_267 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _68_259 = x
in (let _149_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_266}))
in (_149_267, imp))
end)))))

# 312 "FStar.TypeChecker.Rel.fst"
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

# 367 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _149_300 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _149_300 Prims.fst)))

# 369 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _149_303 = (FStar_Syntax_Syntax.null_bv t)
in (_149_303, FStar_Syntax_Util.t_true)))

# 371 "FStar.TypeChecker.Rel.fst"
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

# 377 "FStar.TypeChecker.Rel.fst"
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

# 391 "FStar.TypeChecker.Rel.fst"
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

# 406 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _149_325 = (let _149_324 = (let _149_323 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _68_387 -> (match (_68_387) with
| (_68_383, _68_385, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _149_323))
in (FStar_List.map (wl_prob_to_string wl) _149_324))
in (FStar_All.pipe_right _149_325 (FStar_String.concat "\n\t"))))

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

# 438 "FStar.TypeChecker.Rel.fst"
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

# 444 "FStar.TypeChecker.Rel.fst"
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

# 461 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _149_380 = (let _149_378 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _149_378 FStar_Util.set_elements))
in (FStar_All.pipe_right _149_380 (FStar_Util.for_some (fun _68_459 -> (match (_68_459) with
| (uv, _68_458) -> begin
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
(let _149_387 = (let _149_386 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _149_385 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _149_386 _149_385)))
in Some (_149_387))
end
in (occurs_ok, msg))))

# 476 "FStar.TypeChecker.Rel.fst"
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

# 481 "FStar.TypeChecker.Rel.fst"
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

# 498 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _68_498 _68_502 -> (match ((_68_498, _68_502)) with
| ((a, _68_497), (b, _68_501)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 502 "FStar.TypeChecker.Rel.fst"
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

# 520 "FStar.TypeChecker.Rel.fst"
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

# 525 "FStar.TypeChecker.Rel.fst"
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
| MisMatch (_68_561) -> begin
_68_561
end))

# 605 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _68_18 -> (match (_68_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _68_568 -> begin
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _68_654), FStar_Syntax_Syntax.Tm_uinst (g, _68_659)) -> begin
(let _149_480 = (head_matches env f g)
in (FStar_All.pipe_right _149_480 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _68_670), FStar_Syntax_Syntax.Tm_uvar (uv', _68_675)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_681), FStar_Syntax_Syntax.Tm_refine (y, _68_686)) -> begin
(let _149_481 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_481 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_692), _68_696) -> begin
(let _149_482 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _149_482 head_match))
end
| (_68_699, FStar_Syntax_Syntax.Tm_refine (x, _68_702)) -> begin
(let _149_483 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_483 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_722), FStar_Syntax_Syntax.Tm_app (head', _68_727)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_733), _68_737) -> begin
(head_matches env head t2)
end
| (_68_740, FStar_Syntax_Syntax.Tm_app (head, _68_743)) -> begin
(head_matches env t1 head)
end
| _68_748 -> begin
(let _149_486 = (let _149_485 = (delta_depth_of_term env t1)
in (let _149_484 = (delta_depth_of_term env t2)
in (_149_485, _149_484)))
in MisMatch (_149_486))
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
let _68_799 = if d1_greater_than_d2 then begin
(
# 687 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 689 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _149_507 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _149_507)))
end
in (match (_68_799) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_68_801) -> begin
(fail r)
end
| _68_804 -> begin
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
| T (_68_807) -> begin
_68_807
end))

# 700 "FStar.TypeChecker.Rel.fst"
let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_68_810) -> begin
_68_810
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
| MisMatch (_68_817) -> begin
false
end
| _68_820 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 710 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 711 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_68_830, imp), T (t)) -> begin
(t, imp)
end
| _68_837 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 716 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _68_842 -> (match (_68_842) with
| (t, _68_841) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 722 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_849 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 723 "FStar.TypeChecker.Rel.fst"
let _68_852 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_852) with
| (bs, c) -> begin
(
# 725 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 726 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 727 "FStar.TypeChecker.Rel.fst"
let _68_869 = x
in {FStar_Syntax_Syntax.ppname = _68_869.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_869.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _68_877 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 732 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _68_19 -> (match (_68_19) with
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
in (let _149_589 = (decompose [] bs)
in (rebuild, matches, _149_589))))
end)))
end
| _68_887 -> begin
(
# 743 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _68_20 -> (match (_68_20) with
| [] -> begin
t
end
| _68_891 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 749 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _68_21 -> (match (_68_21) with
| T (t) -> begin
t
end
| _68_898 -> begin
(FStar_All.failwith "Impossible")
end))

# 753 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _68_22 -> (match (_68_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _68_903 -> begin
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
| (_68_916, variance, T (ti)) -> begin
(
# 767 "FStar.TypeChecker.Rel.fst"
let k = (
# 768 "FStar.TypeChecker.Rel.fst"
let _68_924 = (FStar_Syntax_Util.type_u ())
in (match (_68_924) with
| (t, _68_923) -> begin
(let _149_611 = (new_uvar r scope t)
in (Prims.fst _149_611))
end))
in (
# 770 "FStar.TypeChecker.Rel.fst"
let _68_928 = (new_uvar r scope k)
in (match (_68_928) with
| (gi_xs, gi) -> begin
(
# 771 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _68_931 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _149_614 = (let _149_613 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _149_612 -> FStar_TypeChecker_Common.TProb (_149_612)) _149_613))
in (T (gi_xs), _149_614)))
end)))
end
| (_68_934, _68_936, C (_68_938)) -> begin
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
let _68_1016 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _68_956; FStar_Syntax_Syntax.pos = _68_954; FStar_Syntax_Syntax.vars = _68_952})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_623 = (let _149_622 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _149_621 -> C (_149_621)) _149_622))
in (_149_623, (prob)::[]))
end
| _68_967 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _68_975; FStar_Syntax_Syntax.pos = _68_973; FStar_Syntax_Syntax.vars = _68_971})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_626 = (let _149_625 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _149_624 -> C (_149_624)) _149_625))
in (_149_626, (prob)::[]))
end
| _68_986 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_68_988, _68_990, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _68_996; FStar_Syntax_Syntax.pos = _68_994; FStar_Syntax_Syntax.vars = _68_992})) -> begin
(
# 797 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 798 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 799 "FStar.TypeChecker.Rel.fst"
let _68_1007 = (let _149_628 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _149_628 FStar_List.unzip))
in (match (_68_1007) with
| (tcs, sub_probs) -> begin
(
# 800 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _149_633 = (let _149_632 = (let _149_629 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _149_629 un_T))
in (let _149_631 = (let _149_630 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _149_630 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _149_632; FStar_Syntax_Syntax.effect_args = _149_631; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_633))
in (C (gi_xs), sub_probs))
end))))
end
| _68_1010 -> begin
(
# 809 "FStar.TypeChecker.Rel.fst"
let _68_1013 = (sub_prob scope args q)
in (match (_68_1013) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_68_1016) with
| (tc, probs) -> begin
(
# 812 "FStar.TypeChecker.Rel.fst"
let _68_1029 = (match (q) with
| (Some (b), _68_1020, _68_1022) -> begin
(let _149_635 = (let _149_634 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_149_634)::args)
in (Some (b), (b)::scope, _149_635))
end
| _68_1025 -> begin
(None, scope, args)
end)
in (match (_68_1029) with
| (bopt, scope, args) -> begin
(
# 816 "FStar.TypeChecker.Rel.fst"
let _68_1033 = (aux scope args qs)
in (match (_68_1033) with
| (sub_probs, tcs, f) -> begin
(
# 817 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _149_638 = (let _149_637 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_149_637)
in (FStar_Syntax_Util.mk_conj_l _149_638))
end
| Some (b) -> begin
(let _149_642 = (let _149_641 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _149_640 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_149_641)::_149_640))
in (FStar_Syntax_Util.mk_conj_l _149_642))
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _68_1061), FStar_Syntax_Syntax.Tm_uvar (u2, _68_1066)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _68_1080 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _68_1086 _68_1090 -> (match ((_68_1086, _68_1090)) with
| ((a1, _68_1085), (a2, _68_1089)) -> begin
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
let _68_1093 = p
in (let _149_664 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_663 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _68_1093.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_664; FStar_TypeChecker_Common.relation = _68_1093.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_663; FStar_TypeChecker_Common.element = _68_1093.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1093.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1093.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1093.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1093.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1093.FStar_TypeChecker_Common.rank}))))

# 864 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_670 = (compress_tprob wl p)
in (FStar_All.pipe_right _149_670 (fun _149_669 -> FStar_TypeChecker_Common.TProb (_149_669))))
end
| FStar_TypeChecker_Common.CProb (_68_1100) -> begin
p
end))

# 869 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 872 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_675 = (compress_prob wl pr)
in (FStar_All.pipe_right _149_675 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 875 "FStar.TypeChecker.Rel.fst"
let _68_1110 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1110) with
| (lh, _68_1109) -> begin
(
# 876 "FStar.TypeChecker.Rel.fst"
let _68_1114 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_68_1114) with
| (rh, _68_1113) -> begin
(
# 877 "FStar.TypeChecker.Rel.fst"
let _68_1170 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_68_1116), FStar_Syntax_Syntax.Tm_uvar (_68_1119)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_68_1135), _68_1138) -> begin
(
# 884 "FStar.TypeChecker.Rel.fst"
let _68_1142 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_68_1142) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _68_1145 -> begin
(
# 888 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _149_677 = (
# 892 "FStar.TypeChecker.Rel.fst"
let _68_1147 = tp
in (let _149_676 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1147.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1147.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1147.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_676; FStar_TypeChecker_Common.element = _68_1147.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1147.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1147.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1147.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1147.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1147.FStar_TypeChecker_Common.rank}))
in (rank, _149_677)))
end)
end))
end
| (_68_1150, FStar_Syntax_Syntax.Tm_uvar (_68_1152)) -> begin
(
# 896 "FStar.TypeChecker.Rel.fst"
let _68_1157 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1157) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _68_1160 -> begin
(let _149_679 = (
# 899 "FStar.TypeChecker.Rel.fst"
let _68_1161 = tp
in (let _149_678 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1161.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_678; FStar_TypeChecker_Common.relation = _68_1161.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1161.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1161.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1161.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1161.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1161.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1161.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1161.FStar_TypeChecker_Common.rank}))
in (refine_flex, _149_679))
end)
end))
end
| (_68_1164, _68_1166) -> begin
(rigid_rigid, tp)
end)
in (match (_68_1170) with
| (rank, tp) -> begin
(let _149_681 = (FStar_All.pipe_right (
# 904 "FStar.TypeChecker.Rel.fst"
let _68_1171 = tp
in {FStar_TypeChecker_Common.pid = _68_1171.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1171.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1171.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1171.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1171.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1171.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1171.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1171.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1171.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _149_680 -> FStar_TypeChecker_Common.TProb (_149_680)))
in (rank, _149_681))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _149_683 = (FStar_All.pipe_right (
# 906 "FStar.TypeChecker.Rel.fst"
let _68_1175 = cp
in {FStar_TypeChecker_Common.pid = _68_1175.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1175.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1175.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1175.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1175.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1175.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1175.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1175.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1175.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _149_682 -> FStar_TypeChecker_Common.CProb (_149_682)))
in (rigid_rigid, _149_683))
end)))

# 908 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 912 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _68_1182 probs -> (match (_68_1182) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 915 "FStar.TypeChecker.Rel.fst"
let _68_1190 = (rank wl hd)
in (match (_68_1190) with
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
| UDeferred (_68_1200) -> begin
_68_1200
end))

# 932 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_68_1203) -> begin
_68_1203
end))

# 933 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_68_1206) -> begin
_68_1206
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
let _68_1222 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_1222) with
| (k, _68_1221) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _68_1226 -> begin
false
end)
end)))))
end
| _68_1228 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 947 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_68_1234), FStar_Syntax_Syntax.U_max (_68_1237)) -> begin
(let _149_755 = (let _149_754 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_753 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _149_754 _149_753)))
in UFailed (_149_755))
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
| _68_1257 -> begin
(let _149_762 = (let _149_761 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_760 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _149_761 _149_760 msg)))
in UFailed (_149_762))
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
(let _149_765 = (let _149_764 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _149_763 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _149_764 _149_763)))
in (try_umax_components u1 u2 _149_765))
end else begin
(let _149_766 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_149_766))
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
let _68_1352 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_809 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _149_809))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1024 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1024 "FStar.TypeChecker.Rel.fst"
let _68_1359 = probs
in {attempting = tl; wl_deferred = _68_1359.wl_deferred; ctr = _68_1359.ctr; defer_ok = _68_1359.defer_ok; smt_ok = _68_1359.smt_ok; tcenv = _68_1359.tcenv})
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
| (None, _68_1371, _68_1373) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _68_1377 -> begin
(
# 1046 "FStar.TypeChecker.Rel.fst"
let _68_1386 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _68_1383 -> (match (_68_1383) with
| (c, _68_1380, _68_1382) -> begin
(c < probs.ctr)
end))))
in (match (_68_1386) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _149_812 = (FStar_List.map (fun _68_1392 -> (match (_68_1392) with
| (_68_1389, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_149_812))
end
| _68_1394 -> begin
(let _149_815 = (
# 1052 "FStar.TypeChecker.Rel.fst"
let _68_1395 = probs
in (let _149_814 = (FStar_All.pipe_right attempt (FStar_List.map (fun _68_1402 -> (match (_68_1402) with
| (_68_1398, _68_1400, y) -> begin
y
end))))
in {attempting = _149_814; wl_deferred = rest; ctr = _68_1395.ctr; defer_ok = _68_1395.defer_ok; smt_ok = _68_1395.smt_ok; tcenv = _68_1395.tcenv}))
in (solve env _149_815))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _149_821 = (solve_prob orig None [] wl)
in (solve env _149_821))
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
| _68_1437 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _149_836 = (let _149_833 = (whnf env t1)
in _149_833.FStar_Syntax_Syntax.n)
in (let _149_835 = (let _149_834 = (whnf env t2)
in _149_834.FStar_Syntax_Syntax.n)
in (_149_836, _149_835)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _68_1443; FStar_Syntax_Syntax.pos = _68_1441; FStar_Syntax_Syntax.vars = _68_1439}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _68_1455; FStar_Syntax_Syntax.pos = _68_1453; FStar_Syntax_Syntax.vars = _68_1451}, us2)) -> begin
(
# 1081 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1082 "FStar.TypeChecker.Rel.fst"
let _68_1464 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _68_1479 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1095 "FStar.TypeChecker.Rel.fst"
let _68_1484 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_841 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _149_841 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1105 "FStar.TypeChecker.Rel.fst"
let _68_1489 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_845 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _149_845))
end else begin
()
end
in (
# 1107 "FStar.TypeChecker.Rel.fst"
let _68_1493 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1493) with
| (u, args) -> begin
(
# 1108 "FStar.TypeChecker.Rel.fst"
let _68_1499 = (0, 1, 2, 3, 4)
in (match (_68_1499) with
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
let _68_1508 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1508) with
| (h1, args1) -> begin
(
# 1113 "FStar.TypeChecker.Rel.fst"
let _68_1512 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1512) with
| (h2, _68_1511) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _149_857 = (let _149_856 = (let _149_855 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _149_854 -> FStar_TypeChecker_Common.TProb (_149_854)) _149_855))
in (_149_856)::[])
in Some (_149_857))
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
| _68_1524 -> begin
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
in (let _149_864 = (let _149_863 = (let _149_862 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _149_862))
in (_149_863, m))
in Some (_149_864))))))
end))
end
| (_68_1546, FStar_Syntax_Syntax.Tm_refine (y, _68_1549)) -> begin
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
| (FStar_Syntax_Syntax.Tm_refine (x, _68_1559), _68_1563) -> begin
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
| _68_1570 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _68_1578) -> begin
(
# 1167 "FStar.TypeChecker.Rel.fst"
let _68_1603 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _68_23 -> (match (_68_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1171 "FStar.TypeChecker.Rel.fst"
let _68_1589 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1589) with
| (u', _68_1588) -> begin
(match ((let _149_866 = (whnf env u')
in _149_866.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _68_1592) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _68_1596 -> begin
false
end)
end))
end
| _68_1598 -> begin
false
end)
end
| _68_1600 -> begin
false
end))))
in (match (_68_1603) with
| (upper_bounds, rest) -> begin
(
# 1180 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _68_1607 tps -> (match (_68_1607) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _149_871 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _149_871))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _68_1620 -> begin
None
end)
end))
in (match ((let _149_873 = (let _149_872 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_149_872, []))
in (make_upper_bound _149_873 upper_bounds))) with
| None -> begin
(
# 1191 "FStar.TypeChecker.Rel.fst"
let _68_1622 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
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
let _68_1632 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1206 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1206 "FStar.TypeChecker.Rel.fst"
let _68_1629 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _68_1629.wl_deferred; ctr = _68_1629.ctr; defer_ok = _68_1629.defer_ok; smt_ok = _68_1629.smt_ok; tcenv = _68_1629.tcenv})
in (let _149_874 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _149_874)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1208 "FStar.TypeChecker.Rel.fst"
let _68_1634 = wl
in {attempting = sub_probs; wl_deferred = _68_1634.wl_deferred; ctr = _68_1634.ctr; defer_ok = _68_1634.defer_ok; smt_ok = _68_1634.smt_ok; tcenv = _68_1634.tcenv}))) with
| Success (_68_1637) -> begin
(
# 1210 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1210 "FStar.TypeChecker.Rel.fst"
let _68_1639 = wl
in {attempting = rest; wl_deferred = _68_1639.wl_deferred; ctr = _68_1639.ctr; defer_ok = _68_1639.defer_ok; smt_ok = _68_1639.smt_ok; tcenv = _68_1639.tcenv})
in (
# 1211 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1212 "FStar.TypeChecker.Rel.fst"
let _68_1645 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _68_1648 -> begin
None
end)))
end))
end))
end
| _68_1650 -> begin
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
let _68_1667 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_902 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _149_902))
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
let _68_1681 = hd1
in (let _149_903 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1681.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1681.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_903}))
in (
# 1233 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1233 "FStar.TypeChecker.Rel.fst"
let _68_1684 = hd2
in (let _149_904 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1684.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1684.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_904}))
in (
# 1234 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_907 = (let _149_906 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _149_906 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _149_905 -> FStar_TypeChecker_Common.TProb (_149_905)) _149_907))
in (
# 1235 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1236 "FStar.TypeChecker.Rel.fst"
let subst = (let _149_908 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_149_908)
in (
# 1237 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1240 "FStar.TypeChecker.Rel.fst"
let phi = (let _149_910 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _149_909 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _149_910 _149_909)))
in (
# 1241 "FStar.TypeChecker.Rel.fst"
let _68_1696 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_912 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_911 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _149_912 _149_911)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _68_1700 -> begin
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
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _149_916 = (compress_tprob wl problem)
in (solve_t' env _149_916 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1261 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1264 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1265 "FStar.TypeChecker.Rel.fst"
let _68_1728 = (head_matches_delta env wl t1 t2)
in (match (_68_1728) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_68_1730), _68_1733) -> begin
(
# 1268 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_68_1738) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _68_1743 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1273 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1276 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1280 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _149_945 = (let _149_944 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _149_944 t2))
in (FStar_Syntax_Util.mk_forall x _149_945)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _149_946 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _149_946)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_68_1753, Some (t1, t2)) -> begin
(solve_t env (
# 1289 "FStar.TypeChecker.Rel.fst"
let _68_1759 = problem
in {FStar_TypeChecker_Common.pid = _68_1759.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_1759.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_1759.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1759.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1759.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1759.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1759.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1759.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_1762, None) -> begin
(
# 1292 "FStar.TypeChecker.Rel.fst"
let _68_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_950 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_949 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_948 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_947 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _149_950 _149_949 _149_948 _149_947)))))
end else begin
()
end
in (
# 1296 "FStar.TypeChecker.Rel.fst"
let _68_1769 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1769) with
| (head, args) -> begin
(
# 1297 "FStar.TypeChecker.Rel.fst"
let _68_1772 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1772) with
| (head', args') -> begin
(
# 1298 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _149_955 = (let _149_954 = (FStar_Syntax_Print.term_to_string head)
in (let _149_953 = (args_to_string args)
in (let _149_952 = (FStar_Syntax_Print.term_to_string head')
in (let _149_951 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _149_954 _149_953 _149_952 _149_951)))))
in (giveup env _149_955 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _149_956 = (solve_prob orig None [] wl)
in (solve env _149_956))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1319 "FStar.TypeChecker.Rel.fst"
let _68_1782 = (base_and_refinement env wl t1)
in (match (_68_1782) with
| (base1, refinement1) -> begin
(
# 1320 "FStar.TypeChecker.Rel.fst"
let _68_1785 = (base_and_refinement env wl t2)
in (match (_68_1785) with
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
# 1327 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _68_1798 _68_1802 -> (match ((_68_1798, _68_1802)) with
| ((a, _68_1797), (a', _68_1801)) -> begin
(let _149_960 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _149_959 -> FStar_TypeChecker_Common.TProb (_149_959)) _149_960))
end)) args args')
in (
# 1328 "FStar.TypeChecker.Rel.fst"
let formula = (let _149_962 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _149_962))
in (
# 1329 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _68_1808 -> begin
(
# 1334 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1335 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1336 "FStar.TypeChecker.Rel.fst"
let _68_1811 = problem
in {FStar_TypeChecker_Common.pid = _68_1811.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _68_1811.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _68_1811.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1811.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1811.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1811.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1811.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1811.FStar_TypeChecker_Common.rank}) wl)))
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
# 1342 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1343 "FStar.TypeChecker.Rel.fst"
let _68_1828 = p
in (match (_68_1828) with
| ((u, k), ps, xs, (h, _68_1825, qs)) -> begin
(
# 1344 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1349 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1350 "FStar.TypeChecker.Rel.fst"
let _68_1834 = (imitation_sub_probs orig env xs ps qs)
in (match (_68_1834) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1351 "FStar.TypeChecker.Rel.fst"
let im = (let _149_973 = (h gs_xs)
in (u_abs xs _149_973))
in (
# 1352 "FStar.TypeChecker.Rel.fst"
let _68_1836 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_978 = (FStar_Syntax_Print.term_to_string im)
in (let _149_977 = (FStar_Syntax_Print.tag_of_term im)
in (let _149_976 = (let _149_974 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _149_974 (FStar_String.concat ", ")))
in (let _149_975 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _149_978 _149_977 _149_976 _149_975)))))
end else begin
()
end
in (
# 1357 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1362 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1363 "FStar.TypeChecker.Rel.fst"
let _68_1852 = p
in (match (_68_1852) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1367 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1368 "FStar.TypeChecker.Rel.fst"
let _68_1857 = (FStar_List.nth ps i)
in (match (_68_1857) with
| (pi, _68_1856) -> begin
(
# 1369 "FStar.TypeChecker.Rel.fst"
let _68_1861 = (FStar_List.nth xs i)
in (match (_68_1861) with
| (xi, _68_1860) -> begin
(
# 1371 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1372 "FStar.TypeChecker.Rel.fst"
let _68_1866 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1866) with
| (bs, k) -> begin
(
# 1373 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _68_1874)::tl -> begin
(
# 1376 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1377 "FStar.TypeChecker.Rel.fst"
let _68_1880 = (new_uvar r xs k_a)
in (match (_68_1880) with
| (gi_xs, gi) -> begin
(
# 1378 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1379 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1380 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1381 "FStar.TypeChecker.Rel.fst"
let _68_1886 = (aux subst tl)
in (match (_68_1886) with
| (gi_xs', gi_ps') -> begin
(let _149_1000 = (let _149_997 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_149_997)::gi_xs')
in (let _149_999 = (let _149_998 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_149_998)::gi_ps')
in (_149_1000, _149_999)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _149_1001 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _149_1001)) then begin
None
end else begin
(
# 1387 "FStar.TypeChecker.Rel.fst"
let _68_1890 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_68_1890) with
| (g_xs, _68_1889) -> begin
(
# 1388 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1389 "FStar.TypeChecker.Rel.fst"
let proj = (let _149_1002 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _149_1002))
in (
# 1390 "FStar.TypeChecker.Rel.fst"
let sub = (let _149_1008 = (let _149_1007 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _149_1006 = (let _149_1005 = (FStar_List.map (fun _68_1898 -> (match (_68_1898) with
| (_68_1894, _68_1896, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _149_1005))
in (mk_problem (p_scope orig) orig _149_1007 (p_rel orig) _149_1006 None "projection")))
in (FStar_All.pipe_left (fun _149_1003 -> FStar_TypeChecker_Common.TProb (_149_1003)) _149_1008))
in (
# 1391 "FStar.TypeChecker.Rel.fst"
let _68_1900 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1010 = (FStar_Syntax_Print.term_to_string proj)
in (let _149_1009 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _149_1010 _149_1009)))
end else begin
()
end
in (
# 1392 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_1012 = (let _149_1011 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_149_1011))
in (solve_prob orig _149_1012 ((TERM ((u, proj)))::[]) wl))
in (let _149_1014 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _149_1013 -> Some (_149_1013)) _149_1014)))))))
end))
end)
end))
end)))
end)))
in (
# 1397 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1398 "FStar.TypeChecker.Rel.fst"
let _68_1914 = lhs
in (match (_68_1914) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1399 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1400 "FStar.TypeChecker.Rel.fst"
let xs = (let _149_1041 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _149_1041 Prims.fst))
in (let _149_1046 = (decompose env t2)
in ((uv, k), ps, xs, _149_1046))))
in (
# 1403 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1406 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_68_1924) -> begin
(
# 1410 "FStar.TypeChecker.Rel.fst"
let _68_1926 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1417 "FStar.TypeChecker.Rel.fst"
let _68_1934 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1421 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1422 "FStar.TypeChecker.Rel.fst"
let _68_1944 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1944) with
| (hd, _68_1943) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _68_1955 -> begin
(
# 1428 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1431 "FStar.TypeChecker.Rel.fst"
let _68_1957 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1057 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _149_1057))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1434 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1435 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _149_1061 = (let _149_1060 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1060 Prims.fst))
in (FStar_All.pipe_right _149_1061 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1442 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1443 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1444 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1445 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1446 "FStar.TypeChecker.Rel.fst"
let _68_1970 = (occurs_check env wl (uv, k) t2)
in (match (_68_1970) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _149_1063 = (let _149_1062 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _149_1062))
in (giveup_or_defer orig _149_1063))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _149_1064 = (subterms args_lhs)
in (imitate orig env wl _149_1064))
end else begin
(
# 1453 "FStar.TypeChecker.Rel.fst"
let _68_1971 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1067 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1066 = (names_to_string fvs1)
in (let _149_1065 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _149_1067 _149_1066 _149_1065))))
end else begin
()
end
in (
# 1458 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _68_1975 -> begin
(let _149_1068 = (sn_binders env vars)
in (u_abs _149_1068 t2))
end)
in (
# 1461 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1466 "FStar.TypeChecker.Rel.fst"
let _68_1978 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1071 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1070 = (names_to_string fvs1)
in (let _149_1069 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _149_1071 _149_1070 _149_1069))))
end else begin
()
end
in (let _149_1072 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1072 (- (1)))))
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
if (let _149_1073 = (FStar_Syntax_Free.names t1)
in (check_head _149_1073 t2)) then begin
(
# 1478 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1479 "FStar.TypeChecker.Rel.fst"
let _68_1982 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1074 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _149_1074 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _149_1075 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1075 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1504 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1507 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _68_1994 -> (match (_68_1994) with
| (t, u, k, args) -> begin
(
# 1510 "FStar.TypeChecker.Rel.fst"
let _68_1998 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1998) with
| (all_formals, _68_1997) -> begin
(
# 1511 "FStar.TypeChecker.Rel.fst"
let _68_1999 = ()
in (
# 1513 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1521 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _68_2012 -> (match (_68_2012) with
| (x, imp) -> begin
(let _149_1097 = (FStar_Syntax_Syntax.bv_to_name x)
in (_149_1097, imp))
end))))
in (
# 1522 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1523 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1524 "FStar.TypeChecker.Rel.fst"
let _68_2018 = (FStar_Syntax_Util.type_u ())
in (match (_68_2018) with
| (t, _68_2017) -> begin
(let _149_1098 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _149_1098))
end))
in (
# 1526 "FStar.TypeChecker.Rel.fst"
let _68_2022 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_68_2022) with
| (t', tm_u1) -> begin
(
# 1527 "FStar.TypeChecker.Rel.fst"
let _68_2029 = (destruct_flex_t t')
in (match (_68_2029) with
| (_68_2024, u1, k1, _68_2028) -> begin
(
# 1528 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1100 = (let _149_1099 = (u_abs all_formals t')
in ((u, k), _149_1099))
in TERM (_149_1100))
in (
# 1529 "FStar.TypeChecker.Rel.fst"
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
# 1538 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _68_2048 -> (match (_68_2048) with
| (x, _68_2047) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1545 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _149_1102 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _149_1102 formals tl))
end)
end)
end)
end
| _68_2052 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _149_1103 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _149_1103 all_formals args))))
end))
end))
in (
# 1557 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _68_2058 _68_2062 r -> (match ((_68_2058, _68_2062)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _149_1112 = (solve_prob orig None [] wl)
in (solve env _149_1112))
end else begin
(
# 1565 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1566 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1567 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1568 "FStar.TypeChecker.Rel.fst"
let _68_2067 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1115 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1114 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _149_1113 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _149_1115 _149_1114 _149_1113))))
end else begin
()
end
in (
# 1571 "FStar.TypeChecker.Rel.fst"
let _68_2080 = (
# 1572 "FStar.TypeChecker.Rel.fst"
let _68_2072 = (FStar_Syntax_Util.type_u ())
in (match (_68_2072) with
| (t, _68_2071) -> begin
(
# 1573 "FStar.TypeChecker.Rel.fst"
let _68_2076 = (new_uvar r zs t)
in (match (_68_2076) with
| (k, _68_2075) -> begin
(new_uvar r zs k)
end))
end))
in (match (_68_2080) with
| (u_zs, _68_2079) -> begin
(
# 1575 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs xs u_zs)
in (
# 1576 "FStar.TypeChecker.Rel.fst"
let _68_2084 = (occurs_check env wl (u1, k1) sub1)
in (match (_68_2084) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1579 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1581 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1583 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs ys u_zs)
in (
# 1584 "FStar.TypeChecker.Rel.fst"
let _68_2090 = (occurs_check env wl (u2, k2) sub2)
in (match (_68_2090) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1587 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1588 "FStar.TypeChecker.Rel.fst"
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
# 1591 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _68_2098 _68_2103 -> (match ((_68_2098, _68_2103)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1593 "FStar.TypeChecker.Rel.fst"
let _68_2104 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1121 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1120 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _149_1121 _149_1120)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1596 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_2109 _68_2113 -> (match ((_68_2109, _68_2113)) with
| ((a, _68_2108), (t2, _68_2112)) -> begin
(let _149_1126 = (let _149_1124 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _149_1124 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _149_1126 (fun _149_1125 -> FStar_TypeChecker_Common.TProb (_149_1125))))
end)) xs args2)
in (
# 1599 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1128 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1128))
in (
# 1600 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1603 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1604 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1605 "FStar.TypeChecker.Rel.fst"
let _68_2123 = (occurs_check env wl (u1, k1) t2)
in (match (_68_2123) with
| (occurs_ok, _68_2122) -> begin
(
# 1606 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1609 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1130 = (let _149_1129 = (u_abs xs t2)
in ((u1, k1), _149_1129))
in TERM (_149_1130))
in (
# 1610 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1613 "FStar.TypeChecker.Rel.fst"
let _68_2134 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_68_2134) with
| (sol, (_68_2129, u2, k2, ys)) -> begin
(
# 1614 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1615 "FStar.TypeChecker.Rel.fst"
let _68_2136 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1131 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _149_1131))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2141 -> begin
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
# 1623 "FStar.TypeChecker.Rel.fst"
let _68_2146 = lhs
in (match (_68_2146) with
| (t1, u1, k1, args1) -> begin
(
# 1624 "FStar.TypeChecker.Rel.fst"
let _68_2151 = rhs
in (match (_68_2151) with
| (t2, u2, k2, args2) -> begin
(
# 1625 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1626 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1627 "FStar.TypeChecker.Rel.fst"
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
| _68_2169 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1636 "FStar.TypeChecker.Rel.fst"
let _68_2173 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_68_2173) with
| (sol, _68_2172) -> begin
(
# 1637 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1638 "FStar.TypeChecker.Rel.fst"
let _68_2175 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1132 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _149_1132))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2180 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1645 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _149_1133 = (solve_prob orig None [] wl)
in (solve env _149_1133))
end else begin
(
# 1647 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1648 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _149_1134 = (solve_prob orig None [] wl)
in (solve env _149_1134))
end else begin
(
# 1650 "FStar.TypeChecker.Rel.fst"
let _68_2184 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1135 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _149_1135))
end else begin
()
end
in (
# 1653 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1655 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _68_2189 _68_2192 -> (match ((_68_2189, _68_2192)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1657 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1658 "FStar.TypeChecker.Rel.fst"
let _68_2199 = (FStar_Util.first_N n bs)
in (match (_68_2199) with
| (bs, rest) -> begin
(let _149_1165 = (mk_cod rest)
in (bs, _149_1165))
end)))
in (
# 1661 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1662 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _149_1169 = (let _149_1166 = (mk_cod1 [])
in (bs1, _149_1166))
in (let _149_1168 = (let _149_1167 = (mk_cod2 [])
in (bs2, _149_1167))
in (_149_1169, _149_1168)))
end else begin
if (l1 > l2) then begin
(let _149_1172 = (curry l2 bs1 mk_cod1)
in (let _149_1171 = (let _149_1170 = (mk_cod2 [])
in (bs2, _149_1170))
in (_149_1172, _149_1171)))
end else begin
(let _149_1175 = (let _149_1173 = (mk_cod1 [])
in (bs1, _149_1173))
in (let _149_1174 = (curry l1 bs2 mk_cod2)
in (_149_1175, _149_1174)))
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
# 1680 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _68_24 -> (match (_68_24) with
| [] -> begin
c
end
| bs -> begin
(let _149_1180 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _149_1180))
end))
in (
# 1684 "FStar.TypeChecker.Rel.fst"
let _68_2242 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_68_2242) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1689 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1690 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1691 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _149_1187 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _149_1186 -> FStar_TypeChecker_Common.CProb (_149_1186)) _149_1187)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _68_2252), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _68_2258)) -> begin
(
# 1695 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _68_25 -> (match (_68_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1698 "FStar.TypeChecker.Rel.fst"
let _68_2273 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_68_2273) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _149_1200 = (let _149_1199 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _149_1198 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _149_1199 problem.FStar_TypeChecker_Common.relation _149_1198 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _149_1197 -> FStar_TypeChecker_Common.TProb (_149_1197)) _149_1200))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2278), FStar_Syntax_Syntax.Tm_refine (_68_2281)) -> begin
(
# 1707 "FStar.TypeChecker.Rel.fst"
let _68_2286 = (as_refinement env wl t1)
in (match (_68_2286) with
| (x1, phi1) -> begin
(
# 1708 "FStar.TypeChecker.Rel.fst"
let _68_2289 = (as_refinement env wl t2)
in (match (_68_2289) with
| (x2, phi2) -> begin
(
# 1709 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1202 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _149_1201 -> FStar_TypeChecker_Common.TProb (_149_1201)) _149_1202))
in (
# 1710 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1711 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1712 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1713 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1714 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1715 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _149_1219 = (imp phi1 phi2)
in (FStar_All.pipe_right _149_1219 (guard_on_element problem x1))))
in (
# 1716 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _68_2301 -> (match (()) with
| () -> begin
(
# 1717 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1721 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1222 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1222 impl))
in (
# 1722 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1725 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _149_1226 = (let _149_1225 = (let _149_1224 = (FStar_Syntax_Syntax.mk_binder x1)
in (_149_1224)::(p_scope orig))
in (mk_problem _149_1225 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _149_1223 -> FStar_TypeChecker_Common.TProb (_149_1223)) _149_1226))
in (match ((solve env (
# 1726 "FStar.TypeChecker.Rel.fst"
let _68_2306 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _68_2306.ctr; defer_ok = false; smt_ok = _68_2306.smt_ok; tcenv = _68_2306.tcenv}))) with
| Failed (_68_2309) -> begin
(fallback ())
end
| Success (_68_2312) -> begin
(
# 1729 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1229 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _149_1228 = (let _149_1227 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _149_1227 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _149_1229 _149_1228)))
in (
# 1730 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1731 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1731 "FStar.TypeChecker.Rel.fst"
let _68_2316 = wl
in {attempting = _68_2316.attempting; wl_deferred = _68_2316.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _68_2316.defer_ok; smt_ok = _68_2316.smt_ok; tcenv = _68_2316.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _149_1231 = (destruct_flex_t t1)
in (let _149_1230 = (destruct_flex_t t2)
in (flex_flex orig _149_1231 _149_1230)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _149_1232 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _149_1232 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _149_1233 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _149_1233)) then begin
(let _149_1236 = (FStar_All.pipe_left (fun _149_1234 -> FStar_TypeChecker_Common.TProb (_149_1234)) (
# 1761 "FStar.TypeChecker.Rel.fst"
let _68_2461 = problem
in {FStar_TypeChecker_Common.pid = _68_2461.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2461.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2461.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2461.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2461.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2461.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2461.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2461.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2461.FStar_TypeChecker_Common.rank}))
in (let _149_1235 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1236 _149_1235 t2 wl)))
end else begin
(
# 1762 "FStar.TypeChecker.Rel.fst"
let _68_2465 = (base_and_refinement env wl t2)
in (match (_68_2465) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _149_1239 = (FStar_All.pipe_left (fun _149_1237 -> FStar_TypeChecker_Common.TProb (_149_1237)) (
# 1765 "FStar.TypeChecker.Rel.fst"
let _68_2467 = problem
in {FStar_TypeChecker_Common.pid = _68_2467.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2467.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2467.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2467.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2467.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2467.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2467.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2467.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2467.FStar_TypeChecker_Common.rank}))
in (let _149_1238 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1239 _149_1238 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1768 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1768 "FStar.TypeChecker.Rel.fst"
let _68_2473 = y
in {FStar_Syntax_Syntax.ppname = _68_2473.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_2473.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1769 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1770 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1241 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _149_1240 -> FStar_TypeChecker_Common.TProb (_149_1240)) _149_1241))
in (
# 1772 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1242 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1242 impl))
in (
# 1773 "FStar.TypeChecker.Rel.fst"
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
# 1782 "FStar.TypeChecker.Rel.fst"
let _68_2506 = (base_and_refinement env wl t1)
in (match (_68_2506) with
| (t_base, _68_2505) -> begin
(solve_t env (
# 1783 "FStar.TypeChecker.Rel.fst"
let _68_2507 = problem
in {FStar_TypeChecker_Common.pid = _68_2507.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _68_2507.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2507.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2507.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2507.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2507.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2507.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2507.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2510), _68_2513) -> begin
(
# 1786 "FStar.TypeChecker.Rel.fst"
let t2 = (let _149_1243 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _149_1243))
in (solve_t env (
# 1787 "FStar.TypeChecker.Rel.fst"
let _68_2516 = problem
in {FStar_TypeChecker_Common.pid = _68_2516.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2516.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2516.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2516.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2516.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2516.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2516.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2516.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2516.FStar_TypeChecker_Common.rank}) wl))
end
| (_68_2519, FStar_Syntax_Syntax.Tm_refine (_68_2521)) -> begin
(
# 1790 "FStar.TypeChecker.Rel.fst"
let t1 = (let _149_1244 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _149_1244))
in (solve_t env (
# 1791 "FStar.TypeChecker.Rel.fst"
let _68_2525 = problem
in {FStar_TypeChecker_Common.pid = _68_2525.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2525.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2525.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2525.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2525.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2525.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2525.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2525.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2525.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1795 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_68_2542) -> begin
t
end
| _68_2545 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _149_1249 = (
# 1798 "FStar.TypeChecker.Rel.fst"
let _68_2546 = problem
in (let _149_1248 = (maybe_eta t1)
in (let _149_1247 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _68_2546.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1248; FStar_TypeChecker_Common.relation = _68_2546.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1247; FStar_TypeChecker_Common.element = _68_2546.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2546.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2546.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2546.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2546.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2546.FStar_TypeChecker_Common.rank})))
in (solve_t env _149_1249 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1810 "FStar.TypeChecker.Rel.fst"
let head1 = (let _149_1250 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _149_1250 Prims.fst))
in (
# 1811 "FStar.TypeChecker.Rel.fst"
let head2 = (let _149_1251 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1251 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1816 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1817 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1819 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _149_1253 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _149_1252 -> Some (_149_1252)) _149_1253))
end
in (let _149_1254 = (solve_prob orig guard [] wl)
in (solve env _149_1254)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _68_2615, _68_2617), _68_2621) -> begin
(solve_t' env (
# 1827 "FStar.TypeChecker.Rel.fst"
let _68_2623 = problem
in {FStar_TypeChecker_Common.pid = _68_2623.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2623.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2623.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2623.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2623.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2623.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2623.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2623.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2623.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_2626, FStar_Syntax_Syntax.Tm_ascribed (t2, _68_2629, _68_2631)) -> begin
(solve_t' env (
# 1830 "FStar.TypeChecker.Rel.fst"
let _68_2635 = problem
in {FStar_TypeChecker_Common.pid = _68_2635.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2635.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2635.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2635.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2635.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2635.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2635.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2635.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2635.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _149_1257 = (let _149_1256 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_1255 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _149_1256 _149_1255)))
in (FStar_All.failwith _149_1257))
end
| _68_2674 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1842 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1843 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1844 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1845 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1847 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1848 "FStar.TypeChecker.Rel.fst"
let _68_2691 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1850 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_2696 _68_2700 -> (match ((_68_2696, _68_2700)) with
| ((a1, _68_2695), (a2, _68_2699)) -> begin
(let _149_1272 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _149_1271 -> FStar_TypeChecker_Common.TProb (_149_1271)) _149_1272))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1853 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1274 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1274))
in (
# 1854 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _149_1275 = (solve_prob orig None [] wl)
in (solve env _149_1275))
end else begin
(
# 1858 "FStar.TypeChecker.Rel.fst"
let _68_2705 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1277 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1276 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _149_1277 (rel_to_string problem.FStar_TypeChecker_Common.relation) _149_1276)))
end else begin
()
end
in (
# 1863 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1864 "FStar.TypeChecker.Rel.fst"
let _68_2710 = (c1, c2)
in (match (_68_2710) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_68_2712), FStar_Syntax_Syntax.Total (_68_2715)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _149_1278 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _149_1278 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _149_1280 = (
# 1876 "FStar.TypeChecker.Rel.fst"
let _68_2743 = problem
in (let _149_1279 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _68_2743.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1279; FStar_TypeChecker_Common.relation = _68_2743.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2743.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2743.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2743.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2743.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2743.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2743.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2743.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1280 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _149_1282 = (
# 1880 "FStar.TypeChecker.Rel.fst"
let _68_2759 = problem
in (let _149_1281 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _68_2759.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2759.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2759.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1281; FStar_TypeChecker_Common.element = _68_2759.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2759.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2759.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2759.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2759.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2759.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1282 wl))
end
| (FStar_Syntax_Syntax.Comp (_68_2762), FStar_Syntax_Syntax.Comp (_68_2765)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _149_1283 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _149_1283 wl))
end else begin
(
# 1886 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1887 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 1891 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 1892 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 1893 "FStar.TypeChecker.Rel.fst"
let _68_2772 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _149_1286 = (let _149_1285 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1284 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _149_1285 _149_1284)))
in (giveup env _149_1286 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1900 "FStar.TypeChecker.Rel.fst"
let _68_2790 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _68_2783)::(wlp1, _68_2779)::[] -> begin
(wp1, wlp1)
end
| _68_2787 -> begin
(let _149_1288 = (let _149_1287 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _149_1287))
in (FStar_All.failwith _149_1288))
end)
in (match (_68_2790) with
| (wp, wlp) -> begin
(
# 1903 "FStar.TypeChecker.Rel.fst"
let c1 = (let _149_1294 = (let _149_1293 = (let _149_1289 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _149_1289))
in (let _149_1292 = (let _149_1291 = (let _149_1290 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _149_1290))
in (_149_1291)::[])
in (_149_1293)::_149_1292))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _149_1294; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 1910 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _68_26 -> (match (_68_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _68_2797 -> begin
false
end))))
in (
# 1911 "FStar.TypeChecker.Rel.fst"
let _68_2818 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _68_2803)::_68_2800, (wp2, _68_2810)::_68_2807) -> begin
(wp1, wp2)
end
| _68_2815 -> begin
(let _149_1298 = (let _149_1297 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1296 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _149_1297 _149_1296)))
in (FStar_All.failwith _149_1298))
end)
in (match (_68_2818) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _149_1299 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _149_1299 wl))
end else begin
(
# 1918 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 1919 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 1921 "FStar.TypeChecker.Rel.fst"
let _68_2820 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _149_1309 = (let _149_1308 = (let _149_1307 = (let _149_1301 = (let _149_1300 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_149_1300)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1301 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _149_1306 = (let _149_1305 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _149_1304 = (let _149_1303 = (let _149_1302 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1302))
in (_149_1303)::[])
in (_149_1305)::_149_1304))
in (_149_1307, _149_1306)))
in FStar_Syntax_Syntax.Tm_app (_149_1308))
in (FStar_Syntax_Syntax.mk _149_1309 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 1925 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _149_1325 = (let _149_1324 = (let _149_1323 = (let _149_1311 = (let _149_1310 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1310)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1311 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _149_1322 = (let _149_1321 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1320 = (let _149_1319 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _149_1318 = (let _149_1317 = (let _149_1313 = (let _149_1312 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _149_1312 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1313))
in (let _149_1316 = (let _149_1315 = (let _149_1314 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1314))
in (_149_1315)::[])
in (_149_1317)::_149_1316))
in (_149_1319)::_149_1318))
in (_149_1321)::_149_1320))
in (_149_1323, _149_1322)))
in FStar_Syntax_Syntax.Tm_app (_149_1324))
in (FStar_Syntax_Syntax.mk _149_1325 None r))
in (let _149_1334 = (let _149_1333 = (let _149_1332 = (let _149_1327 = (let _149_1326 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1326)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1327 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _149_1331 = (let _149_1330 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1329 = (let _149_1328 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_149_1328)::[])
in (_149_1330)::_149_1329))
in (_149_1332, _149_1331)))
in FStar_Syntax_Syntax.Tm_app (_149_1333))
in (FStar_Syntax_Syntax.mk _149_1334 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 1932 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1336 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _149_1335 -> FStar_TypeChecker_Common.TProb (_149_1335)) _149_1336))
in (
# 1933 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_1340 = (let _149_1339 = (let _149_1338 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1338 g))
in (FStar_All.pipe_left (fun _149_1337 -> Some (_149_1337)) _149_1339))
in (solve_prob orig _149_1340 [] wl))
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

# 1940 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _149_1344 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _68_2836 -> (match (_68_2836) with
| (_68_2828, u, _68_2831, _68_2833, _68_2835) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_1344 (FStar_String.concat ", "))))

# 1942 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _68_2843 -> begin
(
# 1946 "FStar.TypeChecker.Rel.fst"
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
# 1953 "FStar.TypeChecker.Rel.fst"
let carry = (let _149_1350 = (FStar_List.map (fun _68_2851 -> (match (_68_2851) with
| (_68_2849, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _149_1350 (FStar_String.concat ",\n")))
in (
# 1954 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1960 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1962 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1964 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_2860; FStar_TypeChecker_Env.implicits = _68_2858} -> begin
true
end
| _68_2865 -> begin
false
end))

# 1968 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 1970 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 1974 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _68_2883 -> begin
(FStar_All.failwith "impossible")
end)
in (let _149_1366 = (
# 1977 "FStar.TypeChecker.Rel.fst"
let _68_2885 = g
in (let _149_1365 = (let _149_1364 = (let _149_1363 = (let _149_1362 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_1362)::[])
in (u_abs _149_1363 f))
in (FStar_All.pipe_left (fun _149_1361 -> FStar_TypeChecker_Common.NonTrivial (_149_1361)) _149_1364))
in {FStar_TypeChecker_Env.guard_f = _149_1365; FStar_TypeChecker_Env.deferred = _68_2885.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2885.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2885.FStar_TypeChecker_Env.implicits}))
in Some (_149_1366)))
end))

# 1979 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1981 "FStar.TypeChecker.Rel.fst"
let _68_2892 = g
in (let _149_1377 = (let _149_1376 = (let _149_1375 = (let _149_1374 = (let _149_1373 = (let _149_1372 = (FStar_Syntax_Syntax.as_arg e)
in (_149_1372)::[])
in (f, _149_1373))
in FStar_Syntax_Syntax.Tm_app (_149_1374))
in (FStar_Syntax_Syntax.mk _149_1375 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _149_1371 -> FStar_TypeChecker_Common.NonTrivial (_149_1371)) _149_1376))
in {FStar_TypeChecker_Env.guard_f = _149_1377; FStar_TypeChecker_Env.deferred = _68_2892.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2892.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2892.FStar_TypeChecker_Env.implicits}))
end))

# 1983 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_68_2897) -> begin
(FStar_All.failwith "impossible")
end))

# 1987 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _149_1384 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_149_1384))
end))

# 1992 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2915 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 1996 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2000 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2002 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _149_1407 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _149_1407; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2006 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2007 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2009 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2011 "FStar.TypeChecker.Rel.fst"
let _68_2942 = g
in (let _149_1422 = (let _149_1421 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _149_1421 (fun _149_1420 -> FStar_TypeChecker_Common.NonTrivial (_149_1420))))
in {FStar_TypeChecker_Env.guard_f = _149_1422; FStar_TypeChecker_Env.deferred = _68_2942.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2942.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2942.FStar_TypeChecker_Env.implicits}))
end))

# 2016 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2017 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1430 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _149_1429 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _149_1430 (rel_to_string rel) _149_1429)))
end else begin
"TOP"
end
in (
# 2022 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2025 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2026 "FStar.TypeChecker.Rel.fst"
let x = (let _149_1441 = (let _149_1440 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _149_1439 -> Some (_149_1439)) _149_1440))
in (FStar_Syntax_Syntax.new_bv _149_1441 t1))
in (
# 2027 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2028 "FStar.TypeChecker.Rel.fst"
let p = (let _149_1445 = (let _149_1443 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _149_1442 -> Some (_149_1442)) _149_1443))
in (let _149_1444 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _149_1445 _149_1444)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2031 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2032 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2032 "FStar.TypeChecker.Rel.fst"
let _68_2962 = probs
in {attempting = _68_2962.attempting; wl_deferred = _68_2962.wl_deferred; ctr = _68_2962.ctr; defer_ok = false; smt_ok = _68_2962.smt_ok; tcenv = _68_2962.tcenv})
end else begin
probs
end
in (
# 2033 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2034 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2037 "FStar.TypeChecker.Rel.fst"
let _68_2969 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2040 "FStar.TypeChecker.Rel.fst"
let _68_2975 = (FStar_Unionfind.rollback tx)
in (
# 2041 "FStar.TypeChecker.Rel.fst"
let _68_2977 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1457 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _149_1457))
end else begin
()
end
in (err (d, s))))
end)))))

# 2045 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2048 "FStar.TypeChecker.Rel.fst"
let _68_2984 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1462 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _149_1462))
end else begin
()
end
in (
# 2049 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2050 "FStar.TypeChecker.Rel.fst"
let _68_2987 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1463 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _149_1463))
end else begin
()
end
in (
# 2051 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _149_1464 = (FStar_Syntax_Util.unmeta f)
in _149_1464.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2992 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2054 "FStar.TypeChecker.Rel.fst"
let _68_2994 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _68_2994.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2994.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2994.FStar_TypeChecker_Env.implicits})))))
end))

# 2056 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _149_1476 = (let _149_1475 = (let _149_1474 = (let _149_1473 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _149_1473 (fun _149_1472 -> FStar_TypeChecker_Common.NonTrivial (_149_1472))))
in {FStar_TypeChecker_Env.guard_f = _149_1474; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _149_1475))
in (FStar_All.pipe_left (fun _149_1471 -> Some (_149_1471)) _149_1476))
end))

# 2061 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2062 "FStar.TypeChecker.Rel.fst"
let _68_3005 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1484 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1483 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _149_1484 _149_1483)))
end else begin
()
end
in (
# 2064 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1487 = (let _149_1486 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _149_1486))
in (FStar_All.pipe_left (fun _149_1485 -> FStar_TypeChecker_Common.TProb (_149_1485)) _149_1487))
in (
# 2065 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1489 = (solve_and_commit env (singleton env prob) (fun _68_3008 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1489))
in g))))

# 2068 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _149_1499 = (let _149_1498 = (let _149_1497 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1496 = (FStar_TypeChecker_Env.get_range env)
in (_149_1497, _149_1496)))
in FStar_Syntax_Syntax.Error (_149_1498))
in (Prims.raise _149_1499))
end
| Some (g) -> begin
(
# 2072 "FStar.TypeChecker.Rel.fst"
let _68_3017 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1502 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1501 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_1500 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _149_1502 _149_1501 _149_1500))))
end else begin
()
end
in g)
end))

# 2079 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2080 "FStar.TypeChecker.Rel.fst"
let _68_3022 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1510 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1509 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _149_1510 _149_1509)))
end else begin
()
end
in (
# 2082 "FStar.TypeChecker.Rel.fst"
let _68_3026 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_68_3026) with
| (prob, x) -> begin
(
# 2083 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1512 = (solve_and_commit env (singleton env prob) (fun _68_3027 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1512))
in (
# 2084 "FStar.TypeChecker.Rel.fst"
let _68_3030 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _149_1516 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1515 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _149_1514 = (let _149_1513 = (FStar_Util.must g)
in (guard_to_string env _149_1513))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _149_1516 _149_1515 _149_1514))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2092 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _149_1523 = (let _149_1522 = (let _149_1521 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1520 = (FStar_TypeChecker_Env.get_range env)
in (_149_1521, _149_1520)))
in FStar_Syntax_Syntax.Error (_149_1522))
in (Prims.raise _149_1523)))

# 2096 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2097 "FStar.TypeChecker.Rel.fst"
let _68_3038 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1531 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1530 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _149_1531 _149_1530)))
end else begin
()
end
in (
# 2099 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2100 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1534 = (let _149_1533 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _149_1533 "sub_comp"))
in (FStar_All.pipe_left (fun _149_1532 -> FStar_TypeChecker_Common.CProb (_149_1532)) _149_1534))
in (let _149_1536 = (solve_and_commit env (singleton env prob) (fun _68_3042 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1536))))))

# 2104 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2105 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2106 "FStar.TypeChecker.Rel.fst"
let _68_3051 = (FStar_Unionfind.rollback tx)
in (
# 2107 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _149_1554 = (let _149_1553 = (let _149_1552 = (let _149_1550 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_1549 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _149_1550 _149_1549 msg)))
in (let _149_1551 = (FStar_TypeChecker_Env.get_range env)
in (_149_1552, _149_1551)))
in FStar_Syntax_Syntax.Error (_149_1553))
in (Prims.raise _149_1554)))))
in (
# 2116 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2119 "FStar.TypeChecker.Rel.fst"
let _68_3067 = hd
in (match (_68_3067) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _149_1561 = (insert uv u1 tl)
in (hd)::_149_1561)
end
end))
end))
in (
# 2124 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2127 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2130 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _149_1566 = (insert uv u1 out)
in (group_by _149_1566 rest))
end)
end
| _68_3082 -> begin
None
end))
end))
in (
# 2137 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _68_3084 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _68_3087 -> begin
(
# 2142 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2142 "FStar.TypeChecker.Rel.fst"
let _68_3088 = (empty_worklist env)
in {attempting = _68_3088.attempting; wl_deferred = _68_3088.wl_deferred; ctr = _68_3088.ctr; defer_ok = true; smt_ok = _68_3088.smt_ok; tcenv = _68_3088.tcenv})
in (
# 2143 "FStar.TypeChecker.Rel.fst"
let _68_3128 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _68_3093 -> (match (_68_3093) with
| (u1, u2) -> begin
(
# 2144 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2145 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _68_3098 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2151 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _68_3108 -> begin
(u1)::[]
end)
in (
# 2154 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _68_3113 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _68_27 -> (match (_68_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2160 "FStar.TypeChecker.Rel.fst"
let _68_3120 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_3120) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2162 "FStar.TypeChecker.Rel.fst"
let _68_3124 = (FStar_Syntax_Util.univ_kernel u')
in (match (_68_3124) with
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
| USolved (_68_3126) -> begin
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
# 2173 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2173 "FStar.TypeChecker.Rel.fst"
let _68_3132 = (empty_worklist env)
in {attempting = _68_3132.attempting; wl_deferred = _68_3132.wl_deferred; ctr = _68_3132.ctr; defer_ok = false; smt_ok = _68_3132.smt_ok; tcenv = _68_3132.tcenv})
in (
# 2174 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _68_3147 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2186 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2187 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2188 "FStar.TypeChecker.Rel.fst"
let _68_3152 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2191 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2192 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_3159 -> (match (_68_3159) with
| (d, s) -> begin
(
# 2193 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2195 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2196 "FStar.TypeChecker.Rel.fst"
let _68_3162 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1587 = (wl_to_string wl)
in (let _149_1586 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _149_1587 _149_1586)))
end else begin
()
end
in (
# 2198 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2199 "FStar.TypeChecker.Rel.fst"
let _68_3166 = g
in {FStar_TypeChecker_Env.guard_f = _68_3166.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_3166.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3166.FStar_TypeChecker_Env.implicits})
end
| _68_3169 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2201 "FStar.TypeChecker.Rel.fst"
let _68_3171 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2202 "FStar.TypeChecker.Rel.fst"
let _68_3173 = g
in {FStar_TypeChecker_Env.guard_f = _68_3173.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3173.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _68_3173.FStar_TypeChecker_Env.implicits})))))))

# 2204 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2205 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2206 "FStar.TypeChecker.Rel.fst"
let _68_3187 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2210 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2214 "FStar.TypeChecker.Rel.fst"
let _68_3185 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1594 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1593 = (let _149_1592 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _149_1592))
in (FStar_TypeChecker_Errors.diag _149_1594 _149_1593)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (
# 2219 "FStar.TypeChecker.Rel.fst"
let _68_3189 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_3189.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3189.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3189.FStar_TypeChecker_Env.implicits}))))

# 2221 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2222 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _68_3196 -> begin
false
end))
in (
# 2225 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _68_3200 implicits -> (match (_68_3200) with
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
# 2229 "FStar.TypeChecker.Rel.fst"
let _68_3211 = hd
in (match (_68_3211) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2232 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2233 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2234 "FStar.TypeChecker.Rel.fst"
let _68_3214 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1605 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_1604 = (FStar_Syntax_Print.term_to_string tm)
in (let _149_1603 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _149_1605 _149_1604 _149_1603))))
end else begin
()
end
in (
# 2237 "FStar.TypeChecker.Rel.fst"
let _68_3221 = (env.FStar_TypeChecker_Env.type_of (
# 2237 "FStar.TypeChecker.Rel.fst"
let _68_3216 = env
in {FStar_TypeChecker_Env.solver = _68_3216.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3216.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3216.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3216.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3216.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3216.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3216.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3216.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3216.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3216.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3216.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3216.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3216.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_3216.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_3216.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3216.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3216.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3216.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_3216.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3216.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3216.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_68_3221) with
| (_68_3219, g) -> begin
(
# 2238 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2239 "FStar.TypeChecker.Rel.fst"
let _68_3222 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_3222.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3222.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3222.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2241 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl)))
end)))))
end
end))
end)
end))
in (
# 2243 "FStar.TypeChecker.Rel.fst"
let _68_3226 = g
in (let _149_1606 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _68_3226.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3226.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3226.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _149_1606})))))

# 2245 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2246 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1611 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _149_1611 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _149_1612 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _149_1612))
end
| (_68_3235, _68_3237, _68_3239, _68_3241, r)::_68_3233 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2251 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2253 "FStar.TypeChecker.Rel.fst"
let _68_3247 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_3247.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3247.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _68_3247.FStar_TypeChecker_Env.implicits}))





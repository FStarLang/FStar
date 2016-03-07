
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
let rec head_matches : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun t1 t2 -> (match ((let _149_473 = (let _149_470 = (FStar_Syntax_Util.unmeta t1)
in _149_470.FStar_Syntax_Syntax.n)
in (let _149_472 = (let _149_471 = (FStar_Syntax_Util.unmeta t2)
in _149_471.FStar_Syntax_Syntax.n)
in (_149_473, _149_472)))) with
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
MisMatch ((Some (f.FStar_Syntax_Syntax.fv_delta), Some (f.FStar_Syntax_Syntax.fv_delta)))
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _68_583), FStar_Syntax_Syntax.Tm_uinst (g, _68_588)) -> begin
(let _149_474 = (head_matches f g)
in (FStar_All.pipe_right _149_474 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _68_599), FStar_Syntax_Syntax.Tm_uvar (uv', _68_604)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_610), FStar_Syntax_Syntax.Tm_refine (y, _68_615)) -> begin
(let _149_475 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_475 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_621), _68_625) -> begin
(let _149_476 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _149_476 head_match))
end
| (_68_628, FStar_Syntax_Syntax.Tm_refine (x, _68_631)) -> begin
(let _149_477 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _149_477 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_651), FStar_Syntax_Syntax.Tm_app (head', _68_656)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _68_662), _68_666) -> begin
(head_matches head t2)
end
| (_68_669, FStar_Syntax_Syntax.Tm_app (head, _68_672)) -> begin
(head_matches t1 head)
end
| _68_677 -> begin
MisMatch ((None, None))
end))

# 632 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 633 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 634 "FStar.TypeChecker.Rel.fst"
let fail = (fun r -> (r, None))
in (
# 635 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun d t1 t2 -> (
# 636 "FStar.TypeChecker.Rel.fst"
let r = (head_matches t1 t2)
in (match (r) with
| MisMatch (_68_695) -> begin
if (d = 3) then begin
(fail r)
end else begin
(
# 640 "FStar.TypeChecker.Rel.fst"
let steps = if (d = 0) then begin
(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.WHNF)::[]
end else begin
if (d = 1) then begin
(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.WHNF)::[]
end else begin
(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]
end
end
in (
# 646 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement steps env wl t1)
in (
# 647 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement steps env wl t2)
in (aux (d + 1) t1' t2'))))
end
end
| _68_701 -> begin
(success d r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 667 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 668 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 669 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 668 "FStar.TypeChecker.Rel.fst"
let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_68_704) -> begin
_68_704
end))

# 669 "FStar.TypeChecker.Rel.fst"
let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_68_707) -> begin
_68_707
end))

# 670 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 672 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun env t -> (
# 673 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 674 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches t t')) with
| MisMatch (_68_714) -> begin
false
end
| _68_717 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 679 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 680 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_68_727, imp), T (t)) -> begin
(t, imp)
end
| _68_734 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 685 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _68_739 -> (match (_68_739) with
| (t, _68_738) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 691 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_746 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 692 "FStar.TypeChecker.Rel.fst"
let _68_749 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_68_749) with
| (bs, c) -> begin
(
# 694 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 695 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 696 "FStar.TypeChecker.Rel.fst"
let _68_766 = x
in {FStar_Syntax_Syntax.ppname = _68_766.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_766.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _68_774 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 701 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _68_19 -> (match (_68_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 704 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _149_571 = (decompose [] bs)
in (rebuild, matches, _149_571))))
end)))
end
| _68_784 -> begin
(
# 712 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _68_20 -> (match (_68_20) with
| [] -> begin
t
end
| _68_788 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 718 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _68_21 -> (match (_68_21) with
| T (t) -> begin
t
end
| _68_795 -> begin
(FStar_All.failwith "Impossible")
end))

# 722 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _68_22 -> (match (_68_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _68_800 -> begin
(FStar_All.failwith "Impossible")
end))

# 726 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 731 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 732 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 733 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_68_813, variance, T (ti)) -> begin
(
# 736 "FStar.TypeChecker.Rel.fst"
let k = (
# 737 "FStar.TypeChecker.Rel.fst"
let _68_821 = (FStar_Syntax_Util.type_u ())
in (match (_68_821) with
| (t, _68_820) -> begin
(let _149_593 = (new_uvar r scope t)
in (Prims.fst _149_593))
end))
in (
# 739 "FStar.TypeChecker.Rel.fst"
let _68_825 = (new_uvar r scope k)
in (match (_68_825) with
| (gi_xs, gi) -> begin
(
# 740 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _68_828 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _149_596 = (let _149_595 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _149_594 -> FStar_TypeChecker_Common.TProb (_149_594)) _149_595))
in (T (gi_xs), _149_596)))
end)))
end
| (_68_831, _68_833, C (_68_835)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 748 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 752 "FStar.TypeChecker.Rel.fst"
let _68_913 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _68_853; FStar_Syntax_Syntax.pos = _68_851; FStar_Syntax_Syntax.vars = _68_849})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_605 = (let _149_604 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _149_603 -> C (_149_603)) _149_604))
in (_149_605, (prob)::[]))
end
| _68_864 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _68_872; FStar_Syntax_Syntax.pos = _68_870; FStar_Syntax_Syntax.vars = _68_868})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _149_608 = (let _149_607 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _149_606 -> C (_149_606)) _149_607))
in (_149_608, (prob)::[]))
end
| _68_883 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_68_885, _68_887, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _68_893; FStar_Syntax_Syntax.pos = _68_891; FStar_Syntax_Syntax.vars = _68_889})) -> begin
(
# 766 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 767 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 768 "FStar.TypeChecker.Rel.fst"
let _68_904 = (let _149_610 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _149_610 FStar_List.unzip))
in (match (_68_904) with
| (tcs, sub_probs) -> begin
(
# 769 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _149_615 = (let _149_614 = (let _149_611 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _149_611 un_T))
in (let _149_613 = (let _149_612 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _149_612 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _149_614; FStar_Syntax_Syntax.effect_args = _149_613; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _149_615))
in (C (gi_xs), sub_probs))
end))))
end
| _68_907 -> begin
(
# 778 "FStar.TypeChecker.Rel.fst"
let _68_910 = (sub_prob scope args q)
in (match (_68_910) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_68_913) with
| (tc, probs) -> begin
(
# 781 "FStar.TypeChecker.Rel.fst"
let _68_926 = (match (q) with
| (Some (b), _68_917, _68_919) -> begin
(let _149_617 = (let _149_616 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_149_616)::args)
in (Some (b), (b)::scope, _149_617))
end
| _68_922 -> begin
(None, scope, args)
end)
in (match (_68_926) with
| (bopt, scope, args) -> begin
(
# 785 "FStar.TypeChecker.Rel.fst"
let _68_930 = (aux scope args qs)
in (match (_68_930) with
| (sub_probs, tcs, f) -> begin
(
# 786 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _149_620 = (let _149_619 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_149_619)
in (FStar_Syntax_Util.mk_conj_l _149_620))
end
| Some (b) -> begin
(let _149_624 = (let _149_623 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _149_622 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_149_623)::_149_622))
in (FStar_Syntax_Util.mk_conj_l _149_624))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 801 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 802 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 803 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _68_958), FStar_Syntax_Syntax.Tm_uvar (u2, _68_963)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _68_977 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _68_983 _68_987 -> (match ((_68_983, _68_987)) with
| ((a1, _68_982), (a2, _68_986)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 820 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 821 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 823 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 824 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 825 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 826 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 827 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 828 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 829 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 830 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 831 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 831 "FStar.TypeChecker.Rel.fst"
let _68_990 = p
in (let _149_646 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _149_645 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _68_990.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_646; FStar_TypeChecker_Common.relation = _68_990.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_645; FStar_TypeChecker_Common.element = _68_990.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_990.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_990.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_990.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_990.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_990.FStar_TypeChecker_Common.rank}))))

# 833 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _149_652 = (compress_tprob wl p)
in (FStar_All.pipe_right _149_652 (fun _149_651 -> FStar_TypeChecker_Common.TProb (_149_651))))
end
| FStar_TypeChecker_Common.CProb (_68_997) -> begin
p
end))

# 838 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 841 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_657 = (compress_prob wl pr)
in (FStar_All.pipe_right _149_657 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 844 "FStar.TypeChecker.Rel.fst"
let _68_1007 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1007) with
| (lh, _68_1006) -> begin
(
# 845 "FStar.TypeChecker.Rel.fst"
let _68_1011 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_68_1011) with
| (rh, _68_1010) -> begin
(
# 846 "FStar.TypeChecker.Rel.fst"
let _68_1067 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_68_1013), FStar_Syntax_Syntax.Tm_uvar (_68_1016)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_68_1032), _68_1035) -> begin
(
# 853 "FStar.TypeChecker.Rel.fst"
let _68_1039 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_68_1039) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _68_1042 -> begin
(
# 857 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _149_659 = (
# 861 "FStar.TypeChecker.Rel.fst"
let _68_1044 = tp
in (let _149_658 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1044.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1044.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1044.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_658; FStar_TypeChecker_Common.element = _68_1044.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1044.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1044.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1044.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1044.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1044.FStar_TypeChecker_Common.rank}))
in (rank, _149_659)))
end)
end))
end
| (_68_1047, FStar_Syntax_Syntax.Tm_uvar (_68_1049)) -> begin
(
# 865 "FStar.TypeChecker.Rel.fst"
let _68_1054 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1054) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _68_1057 -> begin
(let _149_661 = (
# 868 "FStar.TypeChecker.Rel.fst"
let _68_1058 = tp
in (let _149_660 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _68_1058.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_660; FStar_TypeChecker_Common.relation = _68_1058.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1058.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1058.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1058.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1058.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1058.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1058.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1058.FStar_TypeChecker_Common.rank}))
in (refine_flex, _149_661))
end)
end))
end
| (_68_1061, _68_1063) -> begin
(rigid_rigid, tp)
end)
in (match (_68_1067) with
| (rank, tp) -> begin
(let _149_663 = (FStar_All.pipe_right (
# 873 "FStar.TypeChecker.Rel.fst"
let _68_1068 = tp
in {FStar_TypeChecker_Common.pid = _68_1068.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1068.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1068.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1068.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1068.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1068.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1068.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1068.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1068.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _149_662 -> FStar_TypeChecker_Common.TProb (_149_662)))
in (rank, _149_663))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _149_665 = (FStar_All.pipe_right (
# 875 "FStar.TypeChecker.Rel.fst"
let _68_1072 = cp
in {FStar_TypeChecker_Common.pid = _68_1072.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_1072.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_1072.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_1072.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_1072.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1072.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1072.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1072.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1072.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _149_664 -> FStar_TypeChecker_Common.CProb (_149_664)))
in (rigid_rigid, _149_665))
end)))

# 877 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 881 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _68_1079 probs -> (match (_68_1079) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 884 "FStar.TypeChecker.Rel.fst"
let _68_1087 = (rank wl hd)
in (match (_68_1087) with
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

# 897 "FStar.TypeChecker.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 899 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 900 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 901 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 902 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 900 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_68_1097) -> begin
_68_1097
end))

# 901 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_68_1100) -> begin
_68_1100
end))

# 902 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_68_1103) -> begin
_68_1103
end))

# 904 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 905 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 906 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 907 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 910 "FStar.TypeChecker.Rel.fst"
let _68_1119 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_1119) with
| (k, _68_1118) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _68_1123 -> begin
false
end)
end)))))
end
| _68_1125 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 916 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_68_1131), FStar_Syntax_Syntax.U_max (_68_1134)) -> begin
(let _149_737 = (let _149_736 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_735 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _149_736 _149_735)))
in UFailed (_149_737))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 923 "FStar.TypeChecker.Rel.fst"
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
| _68_1154 -> begin
(let _149_744 = (let _149_743 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_742 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _149_743 _149_742 msg)))
in UFailed (_149_744))
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
# 944 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 949 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _149_747 = (let _149_746 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _149_745 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _149_746 _149_745)))
in (try_umax_components u1 u2 _149_747))
end else begin
(let _149_748 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_149_748))
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
# 974 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 975 "FStar.TypeChecker.Rel.fst"
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

# 987 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 989 "FStar.TypeChecker.Rel.fst"
let _68_1249 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_791 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _149_791))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 993 "FStar.TypeChecker.Rel.fst"
let probs = (
# 993 "FStar.TypeChecker.Rel.fst"
let _68_1256 = probs
in {attempting = tl; wl_deferred = _68_1256.wl_deferred; ctr = _68_1256.ctr; defer_ok = _68_1256.defer_ok; smt_ok = _68_1256.smt_ok; tcenv = _68_1256.tcenv})
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
| (None, _68_1268, _68_1270) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _68_1274 -> begin
(
# 1015 "FStar.TypeChecker.Rel.fst"
let _68_1283 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _68_1280 -> (match (_68_1280) with
| (c, _68_1277, _68_1279) -> begin
(c < probs.ctr)
end))))
in (match (_68_1283) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _149_794 = (FStar_List.map (fun _68_1289 -> (match (_68_1289) with
| (_68_1286, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_149_794))
end
| _68_1291 -> begin
(let _149_797 = (
# 1021 "FStar.TypeChecker.Rel.fst"
let _68_1292 = probs
in (let _149_796 = (FStar_All.pipe_right attempt (FStar_List.map (fun _68_1299 -> (match (_68_1299) with
| (_68_1295, _68_1297, y) -> begin
y
end))))
in {attempting = _149_796; wl_deferred = rest; ctr = _68_1292.ctr; defer_ok = _68_1292.defer_ok; smt_ok = _68_1292.smt_ok; tcenv = _68_1292.tcenv}))
in (solve env _149_797))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _149_803 = (solve_prob orig None [] wl)
in (solve env _149_803))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1035 "FStar.TypeChecker.Rel.fst"
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
| _68_1334 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _149_818 = (let _149_815 = (whnf env t1)
in _149_815.FStar_Syntax_Syntax.n)
in (let _149_817 = (let _149_816 = (whnf env t2)
in _149_816.FStar_Syntax_Syntax.n)
in (_149_818, _149_817)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _68_1340; FStar_Syntax_Syntax.pos = _68_1338; FStar_Syntax_Syntax.vars = _68_1336}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _68_1352; FStar_Syntax_Syntax.pos = _68_1350; FStar_Syntax_Syntax.vars = _68_1348}, us2)) -> begin
(
# 1050 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1051 "FStar.TypeChecker.Rel.fst"
let _68_1361 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _68_1376 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1064 "FStar.TypeChecker.Rel.fst"
let _68_1381 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_823 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _149_823 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1074 "FStar.TypeChecker.Rel.fst"
let _68_1386 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_827 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _149_827))
end else begin
()
end
in (
# 1076 "FStar.TypeChecker.Rel.fst"
let _68_1390 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1390) with
| (u, args) -> begin
(
# 1077 "FStar.TypeChecker.Rel.fst"
let _68_1396 = (0, 1, 2, 3, 4)
in (match (_68_1396) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1078 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1080 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1081 "FStar.TypeChecker.Rel.fst"
let _68_1405 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1405) with
| (h1, args1) -> begin
(
# 1082 "FStar.TypeChecker.Rel.fst"
let _68_1409 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1409) with
| (h2, _68_1408) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _149_839 = (let _149_838 = (let _149_837 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _149_836 -> FStar_TypeChecker_Common.TProb (_149_836)) _149_837))
in (_149_838)::[])
in Some (_149_839))
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
| _68_1421 -> begin
None
end)
end))
end)))
in (
# 1098 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1100 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1104 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1105 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1106 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1107 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _149_846 = (let _149_845 = (let _149_844 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _149_844))
in (_149_845, m))
in Some (_149_846))))))
end))
end
| (_68_1443, FStar_Syntax_Syntax.Tm_refine (y, _68_1446)) -> begin
(
# 1112 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _68_1456), _68_1460) -> begin
(
# 1119 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _68_1467 -> begin
(
# 1126 "FStar.TypeChecker.Rel.fst"
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
# 1132 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _68_1475) -> begin
(
# 1136 "FStar.TypeChecker.Rel.fst"
let _68_1500 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _68_23 -> (match (_68_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1140 "FStar.TypeChecker.Rel.fst"
let _68_1486 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_68_1486) with
| (u', _68_1485) -> begin
(match ((let _149_848 = (whnf env u')
in _149_848.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _68_1489) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _68_1493 -> begin
false
end)
end))
end
| _68_1495 -> begin
false
end)
end
| _68_1497 -> begin
false
end))))
in (match (_68_1500) with
| (upper_bounds, rest) -> begin
(
# 1149 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _68_1504 tps -> (match (_68_1504) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _149_853 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _149_853))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _68_1517 -> begin
None
end)
end))
in (match ((let _149_855 = (let _149_854 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_149_854, []))
in (make_upper_bound _149_855 upper_bounds))) with
| None -> begin
(
# 1160 "FStar.TypeChecker.Rel.fst"
let _68_1519 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1173 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1174 "FStar.TypeChecker.Rel.fst"
let _68_1529 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1175 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1175 "FStar.TypeChecker.Rel.fst"
let _68_1526 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _68_1526.wl_deferred; ctr = _68_1526.ctr; defer_ok = _68_1526.defer_ok; smt_ok = _68_1526.smt_ok; tcenv = _68_1526.tcenv})
in (let _149_856 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _149_856)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1177 "FStar.TypeChecker.Rel.fst"
let _68_1531 = wl
in {attempting = sub_probs; wl_deferred = _68_1531.wl_deferred; ctr = _68_1531.ctr; defer_ok = _68_1531.defer_ok; smt_ok = _68_1531.smt_ok; tcenv = _68_1531.tcenv}))) with
| Success (_68_1534) -> begin
(
# 1179 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1179 "FStar.TypeChecker.Rel.fst"
let _68_1536 = wl
in {attempting = rest; wl_deferred = _68_1536.wl_deferred; ctr = _68_1536.ctr; defer_ok = _68_1536.defer_ok; smt_ok = _68_1536.smt_ok; tcenv = _68_1536.tcenv})
in (
# 1180 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1181 "FStar.TypeChecker.Rel.fst"
let _68_1542 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _68_1545 -> begin
None
end)))
end))
end))
end
| _68_1547 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1191 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1194 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1195 "FStar.TypeChecker.Rel.fst"
let _68_1564 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_884 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _149_884))
end else begin
()
end
in (
# 1197 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1201 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1201 "FStar.TypeChecker.Rel.fst"
let _68_1578 = hd1
in (let _149_885 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1578.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1578.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_885}))
in (
# 1202 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1202 "FStar.TypeChecker.Rel.fst"
let _68_1581 = hd2
in (let _149_886 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _68_1581.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_1581.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _149_886}))
in (
# 1203 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_889 = (let _149_888 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _149_888 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _149_887 -> FStar_TypeChecker_Common.TProb (_149_887)) _149_889))
in (
# 1204 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1205 "FStar.TypeChecker.Rel.fst"
let subst = (let _149_890 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_149_890)
in (
# 1206 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1209 "FStar.TypeChecker.Rel.fst"
let phi = (let _149_892 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _149_891 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _149_892 _149_891)))
in (
# 1210 "FStar.TypeChecker.Rel.fst"
let _68_1593 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_894 = (FStar_Syntax_Print.term_to_string phi)
in (let _149_893 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _149_894 _149_893)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _68_1597 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1219 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1223 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _149_898 = (compress_tprob wl problem)
in (solve_t' env _149_898 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1230 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1233 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1234 "FStar.TypeChecker.Rel.fst"
let _68_1625 = (head_matches_delta env wl t1 t2)
in (match (_68_1625) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_68_1627), _68_1630) -> begin
(
# 1237 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_68_1635) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _68_1640 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1242 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1245 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1249 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _149_927 = (let _149_926 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _149_926 t2))
in (FStar_Syntax_Util.mk_forall x _149_927)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _149_928 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _149_928)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_68_1650, Some (t1, t2)) -> begin
(solve_t env (
# 1258 "FStar.TypeChecker.Rel.fst"
let _68_1656 = problem
in {FStar_TypeChecker_Common.pid = _68_1656.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_1656.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_1656.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1656.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1656.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1656.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1656.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1656.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_1659, None) -> begin
(
# 1261 "FStar.TypeChecker.Rel.fst"
let _68_1662 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_932 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_931 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_930 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_929 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _149_932 _149_931 _149_930 _149_929)))))
end else begin
()
end
in (
# 1265 "FStar.TypeChecker.Rel.fst"
let _68_1666 = (FStar_Syntax_Util.head_and_args t1)
in (match (_68_1666) with
| (head, args) -> begin
(
# 1266 "FStar.TypeChecker.Rel.fst"
let _68_1669 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1669) with
| (head', args') -> begin
(
# 1267 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _149_937 = (let _149_936 = (FStar_Syntax_Print.term_to_string head)
in (let _149_935 = (args_to_string args)
in (let _149_934 = (FStar_Syntax_Print.term_to_string head')
in (let _149_933 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _149_936 _149_935 _149_934 _149_933)))))
in (giveup env _149_937 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _149_938 = (solve_prob orig None [] wl)
in (solve env _149_938))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1288 "FStar.TypeChecker.Rel.fst"
let _68_1679 = (base_and_refinement env wl t1)
in (match (_68_1679) with
| (base1, refinement1) -> begin
(
# 1289 "FStar.TypeChecker.Rel.fst"
let _68_1682 = (base_and_refinement env wl t2)
in (match (_68_1682) with
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
# 1296 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _68_1695 _68_1699 -> (match ((_68_1695, _68_1699)) with
| ((a, _68_1694), (a', _68_1698)) -> begin
(let _149_942 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _149_941 -> FStar_TypeChecker_Common.TProb (_149_941)) _149_942))
end)) args args')
in (
# 1297 "FStar.TypeChecker.Rel.fst"
let formula = (let _149_944 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _149_944))
in (
# 1298 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _68_1705 -> begin
(
# 1303 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1304 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1305 "FStar.TypeChecker.Rel.fst"
let _68_1708 = problem
in {FStar_TypeChecker_Common.pid = _68_1708.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _68_1708.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _68_1708.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_1708.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_1708.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_1708.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_1708.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_1708.FStar_TypeChecker_Common.rank}) wl)))
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
# 1311 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1312 "FStar.TypeChecker.Rel.fst"
let _68_1725 = p
in (match (_68_1725) with
| ((u, k), ps, xs, (h, _68_1722, qs)) -> begin
(
# 1313 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1318 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1319 "FStar.TypeChecker.Rel.fst"
let _68_1731 = (imitation_sub_probs orig env xs ps qs)
in (match (_68_1731) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1320 "FStar.TypeChecker.Rel.fst"
let im = (let _149_955 = (h gs_xs)
in (u_abs xs _149_955))
in (
# 1321 "FStar.TypeChecker.Rel.fst"
let _68_1733 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_960 = (FStar_Syntax_Print.term_to_string im)
in (let _149_959 = (FStar_Syntax_Print.tag_of_term im)
in (let _149_958 = (let _149_956 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _149_956 (FStar_String.concat ", ")))
in (let _149_957 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _149_960 _149_959 _149_958 _149_957)))))
end else begin
()
end
in (
# 1326 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1331 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1332 "FStar.TypeChecker.Rel.fst"
let _68_1749 = p
in (match (_68_1749) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1336 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1337 "FStar.TypeChecker.Rel.fst"
let _68_1754 = (FStar_List.nth ps i)
in (match (_68_1754) with
| (pi, _68_1753) -> begin
(
# 1338 "FStar.TypeChecker.Rel.fst"
let _68_1758 = (FStar_List.nth xs i)
in (match (_68_1758) with
| (xi, _68_1757) -> begin
(
# 1340 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1341 "FStar.TypeChecker.Rel.fst"
let _68_1763 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1763) with
| (bs, k) -> begin
(
# 1342 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _68_1771)::tl -> begin
(
# 1345 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1346 "FStar.TypeChecker.Rel.fst"
let _68_1777 = (new_uvar r xs k_a)
in (match (_68_1777) with
| (gi_xs, gi) -> begin
(
# 1347 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1348 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1349 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1350 "FStar.TypeChecker.Rel.fst"
let _68_1783 = (aux subst tl)
in (match (_68_1783) with
| (gi_xs', gi_ps') -> begin
(let _149_982 = (let _149_979 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_149_979)::gi_xs')
in (let _149_981 = (let _149_980 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_149_980)::gi_ps')
in (_149_982, _149_981)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _149_983 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _149_983)) then begin
None
end else begin
(
# 1356 "FStar.TypeChecker.Rel.fst"
let _68_1787 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_68_1787) with
| (g_xs, _68_1786) -> begin
(
# 1357 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1358 "FStar.TypeChecker.Rel.fst"
let proj = (let _149_984 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _149_984))
in (
# 1359 "FStar.TypeChecker.Rel.fst"
let sub = (let _149_990 = (let _149_989 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _149_988 = (let _149_987 = (FStar_List.map (fun _68_1795 -> (match (_68_1795) with
| (_68_1791, _68_1793, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _149_987))
in (mk_problem (p_scope orig) orig _149_989 (p_rel orig) _149_988 None "projection")))
in (FStar_All.pipe_left (fun _149_985 -> FStar_TypeChecker_Common.TProb (_149_985)) _149_990))
in (
# 1360 "FStar.TypeChecker.Rel.fst"
let _68_1797 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_992 = (FStar_Syntax_Print.term_to_string proj)
in (let _149_991 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _149_992 _149_991)))
end else begin
()
end
in (
# 1361 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_994 = (let _149_993 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_149_993))
in (solve_prob orig _149_994 ((TERM ((u, proj)))::[]) wl))
in (let _149_996 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _149_995 -> Some (_149_995)) _149_996)))))))
end))
end)
end))
end)))
end)))
in (
# 1366 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1367 "FStar.TypeChecker.Rel.fst"
let _68_1811 = lhs
in (match (_68_1811) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1368 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1369 "FStar.TypeChecker.Rel.fst"
let xs = (let _149_1023 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _149_1023 Prims.fst))
in (let _149_1028 = (decompose env t2)
in ((uv, k), ps, xs, _149_1028))))
in (
# 1372 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1375 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_68_1821) -> begin
(
# 1379 "FStar.TypeChecker.Rel.fst"
let _68_1823 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1386 "FStar.TypeChecker.Rel.fst"
let _68_1831 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1390 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1391 "FStar.TypeChecker.Rel.fst"
let _68_1841 = (FStar_Syntax_Util.head_and_args t2)
in (match (_68_1841) with
| (hd, _68_1840) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _68_1852 -> begin
(
# 1397 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1400 "FStar.TypeChecker.Rel.fst"
let _68_1854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1039 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _149_1039))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1403 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1404 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _149_1043 = (let _149_1042 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1042 Prims.fst))
in (FStar_All.pipe_right _149_1043 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1411 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1412 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1413 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1414 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1415 "FStar.TypeChecker.Rel.fst"
let _68_1867 = (occurs_check env wl (uv, k) t2)
in (match (_68_1867) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _149_1045 = (let _149_1044 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _149_1044))
in (giveup_or_defer orig _149_1045))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _149_1046 = (subterms args_lhs)
in (imitate orig env wl _149_1046))
end else begin
(
# 1422 "FStar.TypeChecker.Rel.fst"
let _68_1868 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1049 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1048 = (names_to_string fvs1)
in (let _149_1047 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _149_1049 _149_1048 _149_1047))))
end else begin
()
end
in (
# 1427 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _68_1872 -> begin
(let _149_1050 = (sn_binders env vars)
in (u_abs _149_1050 t2))
end)
in (
# 1430 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1435 "FStar.TypeChecker.Rel.fst"
let _68_1875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1053 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1052 = (names_to_string fvs1)
in (let _149_1051 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _149_1053 _149_1052 _149_1051))))
end else begin
()
end
in (let _149_1054 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1054 (- (1)))))
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
if (let _149_1055 = (FStar_Syntax_Free.names t1)
in (check_head _149_1055 t2)) then begin
(
# 1447 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1448 "FStar.TypeChecker.Rel.fst"
let _68_1879 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1056 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _149_1056 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _149_1057 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _149_1057 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1473 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1476 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _68_1891 -> (match (_68_1891) with
| (t, u, k, args) -> begin
(
# 1479 "FStar.TypeChecker.Rel.fst"
let _68_1895 = (FStar_Syntax_Util.arrow_formals k)
in (match (_68_1895) with
| (all_formals, _68_1894) -> begin
(
# 1480 "FStar.TypeChecker.Rel.fst"
let _68_1896 = ()
in (
# 1482 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1490 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _68_1909 -> (match (_68_1909) with
| (x, imp) -> begin
(let _149_1079 = (FStar_Syntax_Syntax.bv_to_name x)
in (_149_1079, imp))
end))))
in (
# 1491 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1492 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1493 "FStar.TypeChecker.Rel.fst"
let _68_1915 = (FStar_Syntax_Util.type_u ())
in (match (_68_1915) with
| (t, _68_1914) -> begin
(let _149_1080 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _149_1080))
end))
in (
# 1495 "FStar.TypeChecker.Rel.fst"
let _68_1919 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_68_1919) with
| (t', tm_u1) -> begin
(
# 1496 "FStar.TypeChecker.Rel.fst"
let _68_1926 = (destruct_flex_t t')
in (match (_68_1926) with
| (_68_1921, u1, k1, _68_1925) -> begin
(
# 1497 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1082 = (let _149_1081 = (u_abs all_formals t')
in ((u, k), _149_1081))
in TERM (_149_1082))
in (
# 1498 "FStar.TypeChecker.Rel.fst"
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
# 1507 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _68_1945 -> (match (_68_1945) with
| (x, _68_1944) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1514 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _149_1084 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _149_1084 formals tl))
end)
end)
end)
end
| _68_1949 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _149_1085 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _149_1085 all_formals args))))
end))
end))
in (
# 1526 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _68_1955 _68_1959 r -> (match ((_68_1955, _68_1959)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _149_1094 = (solve_prob orig None [] wl)
in (solve env _149_1094))
end else begin
(
# 1534 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1535 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1536 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1537 "FStar.TypeChecker.Rel.fst"
let _68_1964 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1097 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _149_1096 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _149_1095 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _149_1097 _149_1096 _149_1095))))
end else begin
()
end
in (
# 1540 "FStar.TypeChecker.Rel.fst"
let _68_1977 = (
# 1541 "FStar.TypeChecker.Rel.fst"
let _68_1969 = (FStar_Syntax_Util.type_u ())
in (match (_68_1969) with
| (t, _68_1968) -> begin
(
# 1542 "FStar.TypeChecker.Rel.fst"
let _68_1973 = (new_uvar r zs t)
in (match (_68_1973) with
| (k, _68_1972) -> begin
(new_uvar r zs k)
end))
end))
in (match (_68_1977) with
| (u_zs, _68_1976) -> begin
(
# 1544 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs xs u_zs)
in (
# 1545 "FStar.TypeChecker.Rel.fst"
let _68_1981 = (occurs_check env wl (u1, k1) sub1)
in (match (_68_1981) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1548 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1550 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1552 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs ys u_zs)
in (
# 1553 "FStar.TypeChecker.Rel.fst"
let _68_1987 = (occurs_check env wl (u2, k2) sub2)
in (match (_68_1987) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1556 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1557 "FStar.TypeChecker.Rel.fst"
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
# 1560 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _68_1995 _68_2000 -> (match ((_68_1995, _68_2000)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1562 "FStar.TypeChecker.Rel.fst"
let _68_2001 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1103 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1102 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _149_1103 _149_1102)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1565 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_2006 _68_2010 -> (match ((_68_2006, _68_2010)) with
| ((a, _68_2005), (t2, _68_2009)) -> begin
(let _149_1108 = (let _149_1106 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _149_1106 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _149_1108 (fun _149_1107 -> FStar_TypeChecker_Common.TProb (_149_1107))))
end)) xs args2)
in (
# 1568 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1110 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1110))
in (
# 1569 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1572 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1573 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1574 "FStar.TypeChecker.Rel.fst"
let _68_2020 = (occurs_check env wl (u1, k1) t2)
in (match (_68_2020) with
| (occurs_ok, _68_2019) -> begin
(
# 1575 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1578 "FStar.TypeChecker.Rel.fst"
let sol = (let _149_1112 = (let _149_1111 = (u_abs xs t2)
in ((u1, k1), _149_1111))
in TERM (_149_1112))
in (
# 1579 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1582 "FStar.TypeChecker.Rel.fst"
let _68_2031 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_68_2031) with
| (sol, (_68_2026, u2, k2, ys)) -> begin
(
# 1583 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1584 "FStar.TypeChecker.Rel.fst"
let _68_2033 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1113 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _149_1113))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2038 -> begin
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
# 1592 "FStar.TypeChecker.Rel.fst"
let _68_2043 = lhs
in (match (_68_2043) with
| (t1, u1, k1, args1) -> begin
(
# 1593 "FStar.TypeChecker.Rel.fst"
let _68_2048 = rhs
in (match (_68_2048) with
| (t2, u2, k2, args2) -> begin
(
# 1594 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1595 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1596 "FStar.TypeChecker.Rel.fst"
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
| _68_2066 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1605 "FStar.TypeChecker.Rel.fst"
let _68_2070 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_68_2070) with
| (sol, _68_2069) -> begin
(
# 1606 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1607 "FStar.TypeChecker.Rel.fst"
let _68_2072 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _149_1114 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _149_1114))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _68_2077 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1614 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _149_1115 = (solve_prob orig None [] wl)
in (solve env _149_1115))
end else begin
(
# 1616 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1617 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _149_1116 = (solve_prob orig None [] wl)
in (solve env _149_1116))
end else begin
(
# 1619 "FStar.TypeChecker.Rel.fst"
let _68_2081 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1117 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _149_1117))
end else begin
()
end
in (
# 1622 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1624 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _68_2086 _68_2089 -> (match ((_68_2086, _68_2089)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1626 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1627 "FStar.TypeChecker.Rel.fst"
let _68_2096 = (FStar_Util.first_N n bs)
in (match (_68_2096) with
| (bs, rest) -> begin
(let _149_1147 = (mk_cod rest)
in (bs, _149_1147))
end)))
in (
# 1630 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1631 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _149_1151 = (let _149_1148 = (mk_cod1 [])
in (bs1, _149_1148))
in (let _149_1150 = (let _149_1149 = (mk_cod2 [])
in (bs2, _149_1149))
in (_149_1151, _149_1150)))
end else begin
if (l1 > l2) then begin
(let _149_1154 = (curry l2 bs1 mk_cod1)
in (let _149_1153 = (let _149_1152 = (mk_cod2 [])
in (bs2, _149_1152))
in (_149_1154, _149_1153)))
end else begin
(let _149_1157 = (let _149_1155 = (mk_cod1 [])
in (bs1, _149_1155))
in (let _149_1156 = (curry l1 bs2 mk_cod2)
in (_149_1157, _149_1156)))
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
# 1649 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _68_24 -> (match (_68_24) with
| [] -> begin
c
end
| bs -> begin
(let _149_1162 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _149_1162))
end))
in (
# 1653 "FStar.TypeChecker.Rel.fst"
let _68_2139 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_68_2139) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1658 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1659 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1660 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _149_1169 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _149_1168 -> FStar_TypeChecker_Common.CProb (_149_1168)) _149_1169)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _68_2149), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _68_2155)) -> begin
(
# 1664 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _68_25 -> (match (_68_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1667 "FStar.TypeChecker.Rel.fst"
let _68_2170 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_68_2170) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _149_1182 = (let _149_1181 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _149_1180 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _149_1181 problem.FStar_TypeChecker_Common.relation _149_1180 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _149_1179 -> FStar_TypeChecker_Common.TProb (_149_1179)) _149_1182))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2175), FStar_Syntax_Syntax.Tm_refine (_68_2178)) -> begin
(
# 1676 "FStar.TypeChecker.Rel.fst"
let _68_2183 = (as_refinement env wl t1)
in (match (_68_2183) with
| (x1, phi1) -> begin
(
# 1677 "FStar.TypeChecker.Rel.fst"
let _68_2186 = (as_refinement env wl t2)
in (match (_68_2186) with
| (x2, phi2) -> begin
(
# 1678 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1184 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _149_1183 -> FStar_TypeChecker_Common.TProb (_149_1183)) _149_1184))
in (
# 1679 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1680 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1681 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1682 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1683 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1684 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _149_1201 = (imp phi1 phi2)
in (FStar_All.pipe_right _149_1201 (guard_on_element problem x1))))
in (
# 1685 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _68_2198 -> (match (()) with
| () -> begin
(
# 1686 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1690 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1204 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1204 impl))
in (
# 1691 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1694 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _149_1208 = (let _149_1207 = (let _149_1206 = (FStar_Syntax_Syntax.mk_binder x1)
in (_149_1206)::(p_scope orig))
in (mk_problem _149_1207 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _149_1205 -> FStar_TypeChecker_Common.TProb (_149_1205)) _149_1208))
in (match ((solve env (
# 1695 "FStar.TypeChecker.Rel.fst"
let _68_2203 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _68_2203.ctr; defer_ok = false; smt_ok = _68_2203.smt_ok; tcenv = _68_2203.tcenv}))) with
| Failed (_68_2206) -> begin
(fallback ())
end
| Success (_68_2209) -> begin
(
# 1698 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1211 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _149_1210 = (let _149_1209 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _149_1209 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _149_1211 _149_1210)))
in (
# 1699 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1700 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1700 "FStar.TypeChecker.Rel.fst"
let _68_2213 = wl
in {attempting = _68_2213.attempting; wl_deferred = _68_2213.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _68_2213.defer_ok; smt_ok = _68_2213.smt_ok; tcenv = _68_2213.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _149_1213 = (destruct_flex_t t1)
in (let _149_1212 = (destruct_flex_t t2)
in (flex_flex orig _149_1213 _149_1212)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _149_1214 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _149_1214 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1728 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _149_1215 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _149_1215)) then begin
(let _149_1218 = (FStar_All.pipe_left (fun _149_1216 -> FStar_TypeChecker_Common.TProb (_149_1216)) (
# 1730 "FStar.TypeChecker.Rel.fst"
let _68_2358 = problem
in {FStar_TypeChecker_Common.pid = _68_2358.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2358.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2358.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2358.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2358.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2358.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2358.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2358.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2358.FStar_TypeChecker_Common.rank}))
in (let _149_1217 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1218 _149_1217 t2 wl)))
end else begin
(
# 1731 "FStar.TypeChecker.Rel.fst"
let _68_2362 = (base_and_refinement env wl t2)
in (match (_68_2362) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _149_1221 = (FStar_All.pipe_left (fun _149_1219 -> FStar_TypeChecker_Common.TProb (_149_1219)) (
# 1734 "FStar.TypeChecker.Rel.fst"
let _68_2364 = problem
in {FStar_TypeChecker_Common.pid = _68_2364.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2364.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _68_2364.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2364.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2364.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2364.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2364.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2364.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2364.FStar_TypeChecker_Common.rank}))
in (let _149_1220 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _149_1221 _149_1220 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1737 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1737 "FStar.TypeChecker.Rel.fst"
let _68_2370 = y
in {FStar_Syntax_Syntax.ppname = _68_2370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _68_2370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1738 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1739 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1223 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _149_1222 -> FStar_TypeChecker_Common.TProb (_149_1222)) _149_1223))
in (
# 1741 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1224 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1224 impl))
in (
# 1742 "FStar.TypeChecker.Rel.fst"
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
# 1751 "FStar.TypeChecker.Rel.fst"
let _68_2403 = (base_and_refinement env wl t1)
in (match (_68_2403) with
| (t_base, _68_2402) -> begin
(solve_t env (
# 1752 "FStar.TypeChecker.Rel.fst"
let _68_2404 = problem
in {FStar_TypeChecker_Common.pid = _68_2404.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _68_2404.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2404.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2404.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2404.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2404.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2404.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2404.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_68_2407), _68_2410) -> begin
(
# 1755 "FStar.TypeChecker.Rel.fst"
let t2 = (let _149_1225 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _149_1225))
in (solve_t env (
# 1756 "FStar.TypeChecker.Rel.fst"
let _68_2413 = problem
in {FStar_TypeChecker_Common.pid = _68_2413.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2413.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2413.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2413.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2413.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2413.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2413.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2413.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2413.FStar_TypeChecker_Common.rank}) wl))
end
| (_68_2416, FStar_Syntax_Syntax.Tm_refine (_68_2418)) -> begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let t1 = (let _149_1226 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _149_1226))
in (solve_t env (
# 1760 "FStar.TypeChecker.Rel.fst"
let _68_2422 = problem
in {FStar_TypeChecker_Common.pid = _68_2422.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2422.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2422.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2422.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2422.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2422.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2422.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2422.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2422.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1764 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_68_2439) -> begin
t
end
| _68_2442 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _149_1231 = (
# 1767 "FStar.TypeChecker.Rel.fst"
let _68_2443 = problem
in (let _149_1230 = (maybe_eta t1)
in (let _149_1229 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _68_2443.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1230; FStar_TypeChecker_Common.relation = _68_2443.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1229; FStar_TypeChecker_Common.element = _68_2443.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2443.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2443.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2443.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2443.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2443.FStar_TypeChecker_Common.rank})))
in (solve_t env _149_1231 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1779 "FStar.TypeChecker.Rel.fst"
let head1 = (let _149_1232 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _149_1232 Prims.fst))
in (
# 1780 "FStar.TypeChecker.Rel.fst"
let head2 = (let _149_1233 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _149_1233 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1785 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1786 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1788 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _149_1235 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _149_1234 -> Some (_149_1234)) _149_1235))
end
in (let _149_1236 = (solve_prob orig guard [] wl)
in (solve env _149_1236)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _68_2512, _68_2514), _68_2518) -> begin
(solve_t' env (
# 1796 "FStar.TypeChecker.Rel.fst"
let _68_2520 = problem
in {FStar_TypeChecker_Common.pid = _68_2520.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _68_2520.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2520.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2520.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2520.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2520.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2520.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2520.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2520.FStar_TypeChecker_Common.rank}) wl)
end
| (_68_2523, FStar_Syntax_Syntax.Tm_ascribed (t2, _68_2526, _68_2528)) -> begin
(solve_t' env (
# 1799 "FStar.TypeChecker.Rel.fst"
let _68_2532 = problem
in {FStar_TypeChecker_Common.pid = _68_2532.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2532.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2532.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _68_2532.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2532.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2532.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2532.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2532.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2532.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _149_1239 = (let _149_1238 = (FStar_Syntax_Print.tag_of_term t1)
in (let _149_1237 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _149_1238 _149_1237)))
in (FStar_All.failwith _149_1239))
end
| _68_2571 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1811 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1812 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1813 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1814 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1816 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1817 "FStar.TypeChecker.Rel.fst"
let _68_2588 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1819 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _68_2593 _68_2597 -> (match ((_68_2593, _68_2597)) with
| ((a1, _68_2592), (a2, _68_2596)) -> begin
(let _149_1254 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _149_1253 -> FStar_TypeChecker_Common.TProb (_149_1253)) _149_1254))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1822 "FStar.TypeChecker.Rel.fst"
let guard = (let _149_1256 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _149_1256))
in (
# 1823 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _149_1257 = (solve_prob orig None [] wl)
in (solve env _149_1257))
end else begin
(
# 1827 "FStar.TypeChecker.Rel.fst"
let _68_2602 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1259 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1258 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _149_1259 (rel_to_string problem.FStar_TypeChecker_Common.relation) _149_1258)))
end else begin
()
end
in (
# 1832 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1833 "FStar.TypeChecker.Rel.fst"
let _68_2607 = (c1, c2)
in (match (_68_2607) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_68_2609), FStar_Syntax_Syntax.Total (_68_2612)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _149_1260 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _149_1260 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _149_1262 = (
# 1845 "FStar.TypeChecker.Rel.fst"
let _68_2640 = problem
in (let _149_1261 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _68_2640.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _149_1261; FStar_TypeChecker_Common.relation = _68_2640.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _68_2640.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _68_2640.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2640.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2640.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2640.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2640.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2640.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1262 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _149_1264 = (
# 1849 "FStar.TypeChecker.Rel.fst"
let _68_2656 = problem
in (let _149_1263 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _68_2656.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _68_2656.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _68_2656.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _149_1263; FStar_TypeChecker_Common.element = _68_2656.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _68_2656.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _68_2656.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _68_2656.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _68_2656.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _68_2656.FStar_TypeChecker_Common.rank}))
in (solve_c env _149_1264 wl))
end
| (FStar_Syntax_Syntax.Comp (_68_2659), FStar_Syntax_Syntax.Comp (_68_2662)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _149_1265 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _149_1265 wl))
end else begin
(
# 1855 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1856 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 1860 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 1861 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 1862 "FStar.TypeChecker.Rel.fst"
let _68_2669 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _149_1268 = (let _149_1267 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1266 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _149_1267 _149_1266)))
in (giveup env _149_1268 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1869 "FStar.TypeChecker.Rel.fst"
let _68_2687 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _68_2680)::(wlp1, _68_2676)::[] -> begin
(wp1, wlp1)
end
| _68_2684 -> begin
(let _149_1270 = (let _149_1269 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _149_1269))
in (FStar_All.failwith _149_1270))
end)
in (match (_68_2687) with
| (wp, wlp) -> begin
(
# 1872 "FStar.TypeChecker.Rel.fst"
let c1 = (let _149_1276 = (let _149_1275 = (let _149_1271 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _149_1271))
in (let _149_1274 = (let _149_1273 = (let _149_1272 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _149_1272))
in (_149_1273)::[])
in (_149_1275)::_149_1274))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _149_1276; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 1879 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _68_26 -> (match (_68_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _68_2694 -> begin
false
end))))
in (
# 1880 "FStar.TypeChecker.Rel.fst"
let _68_2715 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _68_2700)::_68_2697, (wp2, _68_2707)::_68_2704) -> begin
(wp1, wp2)
end
| _68_2712 -> begin
(let _149_1280 = (let _149_1279 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _149_1278 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _149_1279 _149_1278)))
in (FStar_All.failwith _149_1280))
end)
in (match (_68_2715) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _149_1281 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _149_1281 wl))
end else begin
(
# 1887 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 1888 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 1890 "FStar.TypeChecker.Rel.fst"
let _68_2717 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _149_1291 = (let _149_1290 = (let _149_1289 = (let _149_1283 = (let _149_1282 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_149_1282)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1283 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _149_1288 = (let _149_1287 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _149_1286 = (let _149_1285 = (let _149_1284 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1284))
in (_149_1285)::[])
in (_149_1287)::_149_1286))
in (_149_1289, _149_1288)))
in FStar_Syntax_Syntax.Tm_app (_149_1290))
in (FStar_Syntax_Syntax.mk _149_1291 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 1894 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _149_1307 = (let _149_1306 = (let _149_1305 = (let _149_1293 = (let _149_1292 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1292)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1293 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _149_1304 = (let _149_1303 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1302 = (let _149_1301 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _149_1300 = (let _149_1299 = (let _149_1295 = (let _149_1294 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _149_1294 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1295))
in (let _149_1298 = (let _149_1297 = (let _149_1296 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _149_1296))
in (_149_1297)::[])
in (_149_1299)::_149_1298))
in (_149_1301)::_149_1300))
in (_149_1303)::_149_1302))
in (_149_1305, _149_1304)))
in FStar_Syntax_Syntax.Tm_app (_149_1306))
in (FStar_Syntax_Syntax.mk _149_1307 None r))
in (let _149_1316 = (let _149_1315 = (let _149_1314 = (let _149_1309 = (let _149_1308 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_149_1308)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _149_1309 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _149_1313 = (let _149_1312 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _149_1311 = (let _149_1310 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_149_1310)::[])
in (_149_1312)::_149_1311))
in (_149_1314, _149_1313)))
in FStar_Syntax_Syntax.Tm_app (_149_1315))
in (FStar_Syntax_Syntax.mk _149_1316 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 1901 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _149_1318 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _149_1317 -> FStar_TypeChecker_Common.TProb (_149_1317)) _149_1318))
in (
# 1902 "FStar.TypeChecker.Rel.fst"
let wl = (let _149_1322 = (let _149_1321 = (let _149_1320 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _149_1320 g))
in (FStar_All.pipe_left (fun _149_1319 -> Some (_149_1319)) _149_1321))
in (solve_prob orig _149_1322 [] wl))
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

# 1909 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _149_1326 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _68_2733 -> (match (_68_2733) with
| (_68_2725, u, _68_2728, _68_2730, _68_2732) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _149_1326 (FStar_String.concat ", "))))

# 1911 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _68_2740 -> begin
(
# 1915 "FStar.TypeChecker.Rel.fst"
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
# 1922 "FStar.TypeChecker.Rel.fst"
let carry = (let _149_1332 = (FStar_List.map (fun _68_2748 -> (match (_68_2748) with
| (_68_2746, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _149_1332 (FStar_String.concat ",\n")))
in (
# 1923 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1929 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1931 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1933 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_2757; FStar_TypeChecker_Env.implicits = _68_2755} -> begin
true
end
| _68_2762 -> begin
false
end))

# 1937 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 1939 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 1943 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _68_2780 -> begin
(FStar_All.failwith "impossible")
end)
in (let _149_1348 = (
# 1946 "FStar.TypeChecker.Rel.fst"
let _68_2782 = g
in (let _149_1347 = (let _149_1346 = (let _149_1345 = (let _149_1344 = (FStar_Syntax_Syntax.mk_binder x)
in (_149_1344)::[])
in (u_abs _149_1345 f))
in (FStar_All.pipe_left (fun _149_1343 -> FStar_TypeChecker_Common.NonTrivial (_149_1343)) _149_1346))
in {FStar_TypeChecker_Env.guard_f = _149_1347; FStar_TypeChecker_Env.deferred = _68_2782.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2782.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2782.FStar_TypeChecker_Env.implicits}))
in Some (_149_1348)))
end))

# 1948 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1950 "FStar.TypeChecker.Rel.fst"
let _68_2789 = g
in (let _149_1359 = (let _149_1358 = (let _149_1357 = (let _149_1356 = (let _149_1355 = (let _149_1354 = (FStar_Syntax_Syntax.as_arg e)
in (_149_1354)::[])
in (f, _149_1355))
in FStar_Syntax_Syntax.Tm_app (_149_1356))
in (FStar_Syntax_Syntax.mk _149_1357 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _149_1353 -> FStar_TypeChecker_Common.NonTrivial (_149_1353)) _149_1358))
in {FStar_TypeChecker_Env.guard_f = _149_1359; FStar_TypeChecker_Env.deferred = _68_2789.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2789.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2789.FStar_TypeChecker_Env.implicits}))
end))

# 1952 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_68_2794) -> begin
(FStar_All.failwith "impossible")
end))

# 1956 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _149_1366 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_149_1366))
end))

# 1961 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2812 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 1965 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 1969 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 1971 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _149_1389 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _149_1389; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 1975 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 1976 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 1978 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1980 "FStar.TypeChecker.Rel.fst"
let _68_2839 = g
in (let _149_1404 = (let _149_1403 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _149_1403 (fun _149_1402 -> FStar_TypeChecker_Common.NonTrivial (_149_1402))))
in {FStar_TypeChecker_Env.guard_f = _149_1404; FStar_TypeChecker_Env.deferred = _68_2839.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2839.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2839.FStar_TypeChecker_Env.implicits}))
end))

# 1985 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 1986 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1412 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _149_1411 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _149_1412 (rel_to_string rel) _149_1411)))
end else begin
"TOP"
end
in (
# 1991 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 1994 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 1995 "FStar.TypeChecker.Rel.fst"
let x = (let _149_1423 = (let _149_1422 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _149_1421 -> Some (_149_1421)) _149_1422))
in (FStar_Syntax_Syntax.new_bv _149_1423 t1))
in (
# 1996 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 1997 "FStar.TypeChecker.Rel.fst"
let p = (let _149_1427 = (let _149_1425 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _149_1424 -> Some (_149_1424)) _149_1425))
in (let _149_1426 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _149_1427 _149_1426)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2000 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2001 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2001 "FStar.TypeChecker.Rel.fst"
let _68_2859 = probs
in {attempting = _68_2859.attempting; wl_deferred = _68_2859.wl_deferred; ctr = _68_2859.ctr; defer_ok = false; smt_ok = _68_2859.smt_ok; tcenv = _68_2859.tcenv})
end else begin
probs
end
in (
# 2002 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2003 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2006 "FStar.TypeChecker.Rel.fst"
let _68_2866 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2009 "FStar.TypeChecker.Rel.fst"
let _68_2872 = (FStar_Unionfind.rollback tx)
in (
# 2010 "FStar.TypeChecker.Rel.fst"
let _68_2874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _149_1439 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _149_1439))
end else begin
()
end
in (err (d, s))))
end)))))

# 2014 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2017 "FStar.TypeChecker.Rel.fst"
let _68_2881 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1444 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _149_1444))
end else begin
()
end
in (
# 2018 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2019 "FStar.TypeChecker.Rel.fst"
let _68_2884 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _149_1445 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _149_1445))
end else begin
()
end
in (
# 2020 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _149_1446 = (FStar_Syntax_Util.unmeta f)
in _149_1446.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _68_2889 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2023 "FStar.TypeChecker.Rel.fst"
let _68_2891 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _68_2891.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_2891.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_2891.FStar_TypeChecker_Env.implicits})))))
end))

# 2025 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _149_1458 = (let _149_1457 = (let _149_1456 = (let _149_1455 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _149_1455 (fun _149_1454 -> FStar_TypeChecker_Common.NonTrivial (_149_1454))))
in {FStar_TypeChecker_Env.guard_f = _149_1456; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _149_1457))
in (FStar_All.pipe_left (fun _149_1453 -> Some (_149_1453)) _149_1458))
end))

# 2030 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2031 "FStar.TypeChecker.Rel.fst"
let _68_2902 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1466 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1465 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _149_1466 _149_1465)))
end else begin
()
end
in (
# 2033 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1469 = (let _149_1468 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _149_1468))
in (FStar_All.pipe_left (fun _149_1467 -> FStar_TypeChecker_Common.TProb (_149_1467)) _149_1469))
in (
# 2034 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1471 = (solve_and_commit env (singleton env prob) (fun _68_2905 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1471))
in g))))

# 2037 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _149_1481 = (let _149_1480 = (let _149_1479 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1478 = (FStar_TypeChecker_Env.get_range env)
in (_149_1479, _149_1478)))
in FStar_Syntax_Syntax.Error (_149_1480))
in (Prims.raise _149_1481))
end
| Some (g) -> begin
(
# 2041 "FStar.TypeChecker.Rel.fst"
let _68_2914 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1484 = (FStar_Syntax_Print.term_to_string t1)
in (let _149_1483 = (FStar_Syntax_Print.term_to_string t2)
in (let _149_1482 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _149_1484 _149_1483 _149_1482))))
end else begin
()
end
in g)
end))

# 2048 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2049 "FStar.TypeChecker.Rel.fst"
let _68_2919 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1492 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1491 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _149_1492 _149_1491)))
end else begin
()
end
in (
# 2051 "FStar.TypeChecker.Rel.fst"
let _68_2923 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_68_2923) with
| (prob, x) -> begin
(
# 2052 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1494 = (solve_and_commit env (singleton env prob) (fun _68_2924 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1494))
in (
# 2053 "FStar.TypeChecker.Rel.fst"
let _68_2927 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _149_1498 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _149_1497 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _149_1496 = (let _149_1495 = (FStar_Util.must g)
in (guard_to_string env _149_1495))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _149_1498 _149_1497 _149_1496))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2061 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _149_1505 = (let _149_1504 = (let _149_1503 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _149_1502 = (FStar_TypeChecker_Env.get_range env)
in (_149_1503, _149_1502)))
in FStar_Syntax_Syntax.Error (_149_1504))
in (Prims.raise _149_1505)))

# 2065 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2066 "FStar.TypeChecker.Rel.fst"
let _68_2935 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1513 = (FStar_Syntax_Print.comp_to_string c1)
in (let _149_1512 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _149_1513 _149_1512)))
end else begin
()
end
in (
# 2068 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2069 "FStar.TypeChecker.Rel.fst"
let prob = (let _149_1516 = (let _149_1515 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _149_1515 "sub_comp"))
in (FStar_All.pipe_left (fun _149_1514 -> FStar_TypeChecker_Common.CProb (_149_1514)) _149_1516))
in (let _149_1518 = (solve_and_commit env (singleton env prob) (fun _68_2939 -> None))
in (FStar_All.pipe_left (with_guard env prob) _149_1518))))))

# 2073 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2074 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2075 "FStar.TypeChecker.Rel.fst"
let _68_2948 = (FStar_Unionfind.rollback tx)
in (
# 2076 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _149_1536 = (let _149_1535 = (let _149_1534 = (let _149_1532 = (FStar_Syntax_Print.univ_to_string u1)
in (let _149_1531 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _149_1532 _149_1531 msg)))
in (let _149_1533 = (FStar_TypeChecker_Env.get_range env)
in (_149_1534, _149_1533)))
in FStar_Syntax_Syntax.Error (_149_1535))
in (Prims.raise _149_1536)))))
in (
# 2085 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2088 "FStar.TypeChecker.Rel.fst"
let _68_2964 = hd
in (match (_68_2964) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _149_1543 = (insert uv u1 tl)
in (hd)::_149_1543)
end
end))
end))
in (
# 2093 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2096 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2099 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _149_1548 = (insert uv u1 out)
in (group_by _149_1548 rest))
end)
end
| _68_2979 -> begin
None
end))
end))
in (
# 2106 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _68_2981 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _68_2984 -> begin
(
# 2111 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2111 "FStar.TypeChecker.Rel.fst"
let _68_2985 = (empty_worklist env)
in {attempting = _68_2985.attempting; wl_deferred = _68_2985.wl_deferred; ctr = _68_2985.ctr; defer_ok = true; smt_ok = _68_2985.smt_ok; tcenv = _68_2985.tcenv})
in (
# 2112 "FStar.TypeChecker.Rel.fst"
let _68_3025 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _68_2990 -> (match (_68_2990) with
| (u1, u2) -> begin
(
# 2113 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2114 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _68_2995 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2120 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _68_3005 -> begin
(u1)::[]
end)
in (
# 2123 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _68_3010 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _68_27 -> (match (_68_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2129 "FStar.TypeChecker.Rel.fst"
let _68_3017 = (FStar_Syntax_Util.univ_kernel u)
in (match (_68_3017) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2131 "FStar.TypeChecker.Rel.fst"
let _68_3021 = (FStar_Syntax_Util.univ_kernel u')
in (match (_68_3021) with
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
| USolved (_68_3023) -> begin
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
# 2142 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2142 "FStar.TypeChecker.Rel.fst"
let _68_3029 = (empty_worklist env)
in {attempting = _68_3029.attempting; wl_deferred = _68_3029.wl_deferred; ctr = _68_3029.ctr; defer_ok = false; smt_ok = _68_3029.smt_ok; tcenv = _68_3029.tcenv})
in (
# 2143 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _68_3044 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2155 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2156 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2157 "FStar.TypeChecker.Rel.fst"
let _68_3049 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2160 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2161 "FStar.TypeChecker.Rel.fst"
let fail = (fun _68_3056 -> (match (_68_3056) with
| (d, s) -> begin
(
# 2162 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2164 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2165 "FStar.TypeChecker.Rel.fst"
let _68_3059 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1569 = (wl_to_string wl)
in (let _149_1568 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _149_1569 _149_1568)))
end else begin
()
end
in (
# 2167 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2168 "FStar.TypeChecker.Rel.fst"
let _68_3063 = g
in {FStar_TypeChecker_Env.guard_f = _68_3063.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _68_3063.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3063.FStar_TypeChecker_Env.implicits})
end
| _68_3066 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2170 "FStar.TypeChecker.Rel.fst"
let _68_3068 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2171 "FStar.TypeChecker.Rel.fst"
let _68_3070 = g
in {FStar_TypeChecker_Env.guard_f = _68_3070.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3070.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _68_3070.FStar_TypeChecker_Env.implicits})))))))

# 2173 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2174 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2175 "FStar.TypeChecker.Rel.fst"
let _68_3084 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2179 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2183 "FStar.TypeChecker.Rel.fst"
let _68_3082 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _149_1576 = (FStar_TypeChecker_Env.get_range env)
in (let _149_1575 = (let _149_1574 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _149_1574))
in (FStar_TypeChecker_Errors.diag _149_1576 _149_1575)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (
# 2188 "FStar.TypeChecker.Rel.fst"
let _68_3086 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_3086.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3086.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3086.FStar_TypeChecker_Env.implicits}))))

# 2190 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2191 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _68_3093 -> begin
false
end))
in (
# 2194 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _68_3097 implicits -> (match (_68_3097) with
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
# 2198 "FStar.TypeChecker.Rel.fst"
let _68_3108 = hd
in (match (_68_3108) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2201 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2202 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2203 "FStar.TypeChecker.Rel.fst"
let _68_3111 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _149_1587 = (FStar_Syntax_Print.uvar_to_string u)
in (let _149_1586 = (FStar_Syntax_Print.term_to_string tm)
in (let _149_1585 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _149_1587 _149_1586 _149_1585))))
end else begin
()
end
in (
# 2206 "FStar.TypeChecker.Rel.fst"
let _68_3118 = (env.FStar_TypeChecker_Env.type_of (
# 2206 "FStar.TypeChecker.Rel.fst"
let _68_3113 = env
in {FStar_TypeChecker_Env.solver = _68_3113.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _68_3113.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _68_3113.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _68_3113.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _68_3113.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _68_3113.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _68_3113.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _68_3113.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _68_3113.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _68_3113.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _68_3113.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _68_3113.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _68_3113.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _68_3113.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _68_3113.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _68_3113.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _68_3113.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _68_3113.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _68_3113.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _68_3113.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _68_3113.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_68_3118) with
| (_68_3116, g) -> begin
(
# 2207 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2208 "FStar.TypeChecker.Rel.fst"
let _68_3119 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _68_3119.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3119.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _68_3119.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2210 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl)))
end)))))
end
end))
end)
end))
in (
# 2212 "FStar.TypeChecker.Rel.fst"
let _68_3123 = g
in (let _149_1588 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _68_3123.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3123.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _68_3123.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _149_1588})))))

# 2214 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2215 "FStar.TypeChecker.Rel.fst"
let g = (let _149_1593 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _149_1593 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _149_1594 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _149_1594))
end
| (_68_3132, _68_3134, _68_3136, _68_3138, r)::_68_3130 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2220 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2222 "FStar.TypeChecker.Rel.fst"
let _68_3144 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _68_3144.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _68_3144.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _68_3144.FStar_TypeChecker_Env.implicits}))






open Prims
# 65 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _151_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _151_8 Prims.op_Negation)))))
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
| _69_38 -> begin
(
# 73 "FStar.TypeChecker.Rel.fst"
let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (
# 74 "FStar.TypeChecker.Rel.fst"
let k' = (let _151_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _151_9))
in (
# 75 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _151_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_151_10, uv)))))
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
| TERM (_69_44) -> begin
_69_44
end))

# 84 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_69_47) -> begin
_69_47
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
| Success (_69_57) -> begin
_69_57
end))

# 99 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_69_60) -> begin
_69_60
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
let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _69_1 -> (match (_69_1) with
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
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _69_2 -> (match (_69_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _151_109 = (let _151_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _151_107 = (let _151_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _151_105 = (let _151_104 = (let _151_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _151_102 = (let _151_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _151_100 = (let _151_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _151_98 = (let _151_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_151_97)::[])
in (_151_99)::_151_98))
in (_151_101)::_151_100))
in (_151_103)::_151_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_151_104)
in (_151_106)::_151_105))
in (_151_108)::_151_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _151_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _151_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _151_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _151_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _151_110)))
end))

# 140 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _69_3 -> (match (_69_3) with
| UNIV (u, t) -> begin
(
# 142 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _151_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _151_116 FStar_Util.string_of_int))
end
in (let _151_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _151_117)))
end
| TERM ((u, _69_84), t) -> begin
(
# 146 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _151_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _151_118 FStar_Util.string_of_int))
end
in (let _151_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _151_119)))
end))

# 148 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _151_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _151_124 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _151_134 = (let _151_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _151_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _151_134 (FStar_String.concat ", "))))

# 150 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _151_137 = (FStar_All.pipe_right args (FStar_List.map (fun _69_97 -> (match (_69_97) with
| (x, _69_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _151_137 (FStar_String.concat " "))))

# 159 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 167 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _69_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _69_101.wl_deferred; ctr = _69_101.ctr; defer_ok = _69_101.defer_ok; smt_ok = _69_101.smt_ok; tcenv = _69_101.tcenv}))

# 168 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _69_105 = (empty_worklist env)
in (let _151_146 = (FStar_List.map Prims.snd g)
in {attempting = _151_146; wl_deferred = _69_105.wl_deferred; ctr = _69_105.ctr; defer_ok = false; smt_ok = _69_105.smt_ok; tcenv = _69_105.tcenv})))

# 169 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _69_110 = wl
in {attempting = _69_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _69_110.ctr; defer_ok = _69_110.defer_ok; smt_ok = _69_110.smt_ok; tcenv = _69_110.tcenv}))

# 170 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 170 "FStar.TypeChecker.Rel.fst"
let _69_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _69_114.wl_deferred; ctr = _69_114.ctr; defer_ok = _69_114.defer_ok; smt_ok = _69_114.smt_ok; tcenv = _69_114.tcenv}))

# 172 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 173 "FStar.TypeChecker.Rel.fst"
let _69_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _151_163))
end else begin
()
end
in Failed ((prob, reason))))

# 183 "FStar.TypeChecker.Rel.fst"
let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _69_4 -> (match (_69_4) with
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
let _69_126 = p
in {FStar_TypeChecker_Common.pid = _69_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _69_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_126.FStar_TypeChecker_Common.rank}))

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 189 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _69_5 -> (match (_69_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _151_170 -> FStar_TypeChecker_Common.TProb (_151_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _151_171 -> FStar_TypeChecker_Common.CProb (_151_171)))
end))

# 192 "FStar.TypeChecker.Rel.fst"
let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _69_6 -> (match (_69_6) with
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
let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _69_7 -> (match (_69_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 199 "FStar.TypeChecker.Rel.fst"
let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _69_8 -> (match (_69_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 202 "FStar.TypeChecker.Rel.fst"
let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _69_9 -> (match (_69_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 205 "FStar.TypeChecker.Rel.fst"
let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _69_10 -> (match (_69_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 208 "FStar.TypeChecker.Rel.fst"
let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _69_11 -> (match (_69_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 211 "FStar.TypeChecker.Rel.fst"
let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _69_12 -> (match (_69_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 214 "FStar.TypeChecker.Rel.fst"
let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _69_13 -> (match (_69_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _151_190 -> FStar_TypeChecker_Common.TProb (_151_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _151_191 -> FStar_TypeChecker_Common.CProb (_151_191)) (invert p))
end))

# 217 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 218 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 219 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _69_176 -> (match (()) with
| () -> begin
(
# 220 "FStar.TypeChecker.Rel.fst"
let _69_177 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 222 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _151_204 = (next_pid ())
in (let _151_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _151_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _151_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 234 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 235 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _151_214 = (next_pid ())
in (let _151_213 = (let _151_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _151_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _151_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _151_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 248 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _151_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _151_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 260 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 264 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _151_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _151_232 = (prob_to_string env d)
in (let _151_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _151_233 _151_232 _151_231 s)))))

# 278 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _69_14 -> (match (_69_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _69_218 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _69_221), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 286 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _69_15 -> (match (_69_15) with
| UNIV (_69_230) -> begin
None
end
| TERM ((u, _69_234), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 290 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _69_16 -> (match (_69_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _69_247 -> begin
None
end))))

# 302 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _151_252 = (let _151_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _151_251))
in (FStar_Syntax_Subst.compress _151_252)))

# 303 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _151_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _151_257)))

# 304 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _151_260 = (sn env (Prims.fst t))
in (_151_260, (Prims.snd t))))

# 305 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _69_258 -> (match (_69_258) with
| (x, imp) -> begin
(let _151_267 = (
# 306 "FStar.TypeChecker.Rel.fst"
let _69_259 = x
in (let _151_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _69_259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_266}))
in (_151_267, imp))
end)))))

# 312 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 314 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _151_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_151_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _151_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_151_275))
end
| _69_271 -> begin
u
end)))
in (let _151_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _151_276))))

# 325 "FStar.TypeChecker.Rel.fst"
let normalize_refinement = (fun steps env wl t0 -> (let _151_281 = (whnf env t0)
in (FStar_TypeChecker_Normalize.normalize_refinement steps env _151_281)))

# 327 "FStar.TypeChecker.Rel.fst"
let base_and_refinement = (fun env wl t1 -> (
# 328 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _69_291; FStar_Syntax_Syntax.pos = _69_289; FStar_Syntax_Syntax.vars = _69_287} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _151_291 = (let _151_290 = (FStar_Syntax_Print.term_to_string tt)
in (let _151_289 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _151_290 _151_289)))
in (FStar_All.failwith _151_291))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(
# 343 "FStar.TypeChecker.Rel.fst"
let _69_309 = (let _151_292 = (normalize_refinement [] env wl t1)
in (aux true _151_292))
in (match (_69_309) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _69_312 -> begin
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
(let _151_295 = (let _151_294 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_293 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _151_294 _151_293)))
in (FStar_All.failwith _151_295))
end))
in (let _151_296 = (whnf env t1)
in (aux false _151_296))))

# 367 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _151_301 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _151_301 Prims.fst)))

# 369 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _151_304 = (FStar_Syntax_Syntax.null_bv t)
in (_151_304, FStar_Syntax_Util.t_true)))

# 371 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 372 "FStar.TypeChecker.Rel.fst"
let _69_358 = (base_and_refinement env wl t)
in (match (_69_358) with
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
let force_refinement = (fun _69_366 -> (match (_69_366) with
| (t_base, refopt) -> begin
(
# 378 "FStar.TypeChecker.Rel.fst"
let _69_374 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_69_374) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 391 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _69_17 -> (match (_69_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _151_317 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _151_316 = (let _151_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _151_313))
in (let _151_315 = (let _151_314 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _151_314))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _151_317 _151_316 (rel_to_string p.FStar_TypeChecker_Common.relation) _151_315))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _151_320 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _151_319 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _151_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _151_320 _151_319 (rel_to_string p.FStar_TypeChecker_Common.relation) _151_318))))
end))

# 406 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _151_326 = (let _151_325 = (let _151_324 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _69_387 -> (match (_69_387) with
| (_69_383, _69_385, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _151_324))
in (FStar_List.map (wl_prob_to_string wl) _151_325))
in (FStar_All.pipe_right _151_326 (FStar_String.concat "\n\t"))))

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
let _69_402 = (p_guard prob)
in (match (_69_402) with
| (_69_400, uv) -> begin
(
# 423 "FStar.TypeChecker.Rel.fst"
let _69_415 = (match ((let _151_341 = (FStar_Syntax_Subst.compress uv)
in _151_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 425 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 426 "FStar.TypeChecker.Rel.fst"
let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _151_343 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _151_343 Prims.op_Negation)))))
in (
# 427 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs bs phi)
in (
# 428 "FStar.TypeChecker.Rel.fst"
let _69_411 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _151_346 = (FStar_Util.string_of_int (p_pid prob))
in (let _151_345 = (FStar_Syntax_Print.term_to_string uv)
in (let _151_344 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _151_346 _151_345 _151_344))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _69_414 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 435 "FStar.TypeChecker.Rel.fst"
let _69_417 = (commit uvis)
in (
# 436 "FStar.TypeChecker.Rel.fst"
let _69_419 = wl
in {attempting = _69_419.attempting; wl_deferred = _69_419.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _69_419.defer_ok; smt_ok = _69_419.smt_ok; tcenv = _69_419.tcenv})))
end))))

# 438 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 439 "FStar.TypeChecker.Rel.fst"
let _69_424 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_355 = (FStar_Util.string_of_int pid)
in (let _151_354 = (let _151_353 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _151_353 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _151_355 _151_354)))
end else begin
()
end
in (
# 441 "FStar.TypeChecker.Rel.fst"
let _69_426 = (commit sol)
in (
# 442 "FStar.TypeChecker.Rel.fst"
let _69_428 = wl
in {attempting = _69_428.attempting; wl_deferred = _69_428.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _69_428.defer_ok; smt_ok = _69_428.smt_ok; tcenv = _69_428.tcenv}))))

# 444 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 445 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_69_438, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _151_368 = (FStar_Syntax_Util.mk_conj t f)
in Some (_151_368))
end))
in (
# 449 "FStar.TypeChecker.Rel.fst"
let _69_450 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_371 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _151_370 = (let _151_369 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _151_369 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _151_371 _151_370)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 461 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _151_381 = (let _151_379 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _151_379 FStar_Util.set_elements))
in (FStar_All.pipe_right _151_381 (FStar_Util.for_some (fun _69_459 -> (match (_69_459) with
| (uv, _69_458) -> begin
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
(let _151_388 = (let _151_387 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _151_386 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _151_387 _151_386)))
in Some (_151_388))
end
in (occurs_ok, msg))))

# 476 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 477 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 478 "FStar.TypeChecker.Rel.fst"
let _69_474 = (occurs_check env wl uk t)
in (match (_69_474) with
| (occurs_ok, msg) -> begin
(let _151_420 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _151_420, (msg, fvs, fvs_t)))
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
let _69_492 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _69_484 _69_487 -> (match ((_69_484, _69_487)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _151_429 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _151_429)) then begin
(isect, isect_set)
end else begin
(
# 491 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _151_430 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _151_430))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_69_492) with
| (isect, _69_491) -> begin
(FStar_List.rev isect)
end)))))

# 498 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _69_498 _69_502 -> (match ((_69_498, _69_502)) with
| ((a, _69_497), (b, _69_501)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 502 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 503 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _69_512 -> (match (_69_512) with
| (b, _69_511) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _69_514 -> begin
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
let _69_523 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_445 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _151_445))
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
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _69_537; FStar_Syntax_Syntax.pos = _69_535; FStar_Syntax_Syntax.vars = _69_533}, args) -> begin
(t, uv, k, args)
end
| _69_547 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 525 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 526 "FStar.TypeChecker.Rel.fst"
let _69_554 = (destruct_flex_t t)
in (match (_69_554) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _69_558 -> begin
((t, uv, k, args), None)
end)
end)))

# 600 "FStar.TypeChecker.Rel.fst"
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

# 605 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _69_18 -> (match (_69_18) with
| MisMatch -> begin
MisMatch
end
| _69_562 -> begin
HeadMatch
end))

# 609 "FStar.TypeChecker.Rel.fst"
let rec head_matches : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun t1 t2 -> (match ((let _151_461 = (let _151_458 = (FStar_Syntax_Util.unmeta t1)
in _151_458.FStar_Syntax_Syntax.n)
in (let _151_460 = (let _151_459 = (FStar_Syntax_Util.unmeta t2)
in _151_459.FStar_Syntax_Syntax.n)
in (_151_461, _151_460)))) with
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _69_577), FStar_Syntax_Syntax.Tm_uinst (g, _69_582)) -> begin
(let _151_462 = (head_matches f g)
in (FStar_All.pipe_right _151_462 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _69_593), FStar_Syntax_Syntax.Tm_uvar (uv', _69_598)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _69_604), FStar_Syntax_Syntax.Tm_refine (y, _69_609)) -> begin
(let _151_463 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_463 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _69_615), _69_619) -> begin
(let _151_464 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _151_464 head_match))
end
| (_69_622, FStar_Syntax_Syntax.Tm_refine (x, _69_625)) -> begin
(let _151_465 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _151_465 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _69_645), FStar_Syntax_Syntax.Tm_app (head', _69_650)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _69_656), _69_660) -> begin
(head_matches head t2)
end
| (_69_663, FStar_Syntax_Syntax.Tm_app (head, _69_666)) -> begin
(head_matches t1 head)
end
| _69_671 -> begin
MisMatch
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
let fail = (fun _69_682 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (
# 635 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 2) then begin
(fail ())
end else begin
if (d = 1) then begin
(
# 640 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t1)
in (
# 641 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t2)
in (aux 2 t1' t2')))
end else begin
(
# 643 "FStar.TypeChecker.Rel.fst"
let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t1)
in (
# 644 "FStar.TypeChecker.Rel.fst"
let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t2)
in (aux (d + 1) t1 t2)))
end
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

# 650 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 651 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 650 "FStar.TypeChecker.Rel.fst"
let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_69_695) -> begin
_69_695
end))

# 651 "FStar.TypeChecker.Rel.fst"
let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_69_698) -> begin
_69_698
end))

# 652 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 654 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun env t -> (
# 655 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 656 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 659 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 660 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_69_713, imp), T (t)) -> begin
(t, imp)
end
| _69_720 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 665 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _69_725 -> (match (_69_725) with
| (t, _69_724) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 671 "FStar.TypeChecker.Rel.fst"
let fail = (fun _69_732 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 672 "FStar.TypeChecker.Rel.fst"
let _69_735 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_69_735) with
| (bs, c) -> begin
(
# 674 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 675 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 676 "FStar.TypeChecker.Rel.fst"
let _69_752 = x
in {FStar_Syntax_Syntax.ppname = _69_752.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_752.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _69_760 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 681 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _69_19 -> (match (_69_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(
# 684 "FStar.TypeChecker.Rel.fst"
let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _151_559 = (decompose [] bs)
in (rebuild, matches, _151_559))))
end)))
end
| _69_770 -> begin
(
# 692 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _69_20 -> (match (_69_20) with
| [] -> begin
t
end
| _69_774 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 698 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _69_21 -> (match (_69_21) with
| T (t) -> begin
t
end
| _69_781 -> begin
(FStar_All.failwith "Impossible")
end))

# 702 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _69_22 -> (match (_69_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _69_786 -> begin
(FStar_All.failwith "Impossible")
end))

# 706 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 711 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 712 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 713 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_69_799, variance, T (ti)) -> begin
(
# 716 "FStar.TypeChecker.Rel.fst"
let k = (
# 717 "FStar.TypeChecker.Rel.fst"
let _69_807 = (FStar_Syntax_Util.type_u ())
in (match (_69_807) with
| (t, _69_806) -> begin
(let _151_581 = (new_uvar r scope t)
in (Prims.fst _151_581))
end))
in (
# 719 "FStar.TypeChecker.Rel.fst"
let _69_811 = (new_uvar r scope k)
in (match (_69_811) with
| (gi_xs, gi) -> begin
(
# 720 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _69_814 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _151_584 = (let _151_583 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _151_582 -> FStar_TypeChecker_Common.TProb (_151_582)) _151_583))
in (T (gi_xs), _151_584)))
end)))
end
| (_69_817, _69_819, C (_69_821)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 728 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 732 "FStar.TypeChecker.Rel.fst"
let _69_899 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _69_839; FStar_Syntax_Syntax.pos = _69_837; FStar_Syntax_Syntax.vars = _69_835})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _151_593 = (let _151_592 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _151_591 -> C (_151_591)) _151_592))
in (_151_593, (prob)::[]))
end
| _69_850 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _69_858; FStar_Syntax_Syntax.pos = _69_856; FStar_Syntax_Syntax.vars = _69_854})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _151_596 = (let _151_595 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _151_594 -> C (_151_594)) _151_595))
in (_151_596, (prob)::[]))
end
| _69_869 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_69_871, _69_873, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _69_879; FStar_Syntax_Syntax.pos = _69_877; FStar_Syntax_Syntax.vars = _69_875})) -> begin
(
# 746 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 747 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 748 "FStar.TypeChecker.Rel.fst"
let _69_890 = (let _151_598 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _151_598 FStar_List.unzip))
in (match (_69_890) with
| (tcs, sub_probs) -> begin
(
# 749 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _151_603 = (let _151_602 = (let _151_599 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _151_599 un_T))
in (let _151_601 = (let _151_600 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _151_600 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _151_602; FStar_Syntax_Syntax.effect_args = _151_601; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _151_603))
in (C (gi_xs), sub_probs))
end))))
end
| _69_893 -> begin
(
# 758 "FStar.TypeChecker.Rel.fst"
let _69_896 = (sub_prob scope args q)
in (match (_69_896) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_69_899) with
| (tc, probs) -> begin
(
# 761 "FStar.TypeChecker.Rel.fst"
let _69_912 = (match (q) with
| (Some (b), _69_903, _69_905) -> begin
(let _151_605 = (let _151_604 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_151_604)::args)
in (Some (b), (b)::scope, _151_605))
end
| _69_908 -> begin
(None, scope, args)
end)
in (match (_69_912) with
| (bopt, scope, args) -> begin
(
# 765 "FStar.TypeChecker.Rel.fst"
let _69_916 = (aux scope args qs)
in (match (_69_916) with
| (sub_probs, tcs, f) -> begin
(
# 766 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _151_608 = (let _151_607 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_151_607)
in (FStar_Syntax_Util.mk_conj_l _151_608))
end
| Some (b) -> begin
(let _151_612 = (let _151_611 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _151_610 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_151_611)::_151_610))
in (FStar_Syntax_Util.mk_conj_l _151_612))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 781 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 782 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 783 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _69_944), FStar_Syntax_Syntax.Tm_uvar (u2, _69_949)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _69_963 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _69_969 _69_973 -> (match ((_69_969, _69_973)) with
| ((a1, _69_968), (a2, _69_972)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 800 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 801 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 803 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 804 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 805 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 806 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 807 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 808 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 809 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 810 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 811 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 811 "FStar.TypeChecker.Rel.fst"
let _69_976 = p
in (let _151_634 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _151_633 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _69_976.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _151_634; FStar_TypeChecker_Common.relation = _69_976.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _151_633; FStar_TypeChecker_Common.element = _69_976.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_976.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_976.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_976.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_976.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_976.FStar_TypeChecker_Common.rank}))))

# 813 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _151_640 = (compress_tprob wl p)
in (FStar_All.pipe_right _151_640 (fun _151_639 -> FStar_TypeChecker_Common.TProb (_151_639))))
end
| FStar_TypeChecker_Common.CProb (_69_983) -> begin
p
end))

# 818 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 821 "FStar.TypeChecker.Rel.fst"
let prob = (let _151_645 = (compress_prob wl pr)
in (FStar_All.pipe_right _151_645 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 824 "FStar.TypeChecker.Rel.fst"
let _69_993 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_69_993) with
| (lh, _69_992) -> begin
(
# 825 "FStar.TypeChecker.Rel.fst"
let _69_997 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_69_997) with
| (rh, _69_996) -> begin
(
# 826 "FStar.TypeChecker.Rel.fst"
let _69_1053 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_69_999), FStar_Syntax_Syntax.Tm_uvar (_69_1002)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_69_1018), _69_1021) -> begin
(
# 833 "FStar.TypeChecker.Rel.fst"
let _69_1025 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_69_1025) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _69_1028 -> begin
(
# 837 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _151_647 = (
# 841 "FStar.TypeChecker.Rel.fst"
let _69_1030 = tp
in (let _151_646 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _69_1030.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_1030.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_1030.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _151_646; FStar_TypeChecker_Common.element = _69_1030.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1030.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1030.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1030.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1030.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_1030.FStar_TypeChecker_Common.rank}))
in (rank, _151_647)))
end)
end))
end
| (_69_1033, FStar_Syntax_Syntax.Tm_uvar (_69_1035)) -> begin
(
# 845 "FStar.TypeChecker.Rel.fst"
let _69_1040 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_69_1040) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _69_1043 -> begin
(let _151_649 = (
# 848 "FStar.TypeChecker.Rel.fst"
let _69_1044 = tp
in (let _151_648 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _69_1044.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _151_648; FStar_TypeChecker_Common.relation = _69_1044.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_1044.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_1044.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1044.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1044.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1044.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1044.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_1044.FStar_TypeChecker_Common.rank}))
in (refine_flex, _151_649))
end)
end))
end
| (_69_1047, _69_1049) -> begin
(rigid_rigid, tp)
end)
in (match (_69_1053) with
| (rank, tp) -> begin
(let _151_651 = (FStar_All.pipe_right (
# 853 "FStar.TypeChecker.Rel.fst"
let _69_1054 = tp
in {FStar_TypeChecker_Common.pid = _69_1054.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_1054.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_1054.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_1054.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_1054.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1054.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1054.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1054.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1054.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _151_650 -> FStar_TypeChecker_Common.TProb (_151_650)))
in (rank, _151_651))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _151_653 = (FStar_All.pipe_right (
# 855 "FStar.TypeChecker.Rel.fst"
let _69_1058 = cp
in {FStar_TypeChecker_Common.pid = _69_1058.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_1058.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_1058.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_1058.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_1058.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1058.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1058.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1058.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1058.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _151_652 -> FStar_TypeChecker_Common.CProb (_151_652)))
in (rigid_rigid, _151_653))
end)))

# 857 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 861 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _69_1065 probs -> (match (_69_1065) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 864 "FStar.TypeChecker.Rel.fst"
let _69_1073 = (rank wl hd)
in (match (_69_1073) with
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

# 880 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 881 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 882 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 880 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_69_1083) -> begin
_69_1083
end))

# 881 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_69_1086) -> begin
_69_1086
end))

# 882 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_69_1089) -> begin
_69_1089
end))

# 884 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 885 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 886 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 887 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 890 "FStar.TypeChecker.Rel.fst"
let _69_1105 = (FStar_Syntax_Util.univ_kernel u)
in (match (_69_1105) with
| (k, _69_1104) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _69_1109 -> begin
false
end)
end)))))
end
| _69_1111 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 896 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_69_1117), FStar_Syntax_Syntax.U_max (_69_1120)) -> begin
(let _151_725 = (let _151_724 = (FStar_Syntax_Print.univ_to_string u1)
in (let _151_723 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _151_724 _151_723)))
in UFailed (_151_725))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 903 "FStar.TypeChecker.Rel.fst"
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
| _69_1140 -> begin
(let _151_732 = (let _151_731 = (FStar_Syntax_Print.univ_to_string u1)
in (let _151_730 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _151_731 _151_730 msg)))
in UFailed (_151_732))
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
# 924 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 929 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _151_735 = (let _151_734 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _151_733 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _151_734 _151_733)))
in (try_umax_components u1 u2 _151_735))
end else begin
(let _151_736 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_151_736))
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
# 954 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 955 "FStar.TypeChecker.Rel.fst"
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

# 967 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 969 "FStar.TypeChecker.Rel.fst"
let _69_1235 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_779 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _151_779))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 973 "FStar.TypeChecker.Rel.fst"
let probs = (
# 973 "FStar.TypeChecker.Rel.fst"
let _69_1242 = probs
in {attempting = tl; wl_deferred = _69_1242.wl_deferred; ctr = _69_1242.ctr; defer_ok = _69_1242.defer_ok; smt_ok = _69_1242.smt_ok; tcenv = _69_1242.tcenv})
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
| (None, _69_1254, _69_1256) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _69_1260 -> begin
(
# 995 "FStar.TypeChecker.Rel.fst"
let _69_1269 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _69_1266 -> (match (_69_1266) with
| (c, _69_1263, _69_1265) -> begin
(c < probs.ctr)
end))))
in (match (_69_1269) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _151_782 = (FStar_List.map (fun _69_1275 -> (match (_69_1275) with
| (_69_1272, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_151_782))
end
| _69_1277 -> begin
(let _151_785 = (
# 1001 "FStar.TypeChecker.Rel.fst"
let _69_1278 = probs
in (let _151_784 = (FStar_All.pipe_right attempt (FStar_List.map (fun _69_1285 -> (match (_69_1285) with
| (_69_1281, _69_1283, y) -> begin
y
end))))
in {attempting = _151_784; wl_deferred = rest; ctr = _69_1278.ctr; defer_ok = _69_1278.defer_ok; smt_ok = _69_1278.smt_ok; tcenv = _69_1278.tcenv}))
in (solve env _151_785))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _151_791 = (solve_prob orig None [] wl)
in (solve env _151_791))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1015 "FStar.TypeChecker.Rel.fst"
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
| _69_1320 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _151_806 = (let _151_803 = (whnf env t1)
in _151_803.FStar_Syntax_Syntax.n)
in (let _151_805 = (let _151_804 = (whnf env t2)
in _151_804.FStar_Syntax_Syntax.n)
in (_151_806, _151_805)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _69_1326; FStar_Syntax_Syntax.pos = _69_1324; FStar_Syntax_Syntax.vars = _69_1322}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _69_1338; FStar_Syntax_Syntax.pos = _69_1336; FStar_Syntax_Syntax.vars = _69_1334}, us2)) -> begin
(
# 1030 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1031 "FStar.TypeChecker.Rel.fst"
let _69_1347 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _69_1362 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1044 "FStar.TypeChecker.Rel.fst"
let _69_1367 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_811 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _151_811 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1054 "FStar.TypeChecker.Rel.fst"
let _69_1372 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_815 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _151_815))
end else begin
()
end
in (
# 1056 "FStar.TypeChecker.Rel.fst"
let _69_1376 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_69_1376) with
| (u, args) -> begin
(
# 1057 "FStar.TypeChecker.Rel.fst"
let _69_1382 = (0, 1, 2, 3, 4)
in (match (_69_1382) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1058 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1060 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1061 "FStar.TypeChecker.Rel.fst"
let _69_1391 = (FStar_Syntax_Util.head_and_args t1)
in (match (_69_1391) with
| (h1, args1) -> begin
(
# 1062 "FStar.TypeChecker.Rel.fst"
let _69_1395 = (FStar_Syntax_Util.head_and_args t2)
in (match (_69_1395) with
| (h2, _69_1394) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _151_827 = (let _151_826 = (let _151_825 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _151_824 -> FStar_TypeChecker_Common.TProb (_151_824)) _151_825))
in (_151_826)::[])
in Some (_151_827))
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
| _69_1407 -> begin
None
end)
end))
end)))
in (
# 1078 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1080 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1084 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1085 "FStar.TypeChecker.Rel.fst"
let subst = (let _151_834 = (let _151_833 = (let _151_832 = (FStar_Syntax_Syntax.bv_to_name x)
in (0, _151_832))
in FStar_Syntax_Syntax.DB (_151_833))
in (_151_834)::[])
in (
# 1086 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1087 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _151_837 = (let _151_836 = (let _151_835 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _151_835))
in (_151_836, m))
in Some (_151_837))))))
end))
end
| (_69_1429, FStar_Syntax_Syntax.Tm_refine (y, _69_1432)) -> begin
(
# 1092 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _69_1442), _69_1446) -> begin
(
# 1099 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _69_1453 -> begin
(
# 1106 "FStar.TypeChecker.Rel.fst"
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
# 1112 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _69_1461) -> begin
(
# 1116 "FStar.TypeChecker.Rel.fst"
let _69_1486 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _69_23 -> (match (_69_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1120 "FStar.TypeChecker.Rel.fst"
let _69_1472 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_69_1472) with
| (u', _69_1471) -> begin
(match ((let _151_839 = (whnf env u')
in _151_839.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _69_1475) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _69_1479 -> begin
false
end)
end))
end
| _69_1481 -> begin
false
end)
end
| _69_1483 -> begin
false
end))))
in (match (_69_1486) with
| (upper_bounds, rest) -> begin
(
# 1129 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _69_1490 tps -> (match (_69_1490) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _151_844 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _151_844))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _69_1503 -> begin
None
end)
end))
in (match ((let _151_846 = (let _151_845 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_151_845, []))
in (make_upper_bound _151_846 upper_bounds))) with
| None -> begin
(
# 1140 "FStar.TypeChecker.Rel.fst"
let _69_1505 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1153 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1154 "FStar.TypeChecker.Rel.fst"
let _69_1515 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1155 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1155 "FStar.TypeChecker.Rel.fst"
let _69_1512 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _69_1512.wl_deferred; ctr = _69_1512.ctr; defer_ok = _69_1512.defer_ok; smt_ok = _69_1512.smt_ok; tcenv = _69_1512.tcenv})
in (let _151_847 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _151_847)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1157 "FStar.TypeChecker.Rel.fst"
let _69_1517 = wl
in {attempting = sub_probs; wl_deferred = _69_1517.wl_deferred; ctr = _69_1517.ctr; defer_ok = _69_1517.defer_ok; smt_ok = _69_1517.smt_ok; tcenv = _69_1517.tcenv}))) with
| Success (_69_1520) -> begin
(
# 1159 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1159 "FStar.TypeChecker.Rel.fst"
let _69_1522 = wl
in {attempting = rest; wl_deferred = _69_1522.wl_deferred; ctr = _69_1522.ctr; defer_ok = _69_1522.defer_ok; smt_ok = _69_1522.smt_ok; tcenv = _69_1522.tcenv})
in (
# 1160 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1161 "FStar.TypeChecker.Rel.fst"
let _69_1528 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _69_1531 -> begin
None
end)))
end))
end))
end
| _69_1533 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1171 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1174 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1175 "FStar.TypeChecker.Rel.fst"
let _69_1550 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_875 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _151_875))
end else begin
()
end
in (
# 1177 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1181 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1181 "FStar.TypeChecker.Rel.fst"
let _69_1564 = hd1
in (let _151_876 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _69_1564.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1564.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_876}))
in (
# 1182 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1182 "FStar.TypeChecker.Rel.fst"
let _69_1567 = hd2
in (let _151_877 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _69_1567.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_1567.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _151_877}))
in (
# 1183 "FStar.TypeChecker.Rel.fst"
let prob = (let _151_880 = (let _151_879 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _151_879 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _151_878 -> FStar_TypeChecker_Common.TProb (_151_878)) _151_880))
in (
# 1184 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1185 "FStar.TypeChecker.Rel.fst"
let subst = (let _151_884 = (let _151_882 = (let _151_881 = (FStar_Syntax_Syntax.bv_to_name hd1)
in (0, _151_881))
in FStar_Syntax_Syntax.DB (_151_882))
in (let _151_883 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (_151_884)::_151_883))
in (
# 1186 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1189 "FStar.TypeChecker.Rel.fst"
let phi = (let _151_886 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _151_885 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _151_886 _151_885)))
in (
# 1190 "FStar.TypeChecker.Rel.fst"
let _69_1579 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_888 = (FStar_Syntax_Print.term_to_string phi)
in (let _151_887 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _151_888 _151_887)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _69_1583 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1199 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1203 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _151_892 = (compress_tprob wl problem)
in (solve_t' env _151_892 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1210 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1213 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1214 "FStar.TypeChecker.Rel.fst"
let _69_1611 = (head_matches_delta env wl t1 t2)
in (match (_69_1611) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _69_1614) -> begin
(
# 1217 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_69_1619) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _69_1623) -> begin
(FStar_TypeChecker_Env.is_projector env tc.FStar_Syntax_Syntax.v)
end
| _69_1627 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1222 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1225 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1229 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _151_921 = (let _151_920 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _151_920 t2))
in (FStar_Syntax_Util.mk_forall x _151_921)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _151_922 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _151_922)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_69_1637, Some (t1, t2)) -> begin
(solve_t env (
# 1238 "FStar.TypeChecker.Rel.fst"
let _69_1643 = problem
in {FStar_TypeChecker_Common.pid = _69_1643.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _69_1643.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _69_1643.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1643.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1643.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1643.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1643.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_1643.FStar_TypeChecker_Common.rank}) wl)
end
| (_69_1646, None) -> begin
(
# 1241 "FStar.TypeChecker.Rel.fst"
let _69_1649 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_926 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_925 = (FStar_Syntax_Print.tag_of_term t1)
in (let _151_924 = (FStar_Syntax_Print.term_to_string t2)
in (let _151_923 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _151_926 _151_925 _151_924 _151_923)))))
end else begin
()
end
in (
# 1245 "FStar.TypeChecker.Rel.fst"
let _69_1653 = (FStar_Syntax_Util.head_and_args t1)
in (match (_69_1653) with
| (head, args) -> begin
(
# 1246 "FStar.TypeChecker.Rel.fst"
let _69_1656 = (FStar_Syntax_Util.head_and_args t2)
in (match (_69_1656) with
| (head', args') -> begin
(
# 1247 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _151_931 = (let _151_930 = (FStar_Syntax_Print.term_to_string head)
in (let _151_929 = (args_to_string args)
in (let _151_928 = (FStar_Syntax_Print.term_to_string head')
in (let _151_927 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _151_930 _151_929 _151_928 _151_927)))))
in (giveup env _151_931 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _151_932 = (solve_prob orig None [] wl)
in (solve env _151_932))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1268 "FStar.TypeChecker.Rel.fst"
let _69_1666 = (base_and_refinement env wl t1)
in (match (_69_1666) with
| (base1, refinement1) -> begin
(
# 1269 "FStar.TypeChecker.Rel.fst"
let _69_1669 = (base_and_refinement env wl t2)
in (match (_69_1669) with
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
# 1276 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _69_1682 _69_1686 -> (match ((_69_1682, _69_1686)) with
| ((a, _69_1681), (a', _69_1685)) -> begin
(let _151_936 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _151_935 -> FStar_TypeChecker_Common.TProb (_151_935)) _151_936))
end)) args args')
in (
# 1277 "FStar.TypeChecker.Rel.fst"
let formula = (let _151_938 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _151_938))
in (
# 1278 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _69_1692 -> begin
(
# 1283 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1284 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1285 "FStar.TypeChecker.Rel.fst"
let _69_1695 = problem
in {FStar_TypeChecker_Common.pid = _69_1695.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _69_1695.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _69_1695.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_1695.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_1695.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_1695.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_1695.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_1695.FStar_TypeChecker_Common.rank}) wl)))
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
# 1291 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1292 "FStar.TypeChecker.Rel.fst"
let _69_1712 = p
in (match (_69_1712) with
| ((u, k), ps, xs, (h, _69_1709, qs)) -> begin
(
# 1293 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1298 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1299 "FStar.TypeChecker.Rel.fst"
let _69_1718 = (imitation_sub_probs orig env xs ps qs)
in (match (_69_1718) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1300 "FStar.TypeChecker.Rel.fst"
let im = (let _151_949 = (h gs_xs)
in (u_abs xs _151_949))
in (
# 1301 "FStar.TypeChecker.Rel.fst"
let _69_1720 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_954 = (FStar_Syntax_Print.term_to_string im)
in (let _151_953 = (FStar_Syntax_Print.tag_of_term im)
in (let _151_952 = (let _151_950 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _151_950 (FStar_String.concat ", ")))
in (let _151_951 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _151_954 _151_953 _151_952 _151_951)))))
end else begin
()
end
in (
# 1306 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1311 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1312 "FStar.TypeChecker.Rel.fst"
let _69_1736 = p
in (match (_69_1736) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1316 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1317 "FStar.TypeChecker.Rel.fst"
let _69_1741 = (FStar_List.nth ps i)
in (match (_69_1741) with
| (pi, _69_1740) -> begin
(
# 1318 "FStar.TypeChecker.Rel.fst"
let _69_1745 = (FStar_List.nth xs i)
in (match (_69_1745) with
| (xi, _69_1744) -> begin
(
# 1320 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1321 "FStar.TypeChecker.Rel.fst"
let _69_1750 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1750) with
| (bs, k) -> begin
(
# 1322 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _69_1758)::tl -> begin
(
# 1325 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1326 "FStar.TypeChecker.Rel.fst"
let _69_1764 = (new_uvar r xs k_a)
in (match (_69_1764) with
| (gi_xs, gi) -> begin
(
# 1327 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1328 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1329 "FStar.TypeChecker.Rel.fst"
let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (
# 1330 "FStar.TypeChecker.Rel.fst"
let _69_1770 = (aux subst tl)
in (match (_69_1770) with
| (gi_xs', gi_ps') -> begin
(let _151_976 = (let _151_973 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_151_973)::gi_xs')
in (let _151_975 = (let _151_974 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_151_974)::gi_ps')
in (_151_976, _151_975)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _151_977 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _151_977)) then begin
None
end else begin
(
# 1336 "FStar.TypeChecker.Rel.fst"
let _69_1774 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_69_1774) with
| (g_xs, _69_1773) -> begin
(
# 1337 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1338 "FStar.TypeChecker.Rel.fst"
let proj = (let _151_978 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _151_978))
in (
# 1339 "FStar.TypeChecker.Rel.fst"
let sub = (let _151_984 = (let _151_983 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _151_982 = (let _151_981 = (FStar_List.map (fun _69_1782 -> (match (_69_1782) with
| (_69_1778, _69_1780, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _151_981))
in (mk_problem (p_scope orig) orig _151_983 (p_rel orig) _151_982 None "projection")))
in (FStar_All.pipe_left (fun _151_979 -> FStar_TypeChecker_Common.TProb (_151_979)) _151_984))
in (
# 1340 "FStar.TypeChecker.Rel.fst"
let _69_1784 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_986 = (FStar_Syntax_Print.term_to_string proj)
in (let _151_985 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _151_986 _151_985)))
end else begin
()
end
in (
# 1341 "FStar.TypeChecker.Rel.fst"
let wl = (let _151_988 = (let _151_987 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_151_987))
in (solve_prob orig _151_988 ((TERM ((u, proj)))::[]) wl))
in (let _151_990 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _151_989 -> Some (_151_989)) _151_990)))))))
end))
end)
end))
end)))
end)))
in (
# 1346 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1347 "FStar.TypeChecker.Rel.fst"
let _69_1798 = lhs
in (match (_69_1798) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1348 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1349 "FStar.TypeChecker.Rel.fst"
let xs = (let _151_1017 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _151_1017 Prims.fst))
in (let _151_1022 = (decompose env t2)
in ((uv, k), ps, xs, _151_1022))))
in (
# 1352 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1355 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_69_1808) -> begin
(
# 1359 "FStar.TypeChecker.Rel.fst"
let _69_1810 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1366 "FStar.TypeChecker.Rel.fst"
let _69_1818 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (
# 1370 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1371 "FStar.TypeChecker.Rel.fst"
let _69_1828 = (FStar_Syntax_Util.head_and_args t2)
in (match (_69_1828) with
| (hd, _69_1827) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _69_1839 -> begin
(
# 1377 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1380 "FStar.TypeChecker.Rel.fst"
let _69_1841 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1033 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _151_1033))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1383 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1384 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _151_1037 = (let _151_1036 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _151_1036 Prims.fst))
in (FStar_All.pipe_right _151_1037 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1391 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1392 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1393 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1394 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1395 "FStar.TypeChecker.Rel.fst"
let _69_1854 = (occurs_check env wl (uv, k) t2)
in (match (_69_1854) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _151_1039 = (let _151_1038 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _151_1038))
in (giveup_or_defer orig _151_1039))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _151_1040 = (subterms args_lhs)
in (imitate orig env wl _151_1040))
end else begin
(
# 1402 "FStar.TypeChecker.Rel.fst"
let _69_1855 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1043 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_1042 = (names_to_string fvs1)
in (let _151_1041 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _151_1043 _151_1042 _151_1041))))
end else begin
()
end
in (
# 1407 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _69_1859 -> begin
(let _151_1044 = (sn_binders env vars)
in (u_abs _151_1044 t2))
end)
in (
# 1410 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1415 "FStar.TypeChecker.Rel.fst"
let _69_1862 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1047 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_1046 = (names_to_string fvs1)
in (let _151_1045 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _151_1047 _151_1046 _151_1045))))
end else begin
()
end
in (let _151_1048 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _151_1048 (- (1)))))
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
if (let _151_1049 = (FStar_Syntax_Free.names t1)
in (check_head _151_1049 t2)) then begin
(
# 1427 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1428 "FStar.TypeChecker.Rel.fst"
let _69_1866 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1050 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _151_1050 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _151_1051 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _151_1051 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1453 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1456 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _69_1878 -> (match (_69_1878) with
| (t, u, k, args) -> begin
(
# 1459 "FStar.TypeChecker.Rel.fst"
let _69_1882 = (FStar_Syntax_Util.arrow_formals k)
in (match (_69_1882) with
| (all_formals, _69_1881) -> begin
(
# 1460 "FStar.TypeChecker.Rel.fst"
let _69_1883 = ()
in (
# 1462 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1470 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _69_1896 -> (match (_69_1896) with
| (x, imp) -> begin
(let _151_1073 = (FStar_Syntax_Syntax.bv_to_name x)
in (_151_1073, imp))
end))))
in (
# 1471 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1472 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1473 "FStar.TypeChecker.Rel.fst"
let _69_1902 = (FStar_Syntax_Util.type_u ())
in (match (_69_1902) with
| (t, _69_1901) -> begin
(let _151_1074 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _151_1074))
end))
in (
# 1475 "FStar.TypeChecker.Rel.fst"
let _69_1906 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_69_1906) with
| (t', tm_u1) -> begin
(
# 1476 "FStar.TypeChecker.Rel.fst"
let _69_1913 = (destruct_flex_t t')
in (match (_69_1913) with
| (_69_1908, u1, k1, _69_1912) -> begin
(
# 1477 "FStar.TypeChecker.Rel.fst"
let sol = (let _151_1076 = (let _151_1075 = (u_abs all_formals t')
in ((u, k), _151_1075))
in TERM (_151_1076))
in (
# 1478 "FStar.TypeChecker.Rel.fst"
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
# 1487 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _69_1932 -> (match (_69_1932) with
| (x, _69_1931) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1494 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _151_1078 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _151_1078 formals tl))
end)
end)
end)
end
| _69_1936 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _151_1079 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _151_1079 all_formals args))))
end))
end))
in (
# 1506 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _69_1942 _69_1946 r -> (match ((_69_1942, _69_1946)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _151_1088 = (solve_prob orig None [] wl)
in (solve env _151_1088))
end else begin
(
# 1514 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1515 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1516 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1517 "FStar.TypeChecker.Rel.fst"
let _69_1951 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1091 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _151_1090 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _151_1089 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _151_1091 _151_1090 _151_1089))))
end else begin
()
end
in (
# 1520 "FStar.TypeChecker.Rel.fst"
let _69_1964 = (
# 1521 "FStar.TypeChecker.Rel.fst"
let _69_1956 = (FStar_Syntax_Util.type_u ())
in (match (_69_1956) with
| (t, _69_1955) -> begin
(
# 1522 "FStar.TypeChecker.Rel.fst"
let _69_1960 = (new_uvar r zs t)
in (match (_69_1960) with
| (k, _69_1959) -> begin
(new_uvar r zs k)
end))
end))
in (match (_69_1964) with
| (u_zs, _69_1963) -> begin
(
# 1524 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs xs u_zs)
in (
# 1525 "FStar.TypeChecker.Rel.fst"
let _69_1968 = (occurs_check env wl (u1, k1) sub1)
in (match (_69_1968) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1528 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1530 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1532 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs ys u_zs)
in (
# 1533 "FStar.TypeChecker.Rel.fst"
let _69_1974 = (occurs_check env wl (u2, k2) sub2)
in (match (_69_1974) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1536 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1537 "FStar.TypeChecker.Rel.fst"
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
# 1540 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _69_1982 _69_1987 -> (match ((_69_1982, _69_1987)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1542 "FStar.TypeChecker.Rel.fst"
let _69_1988 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1097 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_1096 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _151_1097 _151_1096)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1545 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _69_1993 _69_1997 -> (match ((_69_1993, _69_1997)) with
| ((a, _69_1992), (t2, _69_1996)) -> begin
(let _151_1102 = (let _151_1100 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _151_1100 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _151_1102 (fun _151_1101 -> FStar_TypeChecker_Common.TProb (_151_1101))))
end)) xs args2)
in (
# 1548 "FStar.TypeChecker.Rel.fst"
let guard = (let _151_1104 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _151_1104))
in (
# 1549 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1552 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1553 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1554 "FStar.TypeChecker.Rel.fst"
let _69_2007 = (occurs_check env wl (u1, k1) t2)
in (match (_69_2007) with
| (occurs_ok, _69_2006) -> begin
(
# 1555 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1558 "FStar.TypeChecker.Rel.fst"
let sol = (let _151_1106 = (let _151_1105 = (u_abs xs t2)
in ((u1, k1), _151_1105))
in TERM (_151_1106))
in (
# 1559 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1562 "FStar.TypeChecker.Rel.fst"
let _69_2018 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_69_2018) with
| (sol, (_69_2013, u2, k2, ys)) -> begin
(
# 1563 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1564 "FStar.TypeChecker.Rel.fst"
let _69_2020 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _151_1107 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _151_1107))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _69_2025 -> begin
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
# 1572 "FStar.TypeChecker.Rel.fst"
let _69_2030 = lhs
in (match (_69_2030) with
| (t1, u1, k1, args1) -> begin
(
# 1573 "FStar.TypeChecker.Rel.fst"
let _69_2035 = rhs
in (match (_69_2035) with
| (t2, u2, k2, args2) -> begin
(
# 1574 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1575 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1576 "FStar.TypeChecker.Rel.fst"
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
| _69_2053 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1585 "FStar.TypeChecker.Rel.fst"
let _69_2057 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_69_2057) with
| (sol, _69_2056) -> begin
(
# 1586 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1587 "FStar.TypeChecker.Rel.fst"
let _69_2059 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _151_1108 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _151_1108))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _69_2064 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1594 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _151_1109 = (solve_prob orig None [] wl)
in (solve env _151_1109))
end else begin
(
# 1596 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1597 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _151_1110 = (solve_prob orig None [] wl)
in (solve env _151_1110))
end else begin
(
# 1599 "FStar.TypeChecker.Rel.fst"
let _69_2068 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1111 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _151_1111))
end else begin
()
end
in (
# 1602 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1604 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _69_2073 _69_2076 -> (match ((_69_2073, _69_2076)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1606 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1607 "FStar.TypeChecker.Rel.fst"
let _69_2083 = (FStar_Util.first_N n bs)
in (match (_69_2083) with
| (bs, rest) -> begin
(let _151_1141 = (mk_cod rest)
in (bs, _151_1141))
end)))
in (
# 1610 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1611 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _151_1145 = (let _151_1142 = (mk_cod1 [])
in (bs1, _151_1142))
in (let _151_1144 = (let _151_1143 = (mk_cod2 [])
in (bs2, _151_1143))
in (_151_1145, _151_1144)))
end else begin
if (l1 > l2) then begin
(let _151_1148 = (curry l2 bs1 mk_cod1)
in (let _151_1147 = (let _151_1146 = (mk_cod2 [])
in (bs2, _151_1146))
in (_151_1148, _151_1147)))
end else begin
(let _151_1151 = (let _151_1149 = (mk_cod1 [])
in (bs1, _151_1149))
in (let _151_1150 = (curry l1 bs2 mk_cod2)
in (_151_1151, _151_1150)))
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
# 1629 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _69_24 -> (match (_69_24) with
| [] -> begin
c
end
| bs -> begin
(let _151_1156 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _151_1156))
end))
in (
# 1633 "FStar.TypeChecker.Rel.fst"
let _69_2126 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_69_2126) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1638 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1639 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1640 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _151_1163 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _151_1162 -> FStar_TypeChecker_Common.CProb (_151_1162)) _151_1163)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _69_2136), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _69_2142)) -> begin
(
# 1644 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t _69_25 -> (match (_69_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1647 "FStar.TypeChecker.Rel.fst"
let _69_2157 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_69_2157) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _151_1176 = (let _151_1175 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _151_1174 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _151_1175 problem.FStar_TypeChecker_Common.relation _151_1174 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _151_1173 -> FStar_TypeChecker_Common.TProb (_151_1173)) _151_1176))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_69_2162), FStar_Syntax_Syntax.Tm_refine (_69_2165)) -> begin
(
# 1656 "FStar.TypeChecker.Rel.fst"
let _69_2170 = (as_refinement env wl t1)
in (match (_69_2170) with
| (x1, phi1) -> begin
(
# 1657 "FStar.TypeChecker.Rel.fst"
let _69_2173 = (as_refinement env wl t2)
in (match (_69_2173) with
| (x2, phi2) -> begin
(
# 1658 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _151_1178 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _151_1177 -> FStar_TypeChecker_Common.TProb (_151_1177)) _151_1178))
in (
# 1659 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1660 "FStar.TypeChecker.Rel.fst"
let subst = (let _151_1181 = (let _151_1180 = (let _151_1179 = (FStar_Syntax_Syntax.bv_to_name x1)
in (0, _151_1179))
in FStar_Syntax_Syntax.DB (_151_1180))
in (_151_1181)::[])
in (
# 1661 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1662 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1663 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1664 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _151_1198 = (imp phi1 phi2)
in (FStar_All.pipe_right _151_1198 (guard_on_element problem x1))))
in (
# 1665 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _69_2185 -> (match (()) with
| () -> begin
(
# 1666 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1670 "FStar.TypeChecker.Rel.fst"
let guard = (let _151_1201 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _151_1201 impl))
in (
# 1671 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1674 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _151_1205 = (let _151_1204 = (let _151_1203 = (FStar_Syntax_Syntax.mk_binder x1)
in (_151_1203)::(p_scope orig))
in (mk_problem _151_1204 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _151_1202 -> FStar_TypeChecker_Common.TProb (_151_1202)) _151_1205))
in (match ((solve env (
# 1675 "FStar.TypeChecker.Rel.fst"
let _69_2190 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _69_2190.ctr; defer_ok = false; smt_ok = _69_2190.smt_ok; tcenv = _69_2190.tcenv}))) with
| Failed (_69_2193) -> begin
(fallback ())
end
| Success (_69_2196) -> begin
(
# 1678 "FStar.TypeChecker.Rel.fst"
let guard = (let _151_1208 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _151_1207 = (let _151_1206 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _151_1206 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _151_1208 _151_1207)))
in (
# 1679 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1680 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1680 "FStar.TypeChecker.Rel.fst"
let _69_2200 = wl
in {attempting = _69_2200.attempting; wl_deferred = _69_2200.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _69_2200.defer_ok; smt_ok = _69_2200.smt_ok; tcenv = _69_2200.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _151_1210 = (destruct_flex_t t1)
in (let _151_1209 = (destruct_flex_t t2)
in (flex_flex orig _151_1210 _151_1209)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _151_1211 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _151_1211 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1708 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _151_1212 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _151_1212)) then begin
(let _151_1215 = (FStar_All.pipe_left (fun _151_1213 -> FStar_TypeChecker_Common.TProb (_151_1213)) (
# 1710 "FStar.TypeChecker.Rel.fst"
let _69_2345 = problem
in {FStar_TypeChecker_Common.pid = _69_2345.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_2345.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _69_2345.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2345.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2345.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2345.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2345.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2345.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2345.FStar_TypeChecker_Common.rank}))
in (let _151_1214 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _151_1215 _151_1214 t2 wl)))
end else begin
(
# 1711 "FStar.TypeChecker.Rel.fst"
let _69_2349 = (base_and_refinement env wl t2)
in (match (_69_2349) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _151_1218 = (FStar_All.pipe_left (fun _151_1216 -> FStar_TypeChecker_Common.TProb (_151_1216)) (
# 1714 "FStar.TypeChecker.Rel.fst"
let _69_2351 = problem
in {FStar_TypeChecker_Common.pid = _69_2351.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_2351.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _69_2351.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2351.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2351.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2351.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2351.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2351.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2351.FStar_TypeChecker_Common.rank}))
in (let _151_1217 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _151_1218 _151_1217 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1717 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1717 "FStar.TypeChecker.Rel.fst"
let _69_2357 = y
in {FStar_Syntax_Syntax.ppname = _69_2357.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _69_2357.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1718 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1719 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _151_1220 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _151_1219 -> FStar_TypeChecker_Common.TProb (_151_1219)) _151_1220))
in (
# 1721 "FStar.TypeChecker.Rel.fst"
let guard = (let _151_1221 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _151_1221 impl))
in (
# 1722 "FStar.TypeChecker.Rel.fst"
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
# 1731 "FStar.TypeChecker.Rel.fst"
let _69_2390 = (base_and_refinement env wl t1)
in (match (_69_2390) with
| (t_base, _69_2389) -> begin
(solve_t env (
# 1732 "FStar.TypeChecker.Rel.fst"
let _69_2391 = problem
in {FStar_TypeChecker_Common.pid = _69_2391.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _69_2391.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2391.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2391.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2391.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2391.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2391.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2391.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_69_2394), _69_2397) -> begin
(
# 1735 "FStar.TypeChecker.Rel.fst"
let t2 = (let _151_1222 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _151_1222))
in (solve_t env (
# 1736 "FStar.TypeChecker.Rel.fst"
let _69_2400 = problem
in {FStar_TypeChecker_Common.pid = _69_2400.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_2400.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_2400.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _69_2400.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2400.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2400.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2400.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2400.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2400.FStar_TypeChecker_Common.rank}) wl))
end
| (_69_2403, FStar_Syntax_Syntax.Tm_refine (_69_2405)) -> begin
(
# 1739 "FStar.TypeChecker.Rel.fst"
let t1 = (let _151_1223 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _151_1223))
in (solve_t env (
# 1740 "FStar.TypeChecker.Rel.fst"
let _69_2409 = problem
in {FStar_TypeChecker_Common.pid = _69_2409.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _69_2409.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_2409.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2409.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2409.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2409.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2409.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2409.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2409.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1744 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_69_2426) -> begin
t
end
| _69_2429 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _151_1228 = (
# 1747 "FStar.TypeChecker.Rel.fst"
let _69_2430 = problem
in (let _151_1227 = (maybe_eta t1)
in (let _151_1226 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _69_2430.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _151_1227; FStar_TypeChecker_Common.relation = _69_2430.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _151_1226; FStar_TypeChecker_Common.element = _69_2430.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2430.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2430.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2430.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2430.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2430.FStar_TypeChecker_Common.rank})))
in (solve_t env _151_1228 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let head1 = (let _151_1229 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _151_1229 Prims.fst))
in (
# 1760 "FStar.TypeChecker.Rel.fst"
let head2 = (let _151_1230 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _151_1230 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1765 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1766 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1768 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _151_1232 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _151_1231 -> Some (_151_1231)) _151_1232))
end
in (let _151_1233 = (solve_prob orig guard [] wl)
in (solve env _151_1233)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _69_2499, _69_2501), _69_2505) -> begin
(solve_t' env (
# 1776 "FStar.TypeChecker.Rel.fst"
let _69_2507 = problem
in {FStar_TypeChecker_Common.pid = _69_2507.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _69_2507.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_2507.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2507.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2507.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2507.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2507.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2507.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2507.FStar_TypeChecker_Common.rank}) wl)
end
| (_69_2510, FStar_Syntax_Syntax.Tm_ascribed (t2, _69_2513, _69_2515)) -> begin
(solve_t' env (
# 1779 "FStar.TypeChecker.Rel.fst"
let _69_2519 = problem
in {FStar_TypeChecker_Common.pid = _69_2519.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_2519.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_2519.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _69_2519.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2519.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2519.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2519.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2519.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2519.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _151_1236 = (let _151_1235 = (FStar_Syntax_Print.tag_of_term t1)
in (let _151_1234 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _151_1235 _151_1234)))
in (FStar_All.failwith _151_1236))
end
| _69_2558 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1791 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1792 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 1793 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 1794 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 1796 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 1797 "FStar.TypeChecker.Rel.fst"
let _69_2575 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 1799 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _69_2580 _69_2584 -> (match ((_69_2580, _69_2584)) with
| ((a1, _69_2579), (a2, _69_2583)) -> begin
(let _151_1251 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _151_1250 -> FStar_TypeChecker_Common.TProb (_151_1250)) _151_1251))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 1802 "FStar.TypeChecker.Rel.fst"
let guard = (let _151_1253 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _151_1253))
in (
# 1803 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _151_1254 = (solve_prob orig None [] wl)
in (solve env _151_1254))
end else begin
(
# 1807 "FStar.TypeChecker.Rel.fst"
let _69_2589 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1256 = (FStar_Syntax_Print.comp_to_string c1)
in (let _151_1255 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _151_1256 (rel_to_string problem.FStar_TypeChecker_Common.relation) _151_1255)))
end else begin
()
end
in (
# 1812 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1813 "FStar.TypeChecker.Rel.fst"
let _69_2594 = (c1, c2)
in (match (_69_2594) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_69_2596), FStar_Syntax_Syntax.Total (_69_2599)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _151_1257 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _151_1257 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _151_1259 = (
# 1825 "FStar.TypeChecker.Rel.fst"
let _69_2627 = problem
in (let _151_1258 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _69_2627.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _151_1258; FStar_TypeChecker_Common.relation = _69_2627.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _69_2627.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _69_2627.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2627.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2627.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2627.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2627.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2627.FStar_TypeChecker_Common.rank}))
in (solve_c env _151_1259 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _151_1261 = (
# 1829 "FStar.TypeChecker.Rel.fst"
let _69_2643 = problem
in (let _151_1260 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _69_2643.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _69_2643.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _69_2643.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _151_1260; FStar_TypeChecker_Common.element = _69_2643.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _69_2643.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _69_2643.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _69_2643.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _69_2643.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _69_2643.FStar_TypeChecker_Common.rank}))
in (solve_c env _151_1261 wl))
end
| (FStar_Syntax_Syntax.Comp (_69_2646), FStar_Syntax_Syntax.Comp (_69_2649)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _151_1262 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _151_1262 wl))
end else begin
(
# 1835 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 1836 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 1840 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 1841 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 1842 "FStar.TypeChecker.Rel.fst"
let _69_2656 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _151_1265 = (let _151_1264 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _151_1263 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _151_1264 _151_1263)))
in (giveup env _151_1265 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1849 "FStar.TypeChecker.Rel.fst"
let _69_2674 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _69_2667)::(wlp1, _69_2663)::[] -> begin
(wp1, wlp1)
end
| _69_2671 -> begin
(let _151_1267 = (let _151_1266 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _151_1266))
in (FStar_All.failwith _151_1267))
end)
in (match (_69_2674) with
| (wp, wlp) -> begin
(
# 1852 "FStar.TypeChecker.Rel.fst"
let c1 = (let _151_1273 = (let _151_1272 = (let _151_1268 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _151_1268))
in (let _151_1271 = (let _151_1270 = (let _151_1269 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _151_1269))
in (_151_1270)::[])
in (_151_1272)::_151_1271))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _151_1273; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 1859 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _69_26 -> (match (_69_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _69_2681 -> begin
false
end))))
in (
# 1860 "FStar.TypeChecker.Rel.fst"
let _69_2702 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _69_2687)::_69_2684, (wp2, _69_2694)::_69_2691) -> begin
(wp1, wp2)
end
| _69_2699 -> begin
(let _151_1277 = (let _151_1276 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _151_1275 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _151_1276 _151_1275)))
in (FStar_All.failwith _151_1277))
end)
in (match (_69_2702) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _151_1278 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _151_1278 wl))
end else begin
(
# 1867 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 1868 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 1870 "FStar.TypeChecker.Rel.fst"
let _69_2704 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _151_1288 = (let _151_1287 = (let _151_1286 = (let _151_1280 = (let _151_1279 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_151_1279)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _151_1280 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _151_1285 = (let _151_1284 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _151_1283 = (let _151_1282 = (let _151_1281 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_1281))
in (_151_1282)::[])
in (_151_1284)::_151_1283))
in (_151_1286, _151_1285)))
in FStar_Syntax_Syntax.Tm_app (_151_1287))
in (FStar_Syntax_Syntax.mk _151_1288 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 1874 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _151_1303 = (let _151_1302 = (let _151_1301 = (let _151_1290 = (let _151_1289 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_151_1289)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _151_1290 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _151_1300 = (let _151_1299 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _151_1298 = (let _151_1297 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _151_1296 = (let _151_1295 = (let _151_1291 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid r)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_1291))
in (let _151_1294 = (let _151_1293 = (let _151_1292 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _151_1292))
in (_151_1293)::[])
in (_151_1295)::_151_1294))
in (_151_1297)::_151_1296))
in (_151_1299)::_151_1298))
in (_151_1301, _151_1300)))
in FStar_Syntax_Syntax.Tm_app (_151_1302))
in (FStar_Syntax_Syntax.mk _151_1303 None r))
in (let _151_1312 = (let _151_1311 = (let _151_1310 = (let _151_1305 = (let _151_1304 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_151_1304)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _151_1305 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _151_1309 = (let _151_1308 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _151_1307 = (let _151_1306 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_151_1306)::[])
in (_151_1308)::_151_1307))
in (_151_1310, _151_1309)))
in FStar_Syntax_Syntax.Tm_app (_151_1311))
in (FStar_Syntax_Syntax.mk _151_1312 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 1881 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _151_1314 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _151_1313 -> FStar_TypeChecker_Common.TProb (_151_1313)) _151_1314))
in (
# 1882 "FStar.TypeChecker.Rel.fst"
let wl = (let _151_1318 = (let _151_1317 = (let _151_1316 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _151_1316 g))
in (FStar_All.pipe_left (fun _151_1315 -> Some (_151_1315)) _151_1317))
in (solve_prob orig _151_1318 [] wl))
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

# 1889 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _151_1322 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _69_2720 -> (match (_69_2720) with
| (_69_2712, u, _69_2715, _69_2717, _69_2719) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _151_1322 (FStar_String.concat ", "))))

# 1891 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _69_2727 -> begin
(
# 1895 "FStar.TypeChecker.Rel.fst"
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
# 1902 "FStar.TypeChecker.Rel.fst"
let carry = (let _151_1328 = (FStar_List.map (fun _69_2735 -> (match (_69_2735) with
| (_69_2733, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _151_1328 (FStar_String.concat ",\n")))
in (
# 1903 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1909 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1911 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1913 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _69_2744; FStar_TypeChecker_Env.implicits = _69_2742} -> begin
true
end
| _69_2749 -> begin
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
# 1923 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _69_2767 -> begin
(FStar_All.failwith "impossible")
end)
in (let _151_1344 = (
# 1926 "FStar.TypeChecker.Rel.fst"
let _69_2769 = g
in (let _151_1343 = (let _151_1342 = (let _151_1341 = (let _151_1340 = (FStar_Syntax_Syntax.mk_binder x)
in (_151_1340)::[])
in (u_abs _151_1341 f))
in (FStar_All.pipe_left (fun _151_1339 -> FStar_TypeChecker_Common.NonTrivial (_151_1339)) _151_1342))
in {FStar_TypeChecker_Env.guard_f = _151_1343; FStar_TypeChecker_Env.deferred = _69_2769.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_2769.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_2769.FStar_TypeChecker_Env.implicits}))
in Some (_151_1344)))
end))

# 1928 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1930 "FStar.TypeChecker.Rel.fst"
let _69_2776 = g
in (let _151_1355 = (let _151_1354 = (let _151_1353 = (let _151_1352 = (let _151_1351 = (let _151_1350 = (FStar_Syntax_Syntax.as_arg e)
in (_151_1350)::[])
in (f, _151_1351))
in FStar_Syntax_Syntax.Tm_app (_151_1352))
in (FStar_Syntax_Syntax.mk _151_1353 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _151_1349 -> FStar_TypeChecker_Common.NonTrivial (_151_1349)) _151_1354))
in {FStar_TypeChecker_Env.guard_f = _151_1355; FStar_TypeChecker_Env.deferred = _69_2776.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_2776.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_2776.FStar_TypeChecker_Env.implicits}))
end))

# 1932 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_69_2781) -> begin
(FStar_All.failwith "impossible")
end))

# 1936 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _151_1362 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_151_1362))
end))

# 1941 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _69_2798) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _69_2802 -> begin
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
# 1949 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 1951 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _151_1385 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _151_1385; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 1955 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 1956 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 1958 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 1960 "FStar.TypeChecker.Rel.fst"
let _69_2829 = g
in (let _151_1400 = (let _151_1399 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _151_1399 (fun _151_1398 -> FStar_TypeChecker_Common.NonTrivial (_151_1398))))
in {FStar_TypeChecker_Env.guard_f = _151_1400; FStar_TypeChecker_Env.deferred = _69_2829.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_2829.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_2829.FStar_TypeChecker_Env.implicits}))
end))

# 1965 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 1966 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _151_1408 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _151_1407 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _151_1408 (rel_to_string rel) _151_1407)))
end else begin
"TOP"
end
in (
# 1971 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 1974 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 1975 "FStar.TypeChecker.Rel.fst"
let x = (let _151_1419 = (let _151_1418 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _151_1417 -> Some (_151_1417)) _151_1418))
in (FStar_Syntax_Syntax.new_bv _151_1419 t1))
in (
# 1976 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 1977 "FStar.TypeChecker.Rel.fst"
let p = (let _151_1423 = (let _151_1421 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _151_1420 -> Some (_151_1420)) _151_1421))
in (let _151_1422 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _151_1423 _151_1422)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 1980 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 1981 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 1981 "FStar.TypeChecker.Rel.fst"
let _69_2849 = probs
in {attempting = _69_2849.attempting; wl_deferred = _69_2849.wl_deferred; ctr = _69_2849.ctr; defer_ok = false; smt_ok = _69_2849.smt_ok; tcenv = _69_2849.tcenv})
end else begin
probs
end
in (
# 1982 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 1983 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 1986 "FStar.TypeChecker.Rel.fst"
let _69_2856 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 1989 "FStar.TypeChecker.Rel.fst"
let _69_2862 = (FStar_Unionfind.rollback tx)
in (
# 1990 "FStar.TypeChecker.Rel.fst"
let _69_2864 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _151_1435 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _151_1435))
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
# 1997 "FStar.TypeChecker.Rel.fst"
let _69_2871 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _151_1440 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _151_1440))
end else begin
()
end
in (
# 1998 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 1999 "FStar.TypeChecker.Rel.fst"
let _69_2874 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _151_1441 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _151_1441))
end else begin
()
end
in (
# 2000 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _151_1442 = (FStar_Syntax_Util.unmeta f)
in _151_1442.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _69_2878) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _69_2882 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2003 "FStar.TypeChecker.Rel.fst"
let _69_2884 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _69_2884.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_2884.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_2884.FStar_TypeChecker_Env.implicits})))))
end))

# 2005 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _151_1454 = (let _151_1453 = (let _151_1452 = (let _151_1451 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _151_1451 (fun _151_1450 -> FStar_TypeChecker_Common.NonTrivial (_151_1450))))
in {FStar_TypeChecker_Env.guard_f = _151_1452; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _151_1453))
in (FStar_All.pipe_left (fun _151_1449 -> Some (_151_1449)) _151_1454))
end))

# 2010 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2011 "FStar.TypeChecker.Rel.fst"
let _69_2895 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1462 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_1461 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _151_1462 _151_1461)))
end else begin
()
end
in (
# 2013 "FStar.TypeChecker.Rel.fst"
let prob = (let _151_1465 = (let _151_1464 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _151_1464))
in (FStar_All.pipe_left (fun _151_1463 -> FStar_TypeChecker_Common.TProb (_151_1463)) _151_1465))
in (
# 2014 "FStar.TypeChecker.Rel.fst"
let g = (let _151_1467 = (solve_and_commit env (singleton env prob) (fun _69_2898 -> None))
in (FStar_All.pipe_left (with_guard env prob) _151_1467))
in g))))

# 2017 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _151_1477 = (let _151_1476 = (let _151_1475 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _151_1474 = (FStar_TypeChecker_Env.get_range env)
in (_151_1475, _151_1474)))
in FStar_Syntax_Syntax.Error (_151_1476))
in (Prims.raise _151_1477))
end
| Some (g) -> begin
(
# 2021 "FStar.TypeChecker.Rel.fst"
let _69_2907 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1480 = (FStar_Syntax_Print.term_to_string t1)
in (let _151_1479 = (FStar_Syntax_Print.term_to_string t2)
in (let _151_1478 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _151_1480 _151_1479 _151_1478))))
end else begin
()
end
in g)
end))

# 2028 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2029 "FStar.TypeChecker.Rel.fst"
let _69_2912 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1488 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_1487 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _151_1488 _151_1487)))
end else begin
()
end
in (
# 2031 "FStar.TypeChecker.Rel.fst"
let _69_2916 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_69_2916) with
| (prob, x) -> begin
(
# 2032 "FStar.TypeChecker.Rel.fst"
let g = (let _151_1490 = (solve_and_commit env (singleton env prob) (fun _69_2917 -> None))
in (FStar_All.pipe_left (with_guard env prob) _151_1490))
in (
# 2033 "FStar.TypeChecker.Rel.fst"
let _69_2920 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _151_1494 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _151_1493 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _151_1492 = (let _151_1491 = (FStar_Util.must g)
in (guard_to_string env _151_1491))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _151_1494 _151_1493 _151_1492))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2041 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _151_1501 = (let _151_1500 = (let _151_1499 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _151_1498 = (FStar_TypeChecker_Env.get_range env)
in (_151_1499, _151_1498)))
in FStar_Syntax_Syntax.Error (_151_1500))
in (Prims.raise _151_1501)))

# 2045 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2046 "FStar.TypeChecker.Rel.fst"
let _69_2928 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1509 = (FStar_Syntax_Print.comp_to_string c1)
in (let _151_1508 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _151_1509 _151_1508)))
end else begin
()
end
in (
# 2048 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2049 "FStar.TypeChecker.Rel.fst"
let prob = (let _151_1512 = (let _151_1511 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _151_1511 "sub_comp"))
in (FStar_All.pipe_left (fun _151_1510 -> FStar_TypeChecker_Common.CProb (_151_1510)) _151_1512))
in (let _151_1514 = (solve_and_commit env (singleton env prob) (fun _69_2932 -> None))
in (FStar_All.pipe_left (with_guard env prob) _151_1514))))))

# 2053 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2054 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2055 "FStar.TypeChecker.Rel.fst"
let _69_2941 = (FStar_Unionfind.rollback tx)
in (
# 2056 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _151_1532 = (let _151_1531 = (let _151_1530 = (let _151_1528 = (FStar_Syntax_Print.univ_to_string u1)
in (let _151_1527 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _151_1528 _151_1527 msg)))
in (let _151_1529 = (FStar_TypeChecker_Env.get_range env)
in (_151_1530, _151_1529)))
in FStar_Syntax_Syntax.Error (_151_1531))
in (Prims.raise _151_1532)))))
in (
# 2065 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2068 "FStar.TypeChecker.Rel.fst"
let _69_2957 = hd
in (match (_69_2957) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _151_1539 = (insert uv u1 tl)
in (hd)::_151_1539)
end
end))
end))
in (
# 2073 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2076 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2079 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _151_1544 = (insert uv u1 out)
in (group_by _151_1544 rest))
end)
end
| _69_2972 -> begin
None
end))
end))
in (
# 2086 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _69_2974 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _69_2977 -> begin
(
# 2091 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2091 "FStar.TypeChecker.Rel.fst"
let _69_2978 = (empty_worklist env)
in {attempting = _69_2978.attempting; wl_deferred = _69_2978.wl_deferred; ctr = _69_2978.ctr; defer_ok = true; smt_ok = _69_2978.smt_ok; tcenv = _69_2978.tcenv})
in (
# 2092 "FStar.TypeChecker.Rel.fst"
let _69_3018 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _69_2983 -> (match (_69_2983) with
| (u1, u2) -> begin
(
# 2093 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2094 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _69_2988 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2100 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _69_2998 -> begin
(u1)::[]
end)
in (
# 2103 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _69_3003 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _69_27 -> (match (_69_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2109 "FStar.TypeChecker.Rel.fst"
let _69_3010 = (FStar_Syntax_Util.univ_kernel u)
in (match (_69_3010) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2111 "FStar.TypeChecker.Rel.fst"
let _69_3014 = (FStar_Syntax_Util.univ_kernel u')
in (match (_69_3014) with
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
| USolved (_69_3016) -> begin
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
# 2122 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2122 "FStar.TypeChecker.Rel.fst"
let _69_3022 = (empty_worklist env)
in {attempting = _69_3022.attempting; wl_deferred = _69_3022.wl_deferred; ctr = _69_3022.ctr; defer_ok = false; smt_ok = _69_3022.smt_ok; tcenv = _69_3022.tcenv})
in (
# 2123 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _69_3037 -> begin
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
# 2136 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2137 "FStar.TypeChecker.Rel.fst"
let _69_3042 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2140 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2141 "FStar.TypeChecker.Rel.fst"
let fail = (fun _69_3049 -> (match (_69_3049) with
| (d, s) -> begin
(
# 2142 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2144 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2145 "FStar.TypeChecker.Rel.fst"
let _69_3052 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1565 = (wl_to_string wl)
in (let _151_1564 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _151_1565 _151_1564)))
end else begin
()
end
in (
# 2147 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2148 "FStar.TypeChecker.Rel.fst"
let _69_3056 = g
in {FStar_TypeChecker_Env.guard_f = _69_3056.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _69_3056.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_3056.FStar_TypeChecker_Env.implicits})
end
| _69_3059 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2150 "FStar.TypeChecker.Rel.fst"
let _69_3061 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2151 "FStar.TypeChecker.Rel.fst"
let _69_3063 = g
in {FStar_TypeChecker_Env.guard_f = _69_3063.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _69_3063.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _69_3063.FStar_TypeChecker_Env.implicits})))))))

# 2153 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2154 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2155 "FStar.TypeChecker.Rel.fst"
let _69_3077 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2159 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2163 "FStar.TypeChecker.Rel.fst"
let _69_3075 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _151_1572 = (FStar_TypeChecker_Env.get_range env)
in (let _151_1571 = (let _151_1570 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _151_1570))
in (FStar_TypeChecker_Errors.diag _151_1572 _151_1571)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (
# 2168 "FStar.TypeChecker.Rel.fst"
let _69_3079 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _69_3079.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_3079.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _69_3079.FStar_TypeChecker_Env.implicits}))))

# 2170 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2171 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _69_3086 -> begin
false
end))
in (
# 2174 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _69_3090 implicits -> (match (_69_3090) with
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
# 2178 "FStar.TypeChecker.Rel.fst"
let _69_3101 = hd
in (match (_69_3101) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2181 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2182 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2183 "FStar.TypeChecker.Rel.fst"
let _69_3104 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _151_1583 = (FStar_Syntax_Print.uvar_to_string u)
in (let _151_1582 = (FStar_Syntax_Print.term_to_string tm)
in (let _151_1581 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _151_1583 _151_1582 _151_1581))))
end else begin
()
end
in (
# 2186 "FStar.TypeChecker.Rel.fst"
let _69_3111 = (env.FStar_TypeChecker_Env.type_of (
# 2186 "FStar.TypeChecker.Rel.fst"
let _69_3106 = env
in {FStar_TypeChecker_Env.solver = _69_3106.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _69_3106.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _69_3106.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _69_3106.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _69_3106.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _69_3106.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _69_3106.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _69_3106.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _69_3106.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _69_3106.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _69_3106.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _69_3106.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _69_3106.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _69_3106.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _69_3106.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _69_3106.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _69_3106.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _69_3106.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _69_3106.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _69_3106.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _69_3106.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_69_3111) with
| (_69_3109, g) -> begin
(
# 2187 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl))
end)))))
end
end))
end)
end))
in (
# 2189 "FStar.TypeChecker.Rel.fst"
let _69_3113 = g
in (let _151_1584 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _69_3113.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _69_3113.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _69_3113.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _151_1584})))))

# 2191 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2192 "FStar.TypeChecker.Rel.fst"
let g = (let _151_1589 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _151_1589 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _151_1590 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _151_1590))
end
| (_69_3122, _69_3124, _69_3126, _69_3128, r)::_69_3120 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2197 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2199 "FStar.TypeChecker.Rel.fst"
let _69_3134 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _69_3134.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _69_3134.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _69_3134.FStar_TypeChecker_Env.implicits}))





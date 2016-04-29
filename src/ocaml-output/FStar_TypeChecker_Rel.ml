
open Prims
# 60 "FStar.TypeChecker.Rel.fst"
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (
# 66 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(
# 69 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _55_38 -> begin
(
# 72 "FStar.TypeChecker.Rel.fst"
let args = (FStar_All.pipe_right binders (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder))
in (
# 73 "FStar.TypeChecker.Rel.fst"
let k' = (let _144_7 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _144_7))
in (
# 74 "FStar.TypeChecker.Rel.fst"
let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _144_8 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_144_8, uv)))))
end)))

# 81 "FStar.TypeChecker.Rel.fst"
type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)

# 82 "FStar.TypeChecker.Rel.fst"
let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.TypeChecker.Rel.fst"
let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.TypeChecker.Rel.fst"
let ___TERM____0 = (fun projectee -> (match (projectee) with
| TERM (_55_44) -> begin
_55_44
end))

# 83 "FStar.TypeChecker.Rel.fst"
let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_55_47) -> begin
_55_47
end))

# 86 "FStar.TypeChecker.Rel.fst"
type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

# 86 "FStar.TypeChecker.Rel.fst"
let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

# 96 "FStar.TypeChecker.Rel.fst"
type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)

# 97 "FStar.TypeChecker.Rel.fst"
let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.TypeChecker.Rel.fst"
let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

# 97 "FStar.TypeChecker.Rel.fst"
let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_55_57) -> begin
_55_57
end))

# 98 "FStar.TypeChecker.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_55_60) -> begin
_55_60
end))

# 100 "FStar.TypeChecker.Rel.fst"
type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

# 101 "FStar.TypeChecker.Rel.fst"
let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 102 "FStar.TypeChecker.Rel.fst"
let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.TypeChecker.Rel.fst"
let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 105 "FStar.TypeChecker.Rel.fst"
type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

# 106 "FStar.TypeChecker.Rel.fst"
type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

# 107 "FStar.TypeChecker.Rel.fst"
type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

# 116 "FStar.TypeChecker.Rel.fst"
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

# 121 "FStar.TypeChecker.Rel.fst"
let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

# 123 "FStar.TypeChecker.Rel.fst"
let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _55_2 -> (match (_55_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_107 = (let _144_106 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _144_105 = (let _144_104 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _144_103 = (let _144_102 = (let _144_101 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _144_100 = (let _144_99 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _144_98 = (let _144_97 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _144_96 = (let _144_95 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_144_95)::[])
in (_144_97)::_144_96))
in (_144_99)::_144_98))
in (_144_101)::_144_100))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_144_102)
in (_144_104)::_144_103))
in (_144_106)::_144_105))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _144_107))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _144_109 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _144_108 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _144_109 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_108)))
end))

# 139 "FStar.TypeChecker.Rel.fst"
let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _55_3 -> (match (_55_3) with
| UNIV (u, t) -> begin
(
# 141 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _144_114 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _144_114 FStar_Util.string_of_int))
end
in (let _144_115 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _144_115)))
end
| TERM ((u, _55_84), t) -> begin
(
# 145 "FStar.TypeChecker.Rel.fst"
let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _144_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _144_116 FStar_Util.string_of_int))
end
in (let _144_117 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _144_117)))
end))

# 147 "FStar.TypeChecker.Rel.fst"
let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _144_122 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _144_122 (FStar_String.concat ", "))))

# 148 "FStar.TypeChecker.Rel.fst"
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set  ->  Prims.string = (fun nms -> (let _144_126 = (let _144_125 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _144_125 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _144_126 (FStar_String.concat ", "))))

# 149 "FStar.TypeChecker.Rel.fst"
let args_to_string = (fun args -> (let _144_129 = (FStar_All.pipe_right args (FStar_List.map (fun _55_97 -> (match (_55_97) with
| (x, _55_96) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _144_129 (FStar_String.concat " "))))

# 158 "FStar.TypeChecker.Rel.fst"
let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 166 "FStar.TypeChecker.Rel.fst"
let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (
# 166 "FStar.TypeChecker.Rel.fst"
let _55_101 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _55_101.wl_deferred; ctr = _55_101.ctr; defer_ok = _55_101.defer_ok; smt_ok = _55_101.smt_ok; tcenv = _55_101.tcenv}))

# 167 "FStar.TypeChecker.Rel.fst"
let wl_of_guard = (fun env g -> (
# 167 "FStar.TypeChecker.Rel.fst"
let _55_105 = (empty_worklist env)
in (let _144_138 = (FStar_List.map Prims.snd g)
in {attempting = _144_138; wl_deferred = _55_105.wl_deferred; ctr = _55_105.ctr; defer_ok = false; smt_ok = _55_105.smt_ok; tcenv = _55_105.tcenv})))

# 168 "FStar.TypeChecker.Rel.fst"
let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 168 "FStar.TypeChecker.Rel.fst"
let _55_110 = wl
in {attempting = _55_110.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _55_110.ctr; defer_ok = _55_110.defer_ok; smt_ok = _55_110.smt_ok; tcenv = _55_110.tcenv}))

# 169 "FStar.TypeChecker.Rel.fst"
let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 169 "FStar.TypeChecker.Rel.fst"
let _55_114 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _55_114.wl_deferred; ctr = _55_114.ctr; defer_ok = _55_114.defer_ok; smt_ok = _55_114.smt_ok; tcenv = _55_114.tcenv}))

# 171 "FStar.TypeChecker.Rel.fst"
let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (
# 172 "FStar.TypeChecker.Rel.fst"
let _55_119 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_155 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _144_155))
end else begin
()
end
in Failed ((prob, reason))))

# 182 "FStar.TypeChecker.Rel.fst"
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
# 186 "FStar.TypeChecker.Rel.fst"
let _55_126 = p
in {FStar_TypeChecker_Common.pid = _55_126.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _55_126.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_126.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_126.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_126.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_126.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_126.FStar_TypeChecker_Common.rank}))

# 187 "FStar.TypeChecker.Rel.fst"
let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 188 "FStar.TypeChecker.Rel.fst"
let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _55_5 -> (match (_55_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _144_162 -> FStar_TypeChecker_Common.TProb (_144_162)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _144_163 -> FStar_TypeChecker_Common.CProb (_144_163)))
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
(FStar_All.pipe_left (fun _144_182 -> FStar_TypeChecker_Common.TProb (_144_182)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _144_183 -> FStar_TypeChecker_Common.CProb (_144_183)) (invert p))
end))

# 216 "FStar.TypeChecker.Rel.fst"
let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 217 "FStar.TypeChecker.Rel.fst"
let next_pid : Prims.unit  ->  Prims.int = (
# 218 "FStar.TypeChecker.Rel.fst"
let ctr = (FStar_ST.alloc 0)
in (fun _55_176 -> (match (()) with
| () -> begin
(
# 219 "FStar.TypeChecker.Rel.fst"
let _55_177 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 221 "FStar.TypeChecker.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _144_196 = (next_pid ())
in (let _144_195 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _144_196; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _144_195; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 233 "FStar.TypeChecker.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (
# 234 "FStar.TypeChecker.Rel.fst"
let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _144_206 = (next_pid ())
in (let _144_205 = (let _144_204 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _144_204 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _144_206; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _144_205; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 247 "FStar.TypeChecker.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _144_213 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _144_213; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 259 "FStar.TypeChecker.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 263 "FStar.TypeChecker.Rel.fst"
let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _144_225 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _144_224 = (prob_to_string env d)
in (let _144_223 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _144_225 _144_224 _144_223 s)))))

# 277 "FStar.TypeChecker.Rel.fst"
let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _55_14 -> (match (_55_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _55_218 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _55_221), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 285 "FStar.TypeChecker.Rel.fst"
let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _55_15 -> (match (_55_15) with
| UNIV (_55_230) -> begin
None
end
| TERM ((u, _55_234), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 289 "FStar.TypeChecker.Rel.fst"
let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _55_16 -> (match (_55_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _55_247 -> begin
None
end))))

# 301 "FStar.TypeChecker.Rel.fst"
let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _144_244 = (let _144_243 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _144_243))
in (FStar_Syntax_Subst.compress _144_244)))

# 302 "FStar.TypeChecker.Rel.fst"
let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _144_249 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _144_249)))

# 303 "FStar.TypeChecker.Rel.fst"
let norm_arg = (fun env t -> (let _144_252 = (sn env (Prims.fst t))
in (_144_252, (Prims.snd t))))

# 304 "FStar.TypeChecker.Rel.fst"
let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _55_258 -> (match (_55_258) with
| (x, imp) -> begin
(let _144_259 = (
# 305 "FStar.TypeChecker.Rel.fst"
let _55_259 = x
in (let _144_258 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_259.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_259.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_258}))
in (_144_259, imp))
end)))))

# 311 "FStar.TypeChecker.Rel.fst"
let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (
# 312 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun u -> (
# 313 "FStar.TypeChecker.Rel.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _144_266 = (aux u)
in FStar_Syntax_Syntax.U_succ (_144_266))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _144_267 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_144_267))
end
| _55_271 -> begin
u
end)))
in (let _144_268 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _144_268))))

# 324 "FStar.TypeChecker.Rel.fst"
let normalize_refinement = (fun steps env wl t0 -> (FStar_TypeChecker_Normalize.normalize_refinement steps env t0))

# 326 "FStar.TypeChecker.Rel.fst"
let base_and_refinement = (fun env wl t1 -> (
# 327 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _55_291; FStar_Syntax_Syntax.pos = _55_289; FStar_Syntax_Syntax.vars = _55_287} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _144_282 = (let _144_281 = (FStar_Syntax_Print.term_to_string tt)
in (let _144_280 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _144_281 _144_280)))
in (FStar_All.failwith _144_282))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(
# 342 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (match ((let _144_283 = (FStar_Syntax_Subst.compress t1')
in _144_283.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_refine (_55_309) -> begin
(aux true t1')
end
| _55_312 -> begin
(t1, None)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _144_286 = (let _144_285 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_284 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _144_285 _144_284)))
in (FStar_All.failwith _144_286))
end))
in (let _144_287 = (whnf env t1)
in (aux false _144_287))))

# 365 "FStar.TypeChecker.Rel.fst"
let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _144_292 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _144_292 Prims.fst)))

# 367 "FStar.TypeChecker.Rel.fst"
let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _144_295 = (FStar_Syntax_Syntax.null_bv t)
in (_144_295, FStar_Syntax_Util.t_true)))

# 369 "FStar.TypeChecker.Rel.fst"
let as_refinement = (fun env wl t -> (
# 370 "FStar.TypeChecker.Rel.fst"
let _55_358 = (base_and_refinement env wl t)
in (match (_55_358) with
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
let force_refinement = (fun _55_366 -> (match (_55_366) with
| (t_base, refopt) -> begin
(
# 376 "FStar.TypeChecker.Rel.fst"
let _55_374 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_55_374) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 389 "FStar.TypeChecker.Rel.fst"
let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _55_17 -> (match (_55_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_308 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _144_307 = (let _144_304 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _144_304))
in (let _144_306 = (let _144_305 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _144_305))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _144_308 _144_307 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_306))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _144_311 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _144_310 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _144_309 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _144_311 _144_310 (rel_to_string p.FStar_TypeChecker_Common.relation) _144_309))))
end))

# 404 "FStar.TypeChecker.Rel.fst"
let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _144_317 = (let _144_316 = (let _144_315 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _55_387 -> (match (_55_387) with
| (_55_383, _55_385, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _144_315))
in (FStar_List.map (wl_prob_to_string wl) _144_316))
in (FStar_All.pipe_right _144_317 (FStar_String.concat "\n\t"))))

# 414 "FStar.TypeChecker.Rel.fst"
let u_abs : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun k ys t -> (
# 415 "FStar.TypeChecker.Rel.fst"
let _55_406 = (match ((let _144_324 = (FStar_Syntax_Subst.compress k)
in _144_324.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if ((FStar_List.length bs) = (FStar_List.length ys)) then begin
(let _144_325 = (FStar_Syntax_Subst.open_comp bs c)
in ((ys, t), _144_325))
end else begin
(
# 419 "FStar.TypeChecker.Rel.fst"
let _55_397 = (FStar_Syntax_Util.abs_formals t)
in (match (_55_397) with
| (ys', t) -> begin
(let _144_326 = (FStar_Syntax_Util.arrow_formals_comp k)
in (((FStar_List.append ys ys'), t), _144_326))
end))
end
end
| _55_399 -> begin
(let _144_328 = (let _144_327 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _144_327))
in ((ys, t), _144_328))
end)
in (match (_55_406) with
| ((ys, t), (xs, c)) -> begin
if ((FStar_List.length xs) <> (FStar_List.length ys)) then begin
(FStar_Syntax_Util.abs ys t (Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))))
end else begin
(
# 424 "FStar.TypeChecker.Rel.fst"
let c = (let _144_329 = (FStar_Syntax_Util.rename_binders xs ys)
in (FStar_Syntax_Subst.subst_comp _144_329 c))
in (let _144_333 = (let _144_332 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_330 -> FStar_Util.Inl (_144_330)))
in (FStar_All.pipe_right _144_332 (fun _144_331 -> Some (_144_331))))
in (FStar_Syntax_Util.abs ys t _144_333)))
end
end)))

# 427 "FStar.TypeChecker.Rel.fst"
let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (
# 428 "FStar.TypeChecker.Rel.fst"
let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (
# 431 "FStar.TypeChecker.Rel.fst"
let _55_420 = (p_guard prob)
in (match (_55_420) with
| (_55_418, uv) -> begin
(
# 432 "FStar.TypeChecker.Rel.fst"
let _55_431 = (match ((let _144_344 = (FStar_Syntax_Subst.compress uv)
in _144_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(
# 434 "FStar.TypeChecker.Rel.fst"
let bs = (p_scope prob)
in (
# 435 "FStar.TypeChecker.Rel.fst"
let phi = (u_abs k bs phi)
in (
# 436 "FStar.TypeChecker.Rel.fst"
let _55_427 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _144_347 = (FStar_Util.string_of_int (p_pid prob))
in (let _144_346 = (FStar_Syntax_Print.term_to_string uv)
in (let _144_345 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _144_347 _144_346 _144_345))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi))))
end
| _55_430 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (
# 443 "FStar.TypeChecker.Rel.fst"
let _55_433 = (commit uvis)
in (
# 444 "FStar.TypeChecker.Rel.fst"
let _55_435 = wl
in {attempting = _55_435.attempting; wl_deferred = _55_435.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_435.defer_ok; smt_ok = _55_435.smt_ok; tcenv = _55_435.tcenv})))
end))))

# 446 "FStar.TypeChecker.Rel.fst"
let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (
# 447 "FStar.TypeChecker.Rel.fst"
let _55_440 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_356 = (FStar_Util.string_of_int pid)
in (let _144_355 = (let _144_354 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _144_354 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _144_356 _144_355)))
end else begin
()
end
in (
# 449 "FStar.TypeChecker.Rel.fst"
let _55_442 = (commit sol)
in (
# 450 "FStar.TypeChecker.Rel.fst"
let _55_444 = wl
in {attempting = _55_444.attempting; wl_deferred = _55_444.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_444.defer_ok; smt_ok = _55_444.smt_ok; tcenv = _55_444.tcenv}))))

# 452 "FStar.TypeChecker.Rel.fst"
let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (
# 453 "FStar.TypeChecker.Rel.fst"
let conj_guard = (fun t g -> (match ((t, g)) with
| (_55_454, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _144_369 = (FStar_Syntax_Util.mk_conj t f)
in Some (_144_369))
end))
in (
# 457 "FStar.TypeChecker.Rel.fst"
let _55_466 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_372 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _144_371 = (let _144_370 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _144_370 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _144_372 _144_371)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 469 "FStar.TypeChecker.Rel.fst"
let rec occurs = (fun wl uk t -> (let _144_382 = (let _144_380 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _144_380 FStar_Util.set_elements))
in (FStar_All.pipe_right _144_382 (FStar_Util.for_some (fun _55_475 -> (match (_55_475) with
| (uv, _55_474) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 475 "FStar.TypeChecker.Rel.fst"
let occurs_check = (fun env wl uk t -> (
# 476 "FStar.TypeChecker.Rel.fst"
let occurs_ok = (not ((occurs wl uk t)))
in (
# 477 "FStar.TypeChecker.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _144_389 = (let _144_388 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _144_387 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _144_388 _144_387)))
in Some (_144_389))
end
in (occurs_ok, msg))))

# 484 "FStar.TypeChecker.Rel.fst"
let occurs_and_freevars_check = (fun env wl uk fvs t -> (
# 485 "FStar.TypeChecker.Rel.fst"
let fvs_t = (FStar_Syntax_Free.names t)
in (
# 486 "FStar.TypeChecker.Rel.fst"
let _55_490 = (occurs_check env wl uk t)
in (match (_55_490) with
| (occurs_ok, msg) -> begin
(let _144_395 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _144_395, (msg, fvs, fvs_t)))
end))))

# 489 "FStar.TypeChecker.Rel.fst"
let intersect_vars = (fun v1 v2 -> (
# 490 "FStar.TypeChecker.Rel.fst"
let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (
# 492 "FStar.TypeChecker.Rel.fst"
let v1_set = (as_set v1)
in (
# 493 "FStar.TypeChecker.Rel.fst"
let _55_508 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _55_500 _55_503 -> (match ((_55_500, _55_503)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _144_404 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _144_404)) then begin
(isect, isect_set)
end else begin
(
# 499 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _144_405 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _144_405))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_55_508) with
| (isect, _55_507) -> begin
(FStar_List.rev isect)
end)))))

# 506 "FStar.TypeChecker.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _55_514 _55_518 -> (match ((_55_514, _55_518)) with
| ((a, _55_513), (b, _55_517)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 510 "FStar.TypeChecker.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 511 "FStar.TypeChecker.Rel.fst"
let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _55_528 -> (match (_55_528) with
| (b, _55_527) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _55_530 -> begin
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
# 524 "FStar.TypeChecker.Rel.fst"
let _55_539 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_420 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _144_420))
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
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _55_553; FStar_Syntax_Syntax.pos = _55_551; FStar_Syntax_Syntax.vars = _55_549}, args) -> begin
(t, uv, k, args)
end
| _55_563 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 533 "FStar.TypeChecker.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 534 "FStar.TypeChecker.Rel.fst"
let _55_570 = (destruct_flex_t t)
in (match (_55_570) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _55_574 -> begin
((t, uv, k, args), None)
end)
end)))

# 608 "FStar.TypeChecker.Rel.fst"
type match_result =
| MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option * FStar_Syntax_Syntax.delta_depth Prims.option)
| HeadMatch
| FullMatch

# 609 "FStar.TypeChecker.Rel.fst"
let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 610 "FStar.TypeChecker.Rel.fst"
let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 611 "FStar.TypeChecker.Rel.fst"
let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 609 "FStar.TypeChecker.Rel.fst"
let ___MisMatch____0 = (fun projectee -> (match (projectee) with
| MisMatch (_55_577) -> begin
_55_577
end))

# 613 "FStar.TypeChecker.Rel.fst"
let head_match : match_result  ->  match_result = (fun _55_18 -> (match (_55_18) with
| MisMatch (i, j) -> begin
MisMatch ((i, j))
end
| _55_584 -> begin
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
# 625 "FStar.TypeChecker.Rel.fst"
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
# 647 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Util.unmeta t1)
in (
# 648 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _55_670), FStar_Syntax_Syntax.Tm_uinst (g, _55_675)) -> begin
(let _144_456 = (head_matches env f g)
in (FStar_All.pipe_right _144_456 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _55_686), FStar_Syntax_Syntax.Tm_uvar (uv', _55_691)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch ((None, None))
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_697), FStar_Syntax_Syntax.Tm_refine (y, _55_702)) -> begin
(let _144_457 = (head_matches env x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _144_457 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_708), _55_712) -> begin
(let _144_458 = (head_matches env x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _144_458 head_match))
end
| (_55_715, FStar_Syntax_Syntax.Tm_refine (x, _55_718)) -> begin
(let _144_459 = (head_matches env t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _144_459 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_738), FStar_Syntax_Syntax.Tm_app (head', _55_743)) -> begin
(head_matches env head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _55_749), _55_753) -> begin
(head_matches env head t2)
end
| (_55_756, FStar_Syntax_Syntax.Tm_app (head, _55_759)) -> begin
(head_matches env t1 head)
end
| _55_764 -> begin
(let _144_462 = (let _144_461 = (delta_depth_of_term env t1)
in (let _144_460 = (delta_depth_of_term env t2)
in (_144_461, _144_460)))
in MisMatch (_144_462))
end))))

# 671 "FStar.TypeChecker.Rel.fst"
let head_matches_delta = (fun env wl t1 t2 -> (
# 672 "FStar.TypeChecker.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 673 "FStar.TypeChecker.Rel.fst"
let fail = (fun r -> (r, None))
in (
# 674 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun n_delta t1 t2 -> (
# 675 "FStar.TypeChecker.Rel.fst"
let r = (head_matches env t1 t2)
in (match (r) with
| MisMatch (Some (d1), Some (d2)) when (d1 = d2) -> begin
(match ((FStar_TypeChecker_Common.decr_delta_depth d1)) with
| None -> begin
(fail r)
end
| Some (d) -> begin
(
# 683 "FStar.TypeChecker.Rel.fst"
let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (
# 684 "FStar.TypeChecker.Rel.fst"
let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (aux (n_delta + 1) t1 t2)))
end)
end
| (MisMatch (Some (FStar_Syntax_Syntax.Delta_equational), _)) | (MisMatch (_, Some (FStar_Syntax_Syntax.Delta_equational))) -> begin
(fail r)
end
| MisMatch (Some (d1), Some (d2)) -> begin
(
# 693 "FStar.TypeChecker.Rel.fst"
let d1_greater_than_d2 = (FStar_TypeChecker_Common.delta_depth_greater_than d1 d2)
in (
# 694 "FStar.TypeChecker.Rel.fst"
let _55_815 = if d1_greater_than_d2 then begin
(
# 695 "FStar.TypeChecker.Rel.fst"
let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d2))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t1)
in (t1', t2))
end else begin
(
# 697 "FStar.TypeChecker.Rel.fst"
let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (let _144_483 = (normalize_refinement ((FStar_TypeChecker_Normalize.UnfoldUntil (d1))::(FStar_TypeChecker_Normalize.WHNF)::[]) env wl t2)
in (t1, _144_483)))
end
in (match (_55_815) with
| (t1, t2) -> begin
(aux (n_delta + 1) t1 t2)
end)))
end
| MisMatch (_55_817) -> begin
(fail r)
end
| _55_820 -> begin
(success n_delta r t1 t2)
end)))
in (aux 0 t1 t2)))))

# 706 "FStar.TypeChecker.Rel.fst"
type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 707 "FStar.TypeChecker.Rel.fst"
let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 708 "FStar.TypeChecker.Rel.fst"
let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 707 "FStar.TypeChecker.Rel.fst"
let ___T____0 = (fun projectee -> (match (projectee) with
| T (_55_823) -> begin
_55_823
end))

# 708 "FStar.TypeChecker.Rel.fst"
let ___C____0 = (fun projectee -> (match (projectee) with
| C (_55_826) -> begin
_55_826
end))

# 709 "FStar.TypeChecker.Rel.fst"
type tcs =
tc Prims.list

# 711 "FStar.TypeChecker.Rel.fst"
let rec decompose : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  ((tc Prims.list  ->  FStar_Syntax_Syntax.term) * (FStar_Syntax_Syntax.term  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list) = (fun env t -> (
# 712 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (
# 713 "FStar.TypeChecker.Rel.fst"
let matches = (fun t' -> (match ((head_matches env t t')) with
| MisMatch (_55_833) -> begin
false
end
| _55_836 -> begin
true
end))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(
# 718 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun args' -> (
# 719 "FStar.TypeChecker.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_55_846, imp), T (t)) -> begin
(t, imp)
end
| _55_853 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (
# 724 "FStar.TypeChecker.Rel.fst"
let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _55_858 -> (match (_55_858) with
| (t, _55_857) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 730 "FStar.TypeChecker.Rel.fst"
let fail = (fun _55_865 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 731 "FStar.TypeChecker.Rel.fst"
let _55_868 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_868) with
| (bs, c) -> begin
(
# 733 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun tcs -> (
# 734 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((
# 735 "FStar.TypeChecker.Rel.fst"
let _55_885 = x
in {FStar_Syntax_Syntax.ppname = _55_885.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_885.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _55_893 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (
# 740 "FStar.TypeChecker.Rel.fst"
let rec decompose = (fun out _55_19 -> (match (_55_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(decompose (((Some (hd), CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest)
end))
in (let _144_565 = (decompose [] bs)
in (rebuild, matches, _144_565))))
end)))
end
| _55_902 -> begin
(
# 750 "FStar.TypeChecker.Rel.fst"
let rebuild = (fun _55_20 -> (match (_55_20) with
| [] -> begin
t
end
| _55_906 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 756 "FStar.TypeChecker.Rel.fst"
let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _55_21 -> (match (_55_21) with
| T (t) -> begin
t
end
| _55_913 -> begin
(FStar_All.failwith "Impossible")
end))

# 760 "FStar.TypeChecker.Rel.fst"
let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _55_22 -> (match (_55_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _55_918 -> begin
(FStar_All.failwith "Impossible")
end))

# 764 "FStar.TypeChecker.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 769 "FStar.TypeChecker.Rel.fst"
let r = (p_loc orig)
in (
# 770 "FStar.TypeChecker.Rel.fst"
let rel = (p_rel orig)
in (
# 771 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_55_931, variance, T (ti)) -> begin
(
# 774 "FStar.TypeChecker.Rel.fst"
let k = (
# 775 "FStar.TypeChecker.Rel.fst"
let _55_939 = (FStar_Syntax_Util.type_u ())
in (match (_55_939) with
| (t, _55_938) -> begin
(let _144_587 = (new_uvar r scope t)
in (Prims.fst _144_587))
end))
in (
# 777 "FStar.TypeChecker.Rel.fst"
let _55_943 = (new_uvar r scope k)
in (match (_55_943) with
| (gi_xs, gi) -> begin
(
# 778 "FStar.TypeChecker.Rel.fst"
let gi_ps = (match (args) with
| [] -> begin
gi
end
| _55_946 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _144_590 = (let _144_589 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _144_588 -> FStar_TypeChecker_Common.TProb (_144_588)) _144_589))
in (T (gi_xs), _144_590)))
end)))
end
| (_55_949, _55_951, C (_55_953)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 786 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(
# 790 "FStar.TypeChecker.Rel.fst"
let _55_1031 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _55_971; FStar_Syntax_Syntax.pos = _55_969; FStar_Syntax_Syntax.vars = _55_967})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _144_599 = (let _144_598 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _144_597 -> C (_144_597)) _144_598))
in (_144_599, (prob)::[]))
end
| _55_982 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _55_990; FStar_Syntax_Syntax.pos = _55_988; FStar_Syntax_Syntax.vars = _55_986})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _144_602 = (let _144_601 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _144_600 -> C (_144_600)) _144_601))
in (_144_602, (prob)::[]))
end
| _55_1001 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_55_1003, _55_1005, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _55_1011; FStar_Syntax_Syntax.pos = _55_1009; FStar_Syntax_Syntax.vars = _55_1007})) -> begin
(
# 804 "FStar.TypeChecker.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (
# 805 "FStar.TypeChecker.Rel.fst"
let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (
# 806 "FStar.TypeChecker.Rel.fst"
let _55_1022 = (let _144_604 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _144_604 FStar_List.unzip))
in (match (_55_1022) with
| (tcs, sub_probs) -> begin
(
# 807 "FStar.TypeChecker.Rel.fst"
let gi_xs = (let _144_609 = (let _144_608 = (let _144_605 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _144_605 un_T))
in (let _144_607 = (let _144_606 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _144_606 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _144_608; FStar_Syntax_Syntax.effect_args = _144_607; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _144_609))
in (C (gi_xs), sub_probs))
end))))
end
| _55_1025 -> begin
(
# 816 "FStar.TypeChecker.Rel.fst"
let _55_1028 = (sub_prob scope args q)
in (match (_55_1028) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_55_1031) with
| (tc, probs) -> begin
(
# 819 "FStar.TypeChecker.Rel.fst"
let _55_1044 = (match (q) with
| (Some (b), _55_1035, _55_1037) -> begin
(let _144_611 = (let _144_610 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_144_610)::args)
in (Some (b), (b)::scope, _144_611))
end
| _55_1040 -> begin
(None, scope, args)
end)
in (match (_55_1044) with
| (bopt, scope, args) -> begin
(
# 823 "FStar.TypeChecker.Rel.fst"
let _55_1048 = (aux scope args qs)
in (match (_55_1048) with
| (sub_probs, tcs, f) -> begin
(
# 824 "FStar.TypeChecker.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _144_614 = (let _144_613 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_144_613)
in (FStar_Syntax_Util.mk_conj_l _144_614))
end
| Some (b) -> begin
(let _144_618 = (let _144_617 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _144_616 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_144_617)::_144_616))
in (FStar_Syntax_Util.mk_conj_l _144_618))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 839 "FStar.TypeChecker.Rel.fst"
let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 840 "FStar.TypeChecker.Rel.fst"
let t1 = (FStar_Syntax_Subst.compress t1)
in (
# 841 "FStar.TypeChecker.Rel.fst"
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _55_1076), FStar_Syntax_Syntax.Tm_uvar (u2, _55_1081)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _55_1095 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _55_1101 _55_1105 -> (match ((_55_1101, _55_1105)) with
| ((a1, _55_1100), (a2, _55_1104)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 858 "FStar.TypeChecker.Rel.fst"
type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 859 "FStar.TypeChecker.Rel.fst"
type im_or_proj_t =
(((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) * FStar_Syntax_Syntax.arg Prims.list * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 863 "FStar.TypeChecker.Rel.fst"
let rigid_rigid : Prims.int = 0

# 864 "FStar.TypeChecker.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 865 "FStar.TypeChecker.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 866 "FStar.TypeChecker.Rel.fst"
let flex_refine : Prims.int = 3

# 867 "FStar.TypeChecker.Rel.fst"
let flex_rigid : Prims.int = 4

# 868 "FStar.TypeChecker.Rel.fst"
let rigid_flex : Prims.int = 5

# 869 "FStar.TypeChecker.Rel.fst"
let refine_flex : Prims.int = 6

# 870 "FStar.TypeChecker.Rel.fst"
let flex_flex : Prims.int = 7

# 871 "FStar.TypeChecker.Rel.fst"
let compress_tprob = (fun wl p -> (
# 871 "FStar.TypeChecker.Rel.fst"
let _55_1108 = p
in (let _144_640 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _144_639 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _55_1108.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_640; FStar_TypeChecker_Common.relation = _55_1108.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_639; FStar_TypeChecker_Common.element = _55_1108.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1108.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1108.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1108.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1108.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1108.FStar_TypeChecker_Common.rank}))))

# 873 "FStar.TypeChecker.Rel.fst"
let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _144_646 = (compress_tprob wl p)
in (FStar_All.pipe_right _144_646 (fun _144_645 -> FStar_TypeChecker_Common.TProb (_144_645))))
end
| FStar_TypeChecker_Common.CProb (_55_1115) -> begin
p
end))

# 878 "FStar.TypeChecker.Rel.fst"
let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (
# 881 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_651 = (compress_prob wl pr)
in (FStar_All.pipe_right _144_651 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(
# 884 "FStar.TypeChecker.Rel.fst"
let _55_1125 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1125) with
| (lh, _55_1124) -> begin
(
# 885 "FStar.TypeChecker.Rel.fst"
let _55_1129 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1129) with
| (rh, _55_1128) -> begin
(
# 886 "FStar.TypeChecker.Rel.fst"
let _55_1185 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_55_1131), FStar_Syntax_Syntax.Tm_uvar (_55_1134)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_55_1150), _55_1153) -> begin
(
# 893 "FStar.TypeChecker.Rel.fst"
let _55_1157 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1157) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _55_1160 -> begin
(
# 897 "FStar.TypeChecker.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _144_653 = (
# 901 "FStar.TypeChecker.Rel.fst"
let _55_1162 = tp
in (let _144_652 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1162.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1162.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1162.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_652; FStar_TypeChecker_Common.element = _55_1162.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1162.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1162.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1162.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1162.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1162.FStar_TypeChecker_Common.rank}))
in (rank, _144_653)))
end)
end))
end
| (_55_1165, FStar_Syntax_Syntax.Tm_uvar (_55_1167)) -> begin
(
# 905 "FStar.TypeChecker.Rel.fst"
let _55_1172 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1172) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _55_1175 -> begin
(let _144_655 = (
# 908 "FStar.TypeChecker.Rel.fst"
let _55_1176 = tp
in (let _144_654 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _55_1176.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_654; FStar_TypeChecker_Common.relation = _55_1176.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1176.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1176.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1176.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1176.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1176.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1176.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1176.FStar_TypeChecker_Common.rank}))
in (refine_flex, _144_655))
end)
end))
end
| (_55_1179, _55_1181) -> begin
(rigid_rigid, tp)
end)
in (match (_55_1185) with
| (rank, tp) -> begin
(let _144_657 = (FStar_All.pipe_right (
# 913 "FStar.TypeChecker.Rel.fst"
let _55_1186 = tp
in {FStar_TypeChecker_Common.pid = _55_1186.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1186.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1186.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1186.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1186.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1186.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1186.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1186.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1186.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _144_656 -> FStar_TypeChecker_Common.TProb (_144_656)))
in (rank, _144_657))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _144_659 = (FStar_All.pipe_right (
# 915 "FStar.TypeChecker.Rel.fst"
let _55_1190 = cp
in {FStar_TypeChecker_Common.pid = _55_1190.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_1190.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_1190.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_1190.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_1190.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1190.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1190.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1190.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1190.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _144_658 -> FStar_TypeChecker_Common.CProb (_144_658)))
in (rigid_rigid, _144_659))
end)))

# 917 "FStar.TypeChecker.Rel.fst"
let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (
# 921 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun _55_1197 probs -> (match (_55_1197) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 924 "FStar.TypeChecker.Rel.fst"
let _55_1205 = (rank wl hd)
in (match (_55_1205) with
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

# 938 "FStar.TypeChecker.Rel.fst"
let is_rigid_flex : Prims.int  ->  Prims.bool = (fun rank -> ((rigid_flex <= rank) && (rank <= refine_flex)))

# 943 "FStar.TypeChecker.Rel.fst"
type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 944 "FStar.TypeChecker.Rel.fst"
let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 945 "FStar.TypeChecker.Rel.fst"
let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 946 "FStar.TypeChecker.Rel.fst"
let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 944 "FStar.TypeChecker.Rel.fst"
let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_55_1216) -> begin
_55_1216
end))

# 945 "FStar.TypeChecker.Rel.fst"
let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_55_1219) -> begin
_55_1219
end))

# 946 "FStar.TypeChecker.Rel.fst"
let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_55_1222) -> begin
_55_1222
end))

# 948 "FStar.TypeChecker.Rel.fst"
let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (
# 949 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (
# 950 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (
# 951 "FStar.TypeChecker.Rel.fst"
let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (
# 954 "FStar.TypeChecker.Rel.fst"
let _55_1238 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_1238) with
| (k, _55_1237) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _55_1242 -> begin
false
end)
end)))))
end
| _55_1244 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (
# 960 "FStar.TypeChecker.Rel.fst"
let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (us1), FStar_Syntax_Syntax.U_max (us2)) -> begin
if ((FStar_List.length us1) = (FStar_List.length us2)) then begin
(
# 964 "FStar.TypeChecker.Rel.fst"
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
| _55_1269 -> begin
USolved (wl)
end))
in (aux wl us1 us2))
end else begin
(let _144_739 = (let _144_738 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_737 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _144_738 _144_737)))
in UFailed (_144_739))
end
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(
# 977 "FStar.TypeChecker.Rel.fst"
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
| _55_1287 -> begin
(let _144_746 = (let _144_745 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_744 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _144_745 _144_744 msg)))
in UFailed (_144_746))
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
# 1009 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(
# 1014 "FStar.TypeChecker.Rel.fst"
let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _144_749 = (let _144_748 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _144_747 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _144_748 _144_747)))
in (try_umax_components u1 u2 _144_749))
end else begin
(let _144_750 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_144_750))
end)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(
# 1024 "FStar.TypeChecker.Rel.fst"
let u1 = (norm_univ wl u1)
in (
# 1025 "FStar.TypeChecker.Rel.fst"
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

# 1041 "FStar.TypeChecker.Rel.fst"
let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (
# 1043 "FStar.TypeChecker.Rel.fst"
let _55_1384 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_796 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _144_796))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1047 "FStar.TypeChecker.Rel.fst"
let probs = (
# 1047 "FStar.TypeChecker.Rel.fst"
let _55_1391 = probs
in {attempting = tl; wl_deferred = _55_1391.wl_deferred; ctr = _55_1391.ctr; defer_ok = _55_1391.defer_ok; smt_ok = _55_1391.smt_ok; tcenv = _55_1391.tcenv})
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
| (None, _55_1406, _55_1408) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _55_1412 -> begin
(
# 1074 "FStar.TypeChecker.Rel.fst"
let _55_1421 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _55_1418 -> (match (_55_1418) with
| (c, _55_1415, _55_1417) -> begin
(c < probs.ctr)
end))))
in (match (_55_1421) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _144_799 = (FStar_List.map (fun _55_1427 -> (match (_55_1427) with
| (_55_1424, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_144_799))
end
| _55_1429 -> begin
(let _144_802 = (
# 1080 "FStar.TypeChecker.Rel.fst"
let _55_1430 = probs
in (let _144_801 = (FStar_All.pipe_right attempt (FStar_List.map (fun _55_1437 -> (match (_55_1437) with
| (_55_1433, _55_1435, y) -> begin
y
end))))
in {attempting = _144_801; wl_deferred = rest; ctr = _55_1430.ctr; defer_ok = _55_1430.defer_ok; smt_ok = _55_1430.smt_ok; tcenv = _55_1430.tcenv}))
in (solve env _144_802))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _144_808 = (solve_prob orig None [] wl)
in (solve env _144_808))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (
# 1094 "FStar.TypeChecker.Rel.fst"
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
| _55_1472 -> begin
UFailed ("Unequal number of universes")
end))
in (
# 1107 "FStar.TypeChecker.Rel.fst"
let t1 = (whnf env t1)
in (
# 1108 "FStar.TypeChecker.Rel.fst"
let t2 = (whnf env t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _55_1480; FStar_Syntax_Syntax.pos = _55_1478; FStar_Syntax_Syntax.vars = _55_1476}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _55_1492; FStar_Syntax_Syntax.pos = _55_1490; FStar_Syntax_Syntax.vars = _55_1488}, us2)) -> begin
(
# 1111 "FStar.TypeChecker.Rel.fst"
let b = (FStar_Syntax_Syntax.fv_eq f g)
in (
# 1112 "FStar.TypeChecker.Rel.fst"
let _55_1501 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _55_1516 -> begin
USolved (wl)
end)))))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(
# 1125 "FStar.TypeChecker.Rel.fst"
let _55_1521 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_824 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _144_824 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_rigid_flex_meet : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1135 "FStar.TypeChecker.Rel.fst"
let _55_1526 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_828 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by meeting refinements:%s\n" _144_828))
end else begin
()
end
in (
# 1137 "FStar.TypeChecker.Rel.fst"
let _55_1530 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1530) with
| (u, args) -> begin
(
# 1139 "FStar.TypeChecker.Rel.fst"
let disjoin = (fun t1 t2 -> (
# 1140 "FStar.TypeChecker.Rel.fst"
let _55_1536 = (head_matches_delta env () t1 t2)
in (match (_55_1536) with
| (mr, ts) -> begin
(match (mr) with
| MisMatch (_55_1538) -> begin
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
# 1153 "FStar.TypeChecker.Rel.fst"
let _55_1554 = (match (ts) with
| Some (t1, t2) -> begin
(let _144_834 = (FStar_Syntax_Subst.compress t1)
in (let _144_833 = (FStar_Syntax_Subst.compress t2)
in (_144_834, _144_833)))
end
| None -> begin
(let _144_836 = (FStar_Syntax_Subst.compress t1)
in (let _144_835 = (FStar_Syntax_Subst.compress t2)
in (_144_836, _144_835)))
end)
in (match (_55_1554) with
| (t1, t2) -> begin
(
# 1156 "FStar.TypeChecker.Rel.fst"
let eq_prob = (fun t1 t2 -> (let _144_842 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "meeting refinements")
in (FStar_All.pipe_left (fun _144_841 -> FStar_TypeChecker_Common.TProb (_144_841)) _144_842)))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let _144_849 = (let _144_848 = (let _144_845 = (let _144_844 = (let _144_843 = (FStar_Syntax_Util.mk_disj phi1 phi2)
in (x, _144_843))
in FStar_Syntax_Syntax.Tm_refine (_144_844))
in (FStar_Syntax_Syntax.mk _144_845 None t1.FStar_Syntax_Syntax.pos))
in (let _144_847 = (let _144_846 = (eq_prob x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (_144_846)::[])
in (_144_848, _144_847)))
in Some (_144_849))
end
| (_55_1568, FStar_Syntax_Syntax.Tm_refine (x, _55_1571)) -> begin
(let _144_852 = (let _144_851 = (let _144_850 = (eq_prob x.FStar_Syntax_Syntax.sort t1)
in (_144_850)::[])
in (t1, _144_851))
in Some (_144_852))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1577), _55_1581) -> begin
(let _144_855 = (let _144_854 = (let _144_853 = (eq_prob x.FStar_Syntax_Syntax.sort t2)
in (_144_853)::[])
in (t2, _144_854))
in Some (_144_855))
end
| _55_1584 -> begin
None
end))
end))
end)
end)))
in (
# 1172 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1588) -> begin
(
# 1176 "FStar.TypeChecker.Rel.fst"
let _55_1613 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_23 -> (match (_55_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_rigid_flex rank) -> begin
(
# 1180 "FStar.TypeChecker.Rel.fst"
let _55_1599 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_55_1599) with
| (u', _55_1598) -> begin
(match ((let _144_857 = (whnf env u')
in _144_857.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1602) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1606 -> begin
false
end)
end))
end
| _55_1608 -> begin
false
end)
end
| _55_1610 -> begin
false
end))))
in (match (_55_1613) with
| (lower_bounds, rest) -> begin
(
# 1189 "FStar.TypeChecker.Rel.fst"
let rec make_lower_bound = (fun _55_1617 tps -> (match (_55_1617) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _144_862 = (whnf env hd.FStar_TypeChecker_Common.lhs)
in (disjoin bound _144_862))) with
| Some (bound, sub) -> begin
(make_lower_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1630 -> begin
None
end)
end))
in (match ((let _144_864 = (let _144_863 = (whnf env tp.FStar_TypeChecker_Common.lhs)
in (_144_863, []))
in (make_lower_bound _144_864 lower_bounds))) with
| None -> begin
(
# 1200 "FStar.TypeChecker.Rel.fst"
let _55_1632 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No lower bounds\n")
end else begin
()
end
in None)
end
| Some (lhs_bound, sub_probs) -> begin
(
# 1205 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env lhs_bound FStar_TypeChecker_Common.EQ tp.FStar_TypeChecker_Common.rhs None tp.FStar_TypeChecker_Common.loc "meeting refinements")
in (
# 1206 "FStar.TypeChecker.Rel.fst"
let _55_1642 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1207 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1207 "FStar.TypeChecker.Rel.fst"
let _55_1639 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1639.wl_deferred; ctr = _55_1639.ctr; defer_ok = _55_1639.defer_ok; smt_ok = _55_1639.smt_ok; tcenv = _55_1639.tcenv})
in (let _144_865 = (wl_to_string wl')
in (FStar_Util.print1 "After meeting refinements: %s\n" _144_865)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1209 "FStar.TypeChecker.Rel.fst"
let _55_1644 = wl
in {attempting = sub_probs; wl_deferred = _55_1644.wl_deferred; ctr = _55_1644.ctr; defer_ok = _55_1644.defer_ok; smt_ok = _55_1644.smt_ok; tcenv = _55_1644.tcenv}))) with
| Success (_55_1647) -> begin
(
# 1211 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1211 "FStar.TypeChecker.Rel.fst"
let _55_1649 = wl
in {attempting = rest; wl_deferred = _55_1649.wl_deferred; ctr = _55_1649.ctr; defer_ok = _55_1649.defer_ok; smt_ok = _55_1649.smt_ok; tcenv = _55_1649.tcenv})
in (
# 1212 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1213 "FStar.TypeChecker.Rel.fst"
let _55_1655 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl lower_bounds)
in Some (wl))))
end
| _55_1658 -> begin
None
end)))
end))
end))
end
| _55_1660 -> begin
(FStar_All.failwith "Impossible: Not a rigid-flex")
end)))
end))))
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1224 "FStar.TypeChecker.Rel.fst"
let _55_1664 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_871 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _144_871))
end else begin
()
end
in (
# 1226 "FStar.TypeChecker.Rel.fst"
let _55_1668 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1668) with
| (u, args) -> begin
(
# 1227 "FStar.TypeChecker.Rel.fst"
let _55_1674 = (0, 1, 2, 3, 4)
in (match (_55_1674) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1228 "FStar.TypeChecker.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1230 "FStar.TypeChecker.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1231 "FStar.TypeChecker.Rel.fst"
let _55_1683 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1683) with
| (h1, args1) -> begin
(
# 1232 "FStar.TypeChecker.Rel.fst"
let _55_1687 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1687) with
| (h2, _55_1686) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _144_883 = (let _144_882 = (let _144_881 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _144_880 -> FStar_TypeChecker_Common.TProb (_144_880)) _144_881))
in (_144_882)::[])
in Some (_144_883))
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
| _55_1699 -> begin
None
end)
end))
end)))
in (
# 1248 "FStar.TypeChecker.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(
# 1250 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1254 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.freshen_bv x)
in (
# 1255 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x)))::[]
in (
# 1256 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1257 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _144_890 = (let _144_889 = (let _144_888 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _144_888))
in (_144_889, m))
in Some (_144_890))))))
end))
end
| (_55_1721, FStar_Syntax_Syntax.Tm_refine (y, _55_1724)) -> begin
(
# 1262 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _55_1734), _55_1738) -> begin
(
# 1269 "FStar.TypeChecker.Rel.fst"
let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _55_1745 -> begin
(
# 1276 "FStar.TypeChecker.Rel.fst"
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
# 1282 "FStar.TypeChecker.Rel.fst"
let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _55_1753) -> begin
(
# 1286 "FStar.TypeChecker.Rel.fst"
let _55_1778 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _55_24 -> (match (_55_24) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1290 "FStar.TypeChecker.Rel.fst"
let _55_1764 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_55_1764) with
| (u', _55_1763) -> begin
(match ((let _144_892 = (whnf env u')
in _144_892.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _55_1767) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _55_1771 -> begin
false
end)
end))
end
| _55_1773 -> begin
false
end)
end
| _55_1775 -> begin
false
end))))
in (match (_55_1778) with
| (upper_bounds, rest) -> begin
(
# 1299 "FStar.TypeChecker.Rel.fst"
let rec make_upper_bound = (fun _55_1782 tps -> (match (_55_1782) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _144_897 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _144_897))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _55_1795 -> begin
None
end)
end))
in (match ((let _144_899 = (let _144_898 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_144_898, []))
in (make_upper_bound _144_899 upper_bounds))) with
| None -> begin
(
# 1310 "FStar.TypeChecker.Rel.fst"
let _55_1797 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1323 "FStar.TypeChecker.Rel.fst"
let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (
# 1324 "FStar.TypeChecker.Rel.fst"
let _55_1807 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(
# 1325 "FStar.TypeChecker.Rel.fst"
let wl' = (
# 1325 "FStar.TypeChecker.Rel.fst"
let _55_1804 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _55_1804.wl_deferred; ctr = _55_1804.ctr; defer_ok = _55_1804.defer_ok; smt_ok = _55_1804.smt_ok; tcenv = _55_1804.tcenv})
in (let _144_900 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _144_900)))
end else begin
()
end
in (match ((solve_t env eq_prob (
# 1327 "FStar.TypeChecker.Rel.fst"
let _55_1809 = wl
in {attempting = sub_probs; wl_deferred = _55_1809.wl_deferred; ctr = _55_1809.ctr; defer_ok = _55_1809.defer_ok; smt_ok = _55_1809.smt_ok; tcenv = _55_1809.tcenv}))) with
| Success (_55_1812) -> begin
(
# 1329 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1329 "FStar.TypeChecker.Rel.fst"
let _55_1814 = wl
in {attempting = rest; wl_deferred = _55_1814.wl_deferred; ctr = _55_1814.ctr; defer_ok = _55_1814.defer_ok; smt_ok = _55_1814.smt_ok; tcenv = _55_1814.tcenv})
in (
# 1330 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (
# 1331 "FStar.TypeChecker.Rel.fst"
let _55_1820 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _55_1823 -> begin
None
end)))
end))
end))
end
| _55_1825 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1341 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1344 "FStar.TypeChecker.Rel.fst"
let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (
# 1345 "FStar.TypeChecker.Rel.fst"
let _55_1842 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_928 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _144_928))
end else begin
()
end
in (
# 1347 "FStar.TypeChecker.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(
# 1351 "FStar.TypeChecker.Rel.fst"
let hd1 = (
# 1351 "FStar.TypeChecker.Rel.fst"
let _55_1856 = hd1
in (let _144_929 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1856.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1856.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_929}))
in (
# 1352 "FStar.TypeChecker.Rel.fst"
let hd2 = (
# 1352 "FStar.TypeChecker.Rel.fst"
let _55_1859 = hd2
in (let _144_930 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1859.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1859.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _144_930}))
in (
# 1353 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_933 = (let _144_932 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _144_932 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _144_931 -> FStar_TypeChecker_Common.TProb (_144_931)) _144_933))
in (
# 1354 "FStar.TypeChecker.Rel.fst"
let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (
# 1355 "FStar.TypeChecker.Rel.fst"
let subst = (let _144_934 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (FStar_Syntax_Syntax.DB ((0, hd1)))::_144_934)
in (
# 1356 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1359 "FStar.TypeChecker.Rel.fst"
let phi = (let _144_936 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _144_935 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _144_936 _144_935)))
in (
# 1360 "FStar.TypeChecker.Rel.fst"
let _55_1871 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_938 = (FStar_Syntax_Print.term_to_string phi)
in (let _144_937 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _144_938 _144_937)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _55_1875 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1369 "FStar.TypeChecker.Rel.fst"
let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1373 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _144_942 = (compress_tprob wl problem)
in (solve_t' env _144_942 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (
# 1380 "FStar.TypeChecker.Rel.fst"
let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (
# 1383 "FStar.TypeChecker.Rel.fst"
let rigid_rigid_delta = (fun env orig wl head1 head2 t1 t2 -> (
# 1384 "FStar.TypeChecker.Rel.fst"
let _55_1903 = (head_matches_delta env wl t1 t2)
in (match (_55_1903) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch (_55_1905), _55_1908) -> begin
(
# 1387 "FStar.TypeChecker.Rel.fst"
let may_relate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc) -> begin
(tc.FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_equational)
end
| _55_1921 -> begin
false
end))
in if (((may_relate head1) || (may_relate head2)) && wl.smt_ok) then begin
(
# 1393 "FStar.TypeChecker.Rel.fst"
let guard = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
end else begin
(
# 1396 "FStar.TypeChecker.Rel.fst"
let has_type_guard = (fun t1 t2 -> (match (problem.FStar_TypeChecker_Common.element) with
| Some (t) -> begin
(FStar_Syntax_Util.mk_has_type t1 t t2)
end
| None -> begin
(
# 1400 "FStar.TypeChecker.Rel.fst"
let x = (FStar_Syntax_Syntax.new_bv None t1)
in (let _144_971 = (let _144_970 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Util.mk_has_type t1 _144_970 t2))
in (FStar_Syntax_Util.mk_forall x _144_971)))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUB) then begin
(has_type_guard t1 t2)
end else begin
(has_type_guard t2 t1)
end)
end
in (let _144_972 = (solve_prob orig (Some (guard)) [] wl)
in (solve env _144_972)))
end else begin
(giveup env "head mismatch" orig)
end)
end
| (_55_1931, Some (t1, t2)) -> begin
(solve_t env (
# 1409 "FStar.TypeChecker.Rel.fst"
let _55_1937 = problem
in {FStar_TypeChecker_Common.pid = _55_1937.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_1937.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_1937.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1937.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1937.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1937.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1937.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1937.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_1940, None) -> begin
(
# 1412 "FStar.TypeChecker.Rel.fst"
let _55_1943 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_976 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_975 = (FStar_Syntax_Print.tag_of_term t1)
in (let _144_974 = (FStar_Syntax_Print.term_to_string t2)
in (let _144_973 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _144_976 _144_975 _144_974 _144_973)))))
end else begin
()
end
in (
# 1416 "FStar.TypeChecker.Rel.fst"
let _55_1947 = (FStar_Syntax_Util.head_and_args t1)
in (match (_55_1947) with
| (head1, args1) -> begin
(
# 1417 "FStar.TypeChecker.Rel.fst"
let _55_1950 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_1950) with
| (head2, args2) -> begin
(
# 1418 "FStar.TypeChecker.Rel.fst"
let nargs = (FStar_List.length args1)
in if (nargs <> (FStar_List.length args2)) then begin
(let _144_981 = (let _144_980 = (FStar_Syntax_Print.term_to_string head1)
in (let _144_979 = (args_to_string args1)
in (let _144_978 = (FStar_Syntax_Print.term_to_string head2)
in (let _144_977 = (args_to_string args2)
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _144_980 _144_979 _144_978 _144_977)))))
in (giveup env _144_981 orig))
end else begin
if ((nargs = 0) || (eq_args args1 args2)) then begin
(match ((solve_maybe_uinsts env orig head1 head2 wl)) with
| USolved (wl) -> begin
(let _144_982 = (solve_prob orig None [] wl)
in (solve env _144_982))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(
# 1439 "FStar.TypeChecker.Rel.fst"
let _55_1960 = (base_and_refinement env wl t1)
in (match (_55_1960) with
| (base1, refinement1) -> begin
(
# 1440 "FStar.TypeChecker.Rel.fst"
let _55_1963 = (base_and_refinement env wl t2)
in (match (_55_1963) with
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
# 1447 "FStar.TypeChecker.Rel.fst"
let subprobs = (FStar_List.map2 (fun _55_1976 _55_1980 -> (match ((_55_1976, _55_1980)) with
| ((a, _55_1975), (a', _55_1979)) -> begin
(let _144_986 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _144_985 -> FStar_TypeChecker_Common.TProb (_144_985)) _144_986))
end)) args1 args2)
in (
# 1448 "FStar.TypeChecker.Rel.fst"
let formula = (let _144_988 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _144_988))
in (
# 1449 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _55_1986 -> begin
(
# 1454 "FStar.TypeChecker.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 1455 "FStar.TypeChecker.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 1456 "FStar.TypeChecker.Rel.fst"
let _55_1989 = problem
in {FStar_TypeChecker_Common.pid = _55_1989.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _55_1989.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _55_1989.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_1989.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_1989.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_1989.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_1989.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_1989.FStar_TypeChecker_Common.rank}) wl)))
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
# 1462 "FStar.TypeChecker.Rel.fst"
let imitate = (fun orig env wl p -> (
# 1463 "FStar.TypeChecker.Rel.fst"
let _55_2008 = p
in (match (_55_2008) with
| (((u, k), xs, c), ps, (h, _55_2005, qs)) -> begin
(
# 1464 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1469 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1470 "FStar.TypeChecker.Rel.fst"
let _55_2014 = (imitation_sub_probs orig env xs ps qs)
in (match (_55_2014) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1471 "FStar.TypeChecker.Rel.fst"
let im = (let _144_1003 = (h gs_xs)
in (let _144_1002 = (let _144_1001 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_999 -> FStar_Util.Inl (_144_999)))
in (FStar_All.pipe_right _144_1001 (fun _144_1000 -> Some (_144_1000))))
in (FStar_Syntax_Util.abs xs _144_1003 _144_1002)))
in (
# 1472 "FStar.TypeChecker.Rel.fst"
let _55_2016 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1010 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _144_1009 = (FStar_Syntax_Print.comp_to_string c)
in (let _144_1008 = (FStar_Syntax_Print.term_to_string im)
in (let _144_1007 = (FStar_Syntax_Print.tag_of_term im)
in (let _144_1006 = (let _144_1004 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _144_1004 (FStar_String.concat ", ")))
in (let _144_1005 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print6 "Imitating  binders are %s, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n" _144_1010 _144_1009 _144_1008 _144_1007 _144_1006 _144_1005)))))))
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
# 1483 "FStar.TypeChecker.Rel.fst"
let imitate' = (fun orig env wl _55_25 -> (match (_55_25) with
| None -> begin
(giveup env "unable to compute subterms" orig)
end
| Some (p) -> begin
(imitate orig env wl p)
end))
in (
# 1488 "FStar.TypeChecker.Rel.fst"
let project = (fun orig env wl i p -> (
# 1489 "FStar.TypeChecker.Rel.fst"
let _55_2042 = p
in (match (_55_2042) with
| ((u, xs, c), ps, (h, matches, qs)) -> begin
(
# 1493 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1494 "FStar.TypeChecker.Rel.fst"
let _55_2047 = (FStar_List.nth ps i)
in (match (_55_2047) with
| (pi, _55_2046) -> begin
(
# 1495 "FStar.TypeChecker.Rel.fst"
let _55_2051 = (FStar_List.nth xs i)
in (match (_55_2051) with
| (xi, _55_2050) -> begin
(
# 1497 "FStar.TypeChecker.Rel.fst"
let rec gs = (fun k -> (
# 1498 "FStar.TypeChecker.Rel.fst"
let _55_2056 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2056) with
| (bs, k) -> begin
(
# 1499 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _55_2064)::tl -> begin
(
# 1502 "FStar.TypeChecker.Rel.fst"
let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (
# 1503 "FStar.TypeChecker.Rel.fst"
let _55_2070 = (new_uvar r xs k_a)
in (match (_55_2070) with
| (gi_xs, gi) -> begin
(
# 1504 "FStar.TypeChecker.Rel.fst"
let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (
# 1505 "FStar.TypeChecker.Rel.fst"
let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (
# 1506 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
in (
# 1507 "FStar.TypeChecker.Rel.fst"
let _55_2076 = (aux subst tl)
in (match (_55_2076) with
| (gi_xs', gi_ps') -> begin
(let _144_1040 = (let _144_1037 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_144_1037)::gi_xs')
in (let _144_1039 = (let _144_1038 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_144_1038)::gi_ps')
in (_144_1040, _144_1039)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _144_1041 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _144_1041)) then begin
None
end else begin
(
# 1513 "FStar.TypeChecker.Rel.fst"
let _55_2080 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_55_2080) with
| (g_xs, _55_2079) -> begin
(
# 1514 "FStar.TypeChecker.Rel.fst"
let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (
# 1515 "FStar.TypeChecker.Rel.fst"
let proj = (let _144_1046 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (let _144_1045 = (let _144_1044 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _144_1042 -> FStar_Util.Inl (_144_1042)))
in (FStar_All.pipe_right _144_1044 (fun _144_1043 -> Some (_144_1043))))
in (FStar_Syntax_Util.abs xs _144_1046 _144_1045)))
in (
# 1516 "FStar.TypeChecker.Rel.fst"
let sub = (let _144_1052 = (let _144_1051 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _144_1050 = (let _144_1049 = (FStar_List.map (fun _55_2088 -> (match (_55_2088) with
| (_55_2084, _55_2086, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _144_1049))
in (mk_problem (p_scope orig) orig _144_1051 (p_rel orig) _144_1050 None "projection")))
in (FStar_All.pipe_left (fun _144_1047 -> FStar_TypeChecker_Common.TProb (_144_1047)) _144_1052))
in (
# 1517 "FStar.TypeChecker.Rel.fst"
let _55_2090 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1054 = (FStar_Syntax_Print.term_to_string proj)
in (let _144_1053 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _144_1054 _144_1053)))
end else begin
()
end
in (
# 1518 "FStar.TypeChecker.Rel.fst"
let wl = (let _144_1056 = (let _144_1055 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_144_1055))
in (solve_prob orig _144_1056 ((TERM ((u, proj)))::[]) wl))
in (let _144_1058 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _144_1057 -> Some (_144_1057)) _144_1058)))))))
end))
end)
end))
end)))
end)))
in (
# 1523 "FStar.TypeChecker.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1524 "FStar.TypeChecker.Rel.fst"
let _55_2104 = lhs
in (match (_55_2104) with
| ((t1, uv, k_uv, args_lhs), maybe_pat_vars) -> begin
(
# 1525 "FStar.TypeChecker.Rel.fst"
let subterms = (fun ps -> (
# 1526 "FStar.TypeChecker.Rel.fst"
let _55_2109 = (FStar_Syntax_Util.arrow_formals_comp k_uv)
in (match (_55_2109) with
| (xs, c) -> begin
if ((FStar_List.length xs) = (FStar_List.length ps)) then begin
(let _144_1080 = (let _144_1079 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _144_1079))
in Some (_144_1080))
end else begin
(
# 1529 "FStar.TypeChecker.Rel.fst"
let k_uv = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env k_uv)
in (
# 1530 "FStar.TypeChecker.Rel.fst"
let rec elim = (fun k args -> (match ((let _144_1086 = (let _144_1085 = (FStar_Syntax_Subst.compress k)
in _144_1085.FStar_Syntax_Syntax.n)
in (_144_1086, args))) with
| (_55_2115, []) -> begin
(let _144_1088 = (let _144_1087 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _144_1087))
in Some (_144_1088))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) -> begin
(
# 1535 "FStar.TypeChecker.Rel.fst"
let _55_2132 = (FStar_Syntax_Util.head_and_args k)
in (match (_55_2132) with
| (uv, uv_args) -> begin
(match ((let _144_1089 = (FStar_Syntax_Subst.compress uv)
in _144_1089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, _55_2135) -> begin
(match ((pat_vars env [] uv_args)) with
| None -> begin
None
end
| Some (scope) -> begin
(
# 1541 "FStar.TypeChecker.Rel.fst"
let xs = (FStar_All.pipe_right args (FStar_List.map (fun _55_2141 -> (let _144_1095 = (let _144_1094 = (let _144_1093 = (let _144_1092 = (let _144_1091 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1091 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _144_1092))
in (Prims.fst _144_1093))
in (FStar_Syntax_Syntax.new_bv (Some (k.FStar_Syntax_Syntax.pos)) _144_1094))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder _144_1095)))))
in (
# 1545 "FStar.TypeChecker.Rel.fst"
let c = (let _144_1099 = (let _144_1098 = (let _144_1097 = (let _144_1096 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1096 Prims.fst))
in (new_uvar k.FStar_Syntax_Syntax.pos scope _144_1097))
in (Prims.fst _144_1098))
in (FStar_Syntax_Syntax.mk_Total _144_1099))
in (
# 1546 "FStar.TypeChecker.Rel.fst"
let k' = (FStar_Syntax_Util.arrow xs c)
in (
# 1547 "FStar.TypeChecker.Rel.fst"
let uv_sol = (let _144_1105 = (let _144_1104 = (let _144_1103 = (let _144_1102 = (let _144_1101 = (let _144_1100 = (FStar_Syntax_Util.type_u ())
in (FStar_All.pipe_right _144_1100 Prims.fst))
in (FStar_Syntax_Syntax.mk_Total _144_1101))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _144_1102))
in FStar_Util.Inl (_144_1103))
in Some (_144_1104))
in (FStar_Syntax_Util.abs scope k' _144_1105))
in (
# 1548 "FStar.TypeChecker.Rel.fst"
let _55_2147 = (FStar_Unionfind.change uvar (FStar_Syntax_Syntax.Fixed (uv_sol)))
in Some ((xs, c)))))))
end)
end
| _55_2150 -> begin
None
end)
end))
end
| (FStar_Syntax_Syntax.Tm_arrow (xs, c), _55_2156) -> begin
(
# 1553 "FStar.TypeChecker.Rel.fst"
let n_args = (FStar_List.length args)
in (
# 1554 "FStar.TypeChecker.Rel.fst"
let n_xs = (FStar_List.length xs)
in if (n_xs = n_args) then begin
(let _144_1107 = (FStar_Syntax_Subst.open_comp xs c)
in (FStar_All.pipe_right _144_1107 (fun _144_1106 -> Some (_144_1106))))
end else begin
if (n_xs < n_args) then begin
(
# 1558 "FStar.TypeChecker.Rel.fst"
let _55_2162 = (FStar_Util.first_N n_xs args)
in (match (_55_2162) with
| (args, rest) -> begin
(
# 1559 "FStar.TypeChecker.Rel.fst"
let _55_2165 = (FStar_Syntax_Subst.open_comp xs c)
in (match (_55_2165) with
| (xs, c) -> begin
(let _144_1109 = (elim (FStar_Syntax_Util.comp_result c) rest)
in (FStar_Util.bind_opt _144_1109 (fun _55_2168 -> (match (_55_2168) with
| (xs', c) -> begin
Some (((FStar_List.append xs xs'), c))
end))))
end))
end))
end else begin
(
# 1564 "FStar.TypeChecker.Rel.fst"
let _55_2171 = (FStar_Util.first_N n_args xs)
in (match (_55_2171) with
| (xs, rest) -> begin
(
# 1565 "FStar.TypeChecker.Rel.fst"
let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((rest, c))) None k.FStar_Syntax_Syntax.pos)
in (let _144_1112 = (let _144_1110 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Subst.open_comp xs _144_1110))
in (FStar_All.pipe_right _144_1112 (fun _144_1111 -> Some (_144_1111)))))
end))
end
end))
end
| _55_2174 -> begin
(let _144_1116 = (let _144_1115 = (FStar_Syntax_Print.uvar_to_string uv)
in (let _144_1114 = (FStar_Syntax_Print.term_to_string k)
in (let _144_1113 = (FStar_Syntax_Print.term_to_string k_uv)
in (FStar_Util.format3 "Impossible: ill-typed application %s : %s\n\t%s" _144_1115 _144_1114 _144_1113))))
in (FStar_All.failwith _144_1116))
end))
in (let _144_1154 = (elim k_uv ps)
in (FStar_Util.bind_opt _144_1154 (fun _55_2177 -> (match (_55_2177) with
| (xs, c) -> begin
(let _144_1153 = (let _144_1152 = (decompose env t2)
in (((uv, k_uv), xs, c), ps, _144_1152))
in Some (_144_1153))
end))))))
end
end)))
in (
# 1575 "FStar.TypeChecker.Rel.fst"
let rec imitate_or_project = (fun n stopt i -> if ((i >= n) || (FStar_Option.isNone stopt)) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(
# 1578 "FStar.TypeChecker.Rel.fst"
let st = (FStar_Option.get stopt)
in (
# 1579 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_55_2185) -> begin
(
# 1583 "FStar.TypeChecker.Rel.fst"
let _55_2187 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(
# 1590 "FStar.TypeChecker.Rel.fst"
let _55_2195 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n stopt (i + 1)))
end
| Some (sol) -> begin
sol
end)
end))
end)
in (
# 1594 "FStar.TypeChecker.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1595 "FStar.TypeChecker.Rel.fst"
let _55_2205 = (FStar_Syntax_Util.head_and_args t2)
in (match (_55_2205) with
| (hd, _55_2204) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _55_2216 -> begin
(
# 1601 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(
# 1604 "FStar.TypeChecker.Rel.fst"
let _55_2218 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1165 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _144_1165))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1607 "FStar.TypeChecker.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1608 "FStar.TypeChecker.Rel.fst"
let fvs_hd = (let _144_1169 = (let _144_1168 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _144_1168 Prims.fst))
in (FStar_All.pipe_right _144_1169 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1615 "FStar.TypeChecker.Rel.fst"
let t1 = (sn env t1)
in (
# 1616 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1617 "FStar.TypeChecker.Rel.fst"
let fvs1 = (FStar_Syntax_Free.names t1)
in (
# 1618 "FStar.TypeChecker.Rel.fst"
let fvs2 = (FStar_Syntax_Free.names t2)
in (
# 1619 "FStar.TypeChecker.Rel.fst"
let _55_2231 = (occurs_check env wl (uv, k_uv) t2)
in (match (_55_2231) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _144_1171 = (let _144_1170 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _144_1170))
in (giveup_or_defer orig _144_1171))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _144_1172 = (subterms args_lhs)
in (imitate' orig env wl _144_1172))
end else begin
(
# 1626 "FStar.TypeChecker.Rel.fst"
let _55_2232 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1175 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1174 = (names_to_string fvs1)
in (let _144_1173 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _144_1175 _144_1174 _144_1173))))
end else begin
()
end
in (
# 1631 "FStar.TypeChecker.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _55_2236 -> begin
(let _144_1176 = (sn_binders env vars)
in (u_abs k_uv _144_1176 t2))
end)
in (
# 1634 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((TERM (((uv, k_uv), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1639 "FStar.TypeChecker.Rel.fst"
let _55_2239 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1179 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1178 = (names_to_string fvs1)
in (let _144_1177 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _144_1179 _144_1178 _144_1177))))
end else begin
()
end
in (let _144_1180 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _144_1180 (- (1)))))
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
if (let _144_1181 = (FStar_Syntax_Free.names t1)
in (check_head _144_1181 t2)) then begin
(
# 1651 "FStar.TypeChecker.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1652 "FStar.TypeChecker.Rel.fst"
let _55_2243 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1182 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _144_1182 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _144_1183 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _144_1183 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1677 "FStar.TypeChecker.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1680 "FStar.TypeChecker.Rel.fst"
let force_quasi_pattern = (fun xs_opt _55_2255 -> (match (_55_2255) with
| (t, u, k, args) -> begin
(
# 1683 "FStar.TypeChecker.Rel.fst"
let _55_2259 = (FStar_Syntax_Util.arrow_formals k)
in (match (_55_2259) with
| (all_formals, _55_2258) -> begin
(
# 1684 "FStar.TypeChecker.Rel.fst"
let _55_2260 = ()
in (
# 1686 "FStar.TypeChecker.Rel.fst"
let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(
# 1694 "FStar.TypeChecker.Rel.fst"
let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _55_2273 -> (match (_55_2273) with
| (x, imp) -> begin
(let _144_1205 = (FStar_Syntax_Syntax.bv_to_name x)
in (_144_1205, imp))
end))))
in (
# 1695 "FStar.TypeChecker.Rel.fst"
let pattern_vars = (FStar_List.rev pattern_vars)
in (
# 1696 "FStar.TypeChecker.Rel.fst"
let kk = (
# 1697 "FStar.TypeChecker.Rel.fst"
let _55_2279 = (FStar_Syntax_Util.type_u ())
in (match (_55_2279) with
| (t, _55_2278) -> begin
(let _144_1206 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _144_1206))
end))
in (
# 1699 "FStar.TypeChecker.Rel.fst"
let _55_2283 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_55_2283) with
| (t', tm_u1) -> begin
(
# 1700 "FStar.TypeChecker.Rel.fst"
let _55_2290 = (destruct_flex_t t')
in (match (_55_2290) with
| (_55_2285, u1, k1, _55_2289) -> begin
(
# 1701 "FStar.TypeChecker.Rel.fst"
let sol = (let _144_1208 = (let _144_1207 = (u_abs k all_formals t')
in ((u, k), _144_1207))
in TERM (_144_1208))
in (
# 1702 "FStar.TypeChecker.Rel.fst"
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
# 1711 "FStar.TypeChecker.Rel.fst"
let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _55_2309 -> (match (_55_2309) with
| (x, _55_2308) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(
# 1718 "FStar.TypeChecker.Rel.fst"
let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _144_1210 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _144_1210 formals tl))
end)
end)
end)
end
| _55_2313 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _144_1211 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _144_1211 all_formals args))))
end))
end))
in (
# 1730 "FStar.TypeChecker.Rel.fst"
let solve_both_pats = (fun wl _55_2320 _55_2325 r -> (match ((_55_2320, _55_2325)) with
| ((u1, k1, xs, args1), (u2, k2, ys, args2)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _144_1220 = (solve_prob orig None [] wl)
in (solve env _144_1220))
end else begin
(
# 1738 "FStar.TypeChecker.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1739 "FStar.TypeChecker.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1740 "FStar.TypeChecker.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1741 "FStar.TypeChecker.Rel.fst"
let _55_2330 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1225 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _144_1224 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _144_1223 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (let _144_1222 = (FStar_Syntax_Print.term_to_string k1)
in (let _144_1221 = (FStar_Syntax_Print.term_to_string k2)
in (FStar_Util.print5 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n" _144_1225 _144_1224 _144_1223 _144_1222 _144_1221))))))
end else begin
()
end
in (
# 1745 "FStar.TypeChecker.Rel.fst"
let _55_2343 = (
# 1746 "FStar.TypeChecker.Rel.fst"
let _55_2335 = (FStar_Syntax_Util.type_u ())
in (match (_55_2335) with
| (t, _55_2334) -> begin
(
# 1747 "FStar.TypeChecker.Rel.fst"
let _55_2339 = (new_uvar r zs t)
in (match (_55_2339) with
| (k, _55_2338) -> begin
(let _144_1231 = (let _144_1226 = (new_uvar r zs k)
in (FStar_All.pipe_left Prims.fst _144_1226))
in (let _144_1230 = (let _144_1227 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow xs _144_1227))
in (let _144_1229 = (let _144_1228 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow ys _144_1228))
in (_144_1231, _144_1230, _144_1229))))
end))
end))
in (match (_55_2343) with
| (u_zs, knew1, knew2) -> begin
(
# 1751 "FStar.TypeChecker.Rel.fst"
let sub1 = (u_abs knew1 xs u_zs)
in (
# 1752 "FStar.TypeChecker.Rel.fst"
let _55_2347 = (occurs_check env wl (u1, k1) sub1)
in (match (_55_2347) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1755 "FStar.TypeChecker.Rel.fst"
let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1757 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1759 "FStar.TypeChecker.Rel.fst"
let sub2 = (u_abs knew2 ys u_zs)
in (
# 1760 "FStar.TypeChecker.Rel.fst"
let _55_2353 = (occurs_check env wl (u2, k2) sub2)
in (match (_55_2353) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1763 "FStar.TypeChecker.Rel.fst"
let sol2 = TERM (((u2, k2), sub2))
in (
# 1764 "FStar.TypeChecker.Rel.fst"
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
# 1768 "FStar.TypeChecker.Rel.fst"
let solve_one_pat = (fun _55_2361 _55_2366 -> (match ((_55_2361, _55_2366)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1770 "FStar.TypeChecker.Rel.fst"
let _55_2367 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1237 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1236 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _144_1237 _144_1236)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1773 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _55_2372 _55_2376 -> (match ((_55_2372, _55_2376)) with
| ((a, _55_2371), (t2, _55_2375)) -> begin
(let _144_1242 = (let _144_1240 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _144_1240 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _144_1242 (fun _144_1241 -> FStar_TypeChecker_Common.TProb (_144_1241))))
end)) xs args2)
in (
# 1776 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1244 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _144_1244))
in (
# 1777 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1780 "FStar.TypeChecker.Rel.fst"
let t2 = (sn env t2)
in (
# 1781 "FStar.TypeChecker.Rel.fst"
let rhs_vars = (FStar_Syntax_Free.names t2)
in (
# 1782 "FStar.TypeChecker.Rel.fst"
let _55_2386 = (occurs_check env wl (u1, k1) t2)
in (match (_55_2386) with
| (occurs_ok, _55_2385) -> begin
(
# 1783 "FStar.TypeChecker.Rel.fst"
let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(
# 1786 "FStar.TypeChecker.Rel.fst"
let sol = (let _144_1246 = (let _144_1245 = (u_abs k1 xs t2)
in ((u1, k1), _144_1245))
in TERM (_144_1246))
in (
# 1787 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1790 "FStar.TypeChecker.Rel.fst"
let _55_2397 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_55_2397) with
| (sol, (_55_2392, u2, k2, ys)) -> begin
(
# 1791 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1792 "FStar.TypeChecker.Rel.fst"
let _55_2399 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _144_1247 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _144_1247))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2404 -> begin
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
# 1800 "FStar.TypeChecker.Rel.fst"
let _55_2409 = lhs
in (match (_55_2409) with
| (t1, u1, k1, args1) -> begin
(
# 1801 "FStar.TypeChecker.Rel.fst"
let _55_2414 = rhs
in (match (_55_2414) with
| (t2, u2, k2, args2) -> begin
(
# 1802 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1803 "FStar.TypeChecker.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1804 "FStar.TypeChecker.Rel.fst"
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
| _55_2432 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1813 "FStar.TypeChecker.Rel.fst"
let _55_2436 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_55_2436) with
| (sol, _55_2435) -> begin
(
# 1814 "FStar.TypeChecker.Rel.fst"
let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (
# 1815 "FStar.TypeChecker.Rel.fst"
let _55_2438 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _144_1248 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _144_1248))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _55_2443 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1822 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _144_1249 = (solve_prob orig None [] wl)
in (solve env _144_1249))
end else begin
(
# 1824 "FStar.TypeChecker.Rel.fst"
let t1 = problem.FStar_TypeChecker_Common.lhs
in (
# 1825 "FStar.TypeChecker.Rel.fst"
let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _144_1250 = (solve_prob orig None [] wl)
in (solve env _144_1250))
end else begin
(
# 1827 "FStar.TypeChecker.Rel.fst"
let _55_2447 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1251 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _144_1251))
end else begin
()
end
in (
# 1830 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in (
# 1832 "FStar.TypeChecker.Rel.fst"
let match_num_binders = (fun _55_2452 _55_2455 -> (match ((_55_2452, _55_2455)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1834 "FStar.TypeChecker.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1835 "FStar.TypeChecker.Rel.fst"
let _55_2462 = (FStar_Util.first_N n bs)
in (match (_55_2462) with
| (bs, rest) -> begin
(let _144_1281 = (mk_cod rest)
in (bs, _144_1281))
end)))
in (
# 1838 "FStar.TypeChecker.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1839 "FStar.TypeChecker.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _144_1285 = (let _144_1282 = (mk_cod1 [])
in (bs1, _144_1282))
in (let _144_1284 = (let _144_1283 = (mk_cod2 [])
in (bs2, _144_1283))
in (_144_1285, _144_1284)))
end else begin
if (l1 > l2) then begin
(let _144_1288 = (curry l2 bs1 mk_cod1)
in (let _144_1287 = (let _144_1286 = (mk_cod2 [])
in (bs2, _144_1286))
in (_144_1288, _144_1287)))
end else begin
(let _144_1291 = (let _144_1289 = (mk_cod1 [])
in (bs1, _144_1289))
in (let _144_1290 = (curry l1 bs2 mk_cod2)
in (_144_1291, _144_1290)))
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
# 1857 "FStar.TypeChecker.Rel.fst"
let mk_c = (fun c _55_26 -> (match (_55_26) with
| [] -> begin
c
end
| bs -> begin
(let _144_1296 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _144_1296))
end))
in (
# 1861 "FStar.TypeChecker.Rel.fst"
let _55_2505 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_55_2505) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1866 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (
# 1867 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (
# 1868 "FStar.TypeChecker.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _144_1303 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _144_1302 -> FStar_TypeChecker_Common.CProb (_144_1302)) _144_1303)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) -> begin
(
# 1872 "FStar.TypeChecker.Rel.fst"
let mk_t = (fun t l _55_27 -> (match (_55_27) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, l))) None t.FStar_Syntax_Syntax.pos)
end))
in (
# 1875 "FStar.TypeChecker.Rel.fst"
let _55_2535 = (match_num_binders (bs1, (mk_t tbody1 lopt1)) (bs2, (mk_t tbody2 lopt2)))
in (match (_55_2535) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _144_1318 = (let _144_1317 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _144_1316 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _144_1317 problem.FStar_TypeChecker_Common.relation _144_1316 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _144_1315 -> FStar_TypeChecker_Common.TProb (_144_1315)) _144_1318))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2540), FStar_Syntax_Syntax.Tm_refine (_55_2543)) -> begin
(
# 1884 "FStar.TypeChecker.Rel.fst"
let _55_2548 = (as_refinement env wl t1)
in (match (_55_2548) with
| (x1, phi1) -> begin
(
# 1885 "FStar.TypeChecker.Rel.fst"
let _55_2551 = (as_refinement env wl t2)
in (match (_55_2551) with
| (x2, phi2) -> begin
(
# 1886 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1320 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _144_1319 -> FStar_TypeChecker_Common.TProb (_144_1319)) _144_1320))
in (
# 1887 "FStar.TypeChecker.Rel.fst"
let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (
# 1888 "FStar.TypeChecker.Rel.fst"
let subst = (FStar_Syntax_Syntax.DB ((0, x1)))::[]
in (
# 1889 "FStar.TypeChecker.Rel.fst"
let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (
# 1890 "FStar.TypeChecker.Rel.fst"
let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (
# 1891 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x1)
in (
# 1892 "FStar.TypeChecker.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _144_1337 = (imp phi1 phi2)
in (FStar_All.pipe_right _144_1337 (guard_on_element problem x1))))
in (
# 1893 "FStar.TypeChecker.Rel.fst"
let fallback = (fun _55_2563 -> (match (()) with
| () -> begin
(
# 1894 "FStar.TypeChecker.Rel.fst"
let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (
# 1898 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1340 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1340 impl))
in (
# 1899 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 1902 "FStar.TypeChecker.Rel.fst"
let ref_prob = (let _144_1344 = (let _144_1343 = (let _144_1342 = (FStar_Syntax_Syntax.mk_binder x1)
in (_144_1342)::(p_scope orig))
in (mk_problem _144_1343 orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula"))
in (FStar_All.pipe_left (fun _144_1341 -> FStar_TypeChecker_Common.TProb (_144_1341)) _144_1344))
in (match ((solve env (
# 1903 "FStar.TypeChecker.Rel.fst"
let _55_2568 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _55_2568.ctr; defer_ok = false; smt_ok = _55_2568.smt_ok; tcenv = _55_2568.tcenv}))) with
| Failed (_55_2571) -> begin
(fallback ())
end
| Success (_55_2574) -> begin
(
# 1906 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1347 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _144_1346 = (let _144_1345 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _144_1345 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _144_1347 _144_1346)))
in (
# 1907 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1908 "FStar.TypeChecker.Rel.fst"
let wl = (
# 1908 "FStar.TypeChecker.Rel.fst"
let _55_2578 = wl
in {attempting = _55_2578.attempting; wl_deferred = _55_2578.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _55_2578.defer_ok; smt_ok = _55_2578.smt_ok; tcenv = _55_2578.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _144_1349 = (destruct_flex_t t1)
in (let _144_1348 = (destruct_flex_t t2)
in (flex_flex orig _144_1349 _144_1348)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _144_1350 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _144_1350 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1936 "FStar.TypeChecker.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _144_1351 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _144_1351)) then begin
(let _144_1354 = (FStar_All.pipe_left (fun _144_1352 -> FStar_TypeChecker_Common.TProb (_144_1352)) (
# 1938 "FStar.TypeChecker.Rel.fst"
let _55_2723 = problem
in {FStar_TypeChecker_Common.pid = _55_2723.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2723.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2723.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2723.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2723.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2723.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2723.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2723.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2723.FStar_TypeChecker_Common.rank}))
in (let _144_1353 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _144_1354 _144_1353 t2 wl)))
end else begin
(
# 1939 "FStar.TypeChecker.Rel.fst"
let _55_2727 = (base_and_refinement env wl t2)
in (match (_55_2727) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _144_1357 = (FStar_All.pipe_left (fun _144_1355 -> FStar_TypeChecker_Common.TProb (_144_1355)) (
# 1942 "FStar.TypeChecker.Rel.fst"
let _55_2729 = problem
in {FStar_TypeChecker_Common.pid = _55_2729.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2729.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _55_2729.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2729.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2729.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2729.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2729.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2729.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2729.FStar_TypeChecker_Common.rank}))
in (let _144_1356 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _144_1357 _144_1356 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1945 "FStar.TypeChecker.Rel.fst"
let y' = (
# 1945 "FStar.TypeChecker.Rel.fst"
let _55_2735 = y
in {FStar_Syntax_Syntax.ppname = _55_2735.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2735.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (
# 1946 "FStar.TypeChecker.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1947 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1359 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _144_1358 -> FStar_TypeChecker_Common.TProb (_144_1358)) _144_1359))
in (
# 1949 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1360 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1360 impl))
in (
# 1950 "FStar.TypeChecker.Rel.fst"
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
# 1959 "FStar.TypeChecker.Rel.fst"
let _55_2768 = (base_and_refinement env wl t1)
in (match (_55_2768) with
| (t_base, _55_2767) -> begin
(solve_t env (
# 1960 "FStar.TypeChecker.Rel.fst"
let _55_2769 = problem
in {FStar_TypeChecker_Common.pid = _55_2769.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _55_2769.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2769.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2769.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2769.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2769.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2769.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2769.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_55_2772), _55_2775) -> begin
(
# 1963 "FStar.TypeChecker.Rel.fst"
let t2 = (let _144_1361 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _144_1361))
in (solve_t env (
# 1964 "FStar.TypeChecker.Rel.fst"
let _55_2778 = problem
in {FStar_TypeChecker_Common.pid = _55_2778.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2778.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2778.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2778.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2778.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2778.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2778.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2778.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2778.FStar_TypeChecker_Common.rank}) wl))
end
| (_55_2781, FStar_Syntax_Syntax.Tm_refine (_55_2783)) -> begin
(
# 1967 "FStar.TypeChecker.Rel.fst"
let t1 = (let _144_1362 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _144_1362))
in (solve_t env (
# 1968 "FStar.TypeChecker.Rel.fst"
let _55_2787 = problem
in {FStar_TypeChecker_Common.pid = _55_2787.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2787.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2787.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2787.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2787.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2787.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2787.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2787.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2787.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(
# 1972 "FStar.TypeChecker.Rel.fst"
let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_55_2804) -> begin
t
end
| _55_2807 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _144_1367 = (
# 1975 "FStar.TypeChecker.Rel.fst"
let _55_2808 = problem
in (let _144_1366 = (maybe_eta t1)
in (let _144_1365 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _55_2808.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_1366; FStar_TypeChecker_Common.relation = _55_2808.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_1365; FStar_TypeChecker_Common.element = _55_2808.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2808.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2808.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2808.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2808.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2808.FStar_TypeChecker_Common.rank})))
in (solve_t env _144_1367 wl)))
end
| ((FStar_Syntax_Syntax.Tm_match (_), _)) | ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_match (_))) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(
# 1989 "FStar.TypeChecker.Rel.fst"
let head1 = (let _144_1368 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _144_1368 Prims.fst))
in (
# 1990 "FStar.TypeChecker.Rel.fst"
let head2 = (let _144_1369 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _144_1369 Prims.fst))
in if ((((FStar_TypeChecker_Env.is_interpreted env head1) || (FStar_TypeChecker_Env.is_interpreted env head2)) && wl.smt_ok) && (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ)) then begin
(
# 1995 "FStar.TypeChecker.Rel.fst"
let uv1 = (FStar_Syntax_Free.uvars t1)
in (
# 1996 "FStar.TypeChecker.Rel.fst"
let uv2 = (FStar_Syntax_Free.uvars t2)
in if ((FStar_Util.set_is_empty uv1) && (FStar_Util.set_is_empty uv2)) then begin
(
# 1998 "FStar.TypeChecker.Rel.fst"
let guard = if (eq_tm t1 t2) then begin
None
end else begin
(let _144_1371 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _144_1370 -> Some (_144_1370)) _144_1371))
end
in (let _144_1372 = (solve_prob orig guard [] wl)
in (solve env _144_1372)))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end else begin
(rigid_rigid_delta env orig wl head1 head2 t1 t2)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _55_2889, _55_2891), _55_2895) -> begin
(solve_t' env (
# 2006 "FStar.TypeChecker.Rel.fst"
let _55_2897 = problem
in {FStar_TypeChecker_Common.pid = _55_2897.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _55_2897.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_2897.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_2897.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2897.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2897.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2897.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2897.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2897.FStar_TypeChecker_Common.rank}) wl)
end
| (_55_2900, FStar_Syntax_Syntax.Tm_ascribed (t2, _55_2903, _55_2905)) -> begin
(solve_t' env (
# 2009 "FStar.TypeChecker.Rel.fst"
let _55_2909 = problem
in {FStar_TypeChecker_Common.pid = _55_2909.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_2909.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_2909.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _55_2909.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_2909.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_2909.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_2909.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_2909.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_2909.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _144_1375 = (let _144_1374 = (FStar_Syntax_Print.tag_of_term t1)
in (let _144_1373 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _144_1374 _144_1373)))
in (FStar_All.failwith _144_1375))
end
| _55_2948 -> begin
(giveup env "head tag mismatch" orig)
end))))
end))
end)))))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 2021 "FStar.TypeChecker.Rel.fst"
let c1 = problem.FStar_TypeChecker_Common.lhs
in (
# 2022 "FStar.TypeChecker.Rel.fst"
let c2 = problem.FStar_TypeChecker_Common.rhs
in (
# 2023 "FStar.TypeChecker.Rel.fst"
let orig = FStar_TypeChecker_Common.CProb (problem)
in (
# 2024 "FStar.TypeChecker.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 2027 "FStar.TypeChecker.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 2028 "FStar.TypeChecker.Rel.fst"
let _55_2965 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 2030 "FStar.TypeChecker.Rel.fst"
let sub_probs = (FStar_List.map2 (fun _55_2970 _55_2974 -> (match ((_55_2970, _55_2974)) with
| ((a1, _55_2969), (a2, _55_2973)) -> begin
(let _144_1390 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _144_1389 -> FStar_TypeChecker_Common.TProb (_144_1389)) _144_1390))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (
# 2033 "FStar.TypeChecker.Rel.fst"
let guard = (let _144_1392 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _144_1392))
in (
# 2034 "FStar.TypeChecker.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (
# 2038 "FStar.TypeChecker.Rel.fst"
let solve_sub = (fun c1 edge c2 -> (
# 2039 "FStar.TypeChecker.Rel.fst"
let r = (FStar_TypeChecker_Env.get_range env)
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(
# 2041 "FStar.TypeChecker.Rel.fst"
let _55_2997 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _55_2990)::(wlp1, _55_2986)::[] -> begin
(wp1, wlp1)
end
| _55_2994 -> begin
(let _144_1400 = (let _144_1399 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _144_1399))
in (FStar_All.failwith _144_1400))
end)
in (match (_55_2997) with
| (wp, wlp) -> begin
(
# 2044 "FStar.TypeChecker.Rel.fst"
let c1 = (let _144_1406 = (let _144_1405 = (let _144_1401 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _144_1401))
in (let _144_1404 = (let _144_1403 = (let _144_1402 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _144_1402))
in (_144_1403)::[])
in (_144_1405)::_144_1404))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _144_1406; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2051 "FStar.TypeChecker.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _55_28 -> (match (_55_28) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _55_3004 -> begin
false
end))))
in (
# 2052 "FStar.TypeChecker.Rel.fst"
let _55_3025 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _55_3010)::_55_3007, (wp2, _55_3017)::_55_3014) -> begin
(wp1, wp2)
end
| _55_3022 -> begin
(let _144_1410 = (let _144_1409 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _144_1408 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _144_1409 _144_1408)))
in (FStar_All.failwith _144_1410))
end)
in (match (_55_3025) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _144_1411 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _144_1411 wl))
end else begin
(
# 2059 "FStar.TypeChecker.Rel.fst"
let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (
# 2060 "FStar.TypeChecker.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2062 "FStar.TypeChecker.Rel.fst"
let _55_3027 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _144_1421 = (let _144_1420 = (let _144_1419 = (let _144_1413 = (let _144_1412 = (env.FStar_TypeChecker_Env.universe_of env c1.FStar_Syntax_Syntax.result_typ)
in (_144_1412)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1413 env c2_decl c2_decl.FStar_Syntax_Syntax.trivial))
in (let _144_1418 = (let _144_1417 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _144_1416 = (let _144_1415 = (let _144_1414 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1414))
in (_144_1415)::[])
in (_144_1417)::_144_1416))
in (_144_1419, _144_1418)))
in FStar_Syntax_Syntax.Tm_app (_144_1420))
in (FStar_Syntax_Syntax.mk _144_1421 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(
# 2066 "FStar.TypeChecker.Rel.fst"
let wp2_imp_wp1 = (let _144_1437 = (let _144_1436 = (let _144_1435 = (let _144_1423 = (let _144_1422 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_144_1422)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1423 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop))
in (let _144_1434 = (let _144_1433 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _144_1432 = (let _144_1431 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _144_1430 = (let _144_1429 = (let _144_1425 = (let _144_1424 = (FStar_Ident.set_lid_range FStar_Syntax_Const.imp_lid r)
in (FStar_Syntax_Syntax.fvar _144_1424 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1425))
in (let _144_1428 = (let _144_1427 = (let _144_1426 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _144_1426))
in (_144_1427)::[])
in (_144_1429)::_144_1428))
in (_144_1431)::_144_1430))
in (_144_1433)::_144_1432))
in (_144_1435, _144_1434)))
in FStar_Syntax_Syntax.Tm_app (_144_1436))
in (FStar_Syntax_Syntax.mk _144_1437 None r))
in (let _144_1446 = (let _144_1445 = (let _144_1444 = (let _144_1439 = (let _144_1438 = (env.FStar_TypeChecker_Env.universe_of env c2.FStar_Syntax_Syntax.result_typ)
in (_144_1438)::[])
in (FStar_TypeChecker_Env.inst_effect_fun_with _144_1439 env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type))
in (let _144_1443 = (let _144_1442 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _144_1441 = (let _144_1440 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_144_1440)::[])
in (_144_1442)::_144_1441))
in (_144_1444, _144_1443)))
in FStar_Syntax_Syntax.Tm_app (_144_1445))
in (FStar_Syntax_Syntax.mk _144_1446 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (
# 2073 "FStar.TypeChecker.Rel.fst"
let base_prob = (let _144_1448 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _144_1447 -> FStar_TypeChecker_Common.TProb (_144_1447)) _144_1448))
in (
# 2074 "FStar.TypeChecker.Rel.fst"
let wl = (let _144_1452 = (let _144_1451 = (let _144_1450 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _144_1450 g))
in (FStar_All.pipe_left (fun _144_1449 -> Some (_144_1449)) _144_1451))
in (solve_prob orig _144_1452 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _144_1453 = (solve_prob orig None [] wl)
in (solve env _144_1453))
end else begin
(
# 2080 "FStar.TypeChecker.Rel.fst"
let _55_3033 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1455 = (FStar_Syntax_Print.comp_to_string c1)
in (let _144_1454 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _144_1455 (rel_to_string problem.FStar_TypeChecker_Common.relation) _144_1454)))
end else begin
()
end
in (
# 2085 "FStar.TypeChecker.Rel.fst"
let _55_3037 = (let _144_1457 = (FStar_TypeChecker_Normalize.ghost_to_pure env c1)
in (let _144_1456 = (FStar_TypeChecker_Normalize.ghost_to_pure env c2)
in (_144_1457, _144_1456)))
in (match (_55_3037) with
| (c1, c2) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.Total (t2)) when (FStar_Syntax_Util.non_informative t2) -> begin
(let _144_1458 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _144_1458 wl))
end
| (FStar_Syntax_Syntax.GTotal (_55_3044), FStar_Syntax_Syntax.Total (_55_3047)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _144_1459 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _144_1459 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _144_1461 = (
# 2100 "FStar.TypeChecker.Rel.fst"
let _55_3075 = problem
in (let _144_1460 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _55_3075.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _144_1460; FStar_TypeChecker_Common.relation = _55_3075.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _55_3075.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _55_3075.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3075.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3075.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3075.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3075.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3075.FStar_TypeChecker_Common.rank}))
in (solve_c env _144_1461 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _144_1463 = (
# 2104 "FStar.TypeChecker.Rel.fst"
let _55_3091 = problem
in (let _144_1462 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _55_3091.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _55_3091.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _55_3091.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _144_1462; FStar_TypeChecker_Common.element = _55_3091.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _55_3091.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _55_3091.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _55_3091.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _55_3091.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _55_3091.FStar_TypeChecker_Common.rank}))
in (solve_c env _144_1463 wl))
end
| (FStar_Syntax_Syntax.Comp (_55_3094), FStar_Syntax_Syntax.Comp (_55_3097)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _144_1464 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _144_1464 wl))
end else begin
(
# 2110 "FStar.TypeChecker.Rel.fst"
let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (
# 2111 "FStar.TypeChecker.Rel.fst"
let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2115 "FStar.TypeChecker.Rel.fst"
let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (
# 2116 "FStar.TypeChecker.Rel.fst"
let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (
# 2117 "FStar.TypeChecker.Rel.fst"
let _55_3104 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
if (((FStar_Syntax_Util.is_ghost_effect c1.FStar_Syntax_Syntax.effect_name) && (FStar_Syntax_Util.is_pure_effect c2.FStar_Syntax_Syntax.effect_name)) && (let _144_1465 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::[]) env c2.FStar_Syntax_Syntax.result_typ)
in (FStar_Syntax_Util.non_informative _144_1465))) then begin
(
# 2123 "FStar.TypeChecker.Rel.fst"
let edge = {FStar_TypeChecker_Env.msource = c1.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mtarget = c2.FStar_Syntax_Syntax.effect_name; FStar_TypeChecker_Env.mlift = (fun r t -> t)}
in (solve_sub c1 edge c2))
end else begin
(let _144_1470 = (let _144_1469 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _144_1468 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _144_1469 _144_1468)))
in (giveup env _144_1470 orig))
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

# 2135 "FStar.TypeChecker.Rel.fst"
let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _144_1474 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _55_3124 -> (match (_55_3124) with
| (_55_3114, _55_3116, u, _55_3119, _55_3121, _55_3123) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _144_1474 (FStar_String.concat ", "))))

# 2137 "FStar.TypeChecker.Rel.fst"
let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _55_3131 -> begin
(
# 2141 "FStar.TypeChecker.Rel.fst"
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
# 2148 "FStar.TypeChecker.Rel.fst"
let carry = (let _144_1480 = (FStar_List.map (fun _55_3139 -> (match (_55_3139) with
| (_55_3137, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _144_1480 (FStar_String.concat ",\n")))
in (
# 2149 "FStar.TypeChecker.Rel.fst"
let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 2155 "FStar.TypeChecker.Rel.fst"
let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 2157 "FStar.TypeChecker.Rel.fst"
let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 2159 "FStar.TypeChecker.Rel.fst"
let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3148; FStar_TypeChecker_Env.implicits = _55_3146} -> begin
true
end
| _55_3153 -> begin
false
end))

# 2163 "FStar.TypeChecker.Rel.fst"
let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 2165 "FStar.TypeChecker.Rel.fst"
let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2169 "FStar.TypeChecker.Rel.fst"
let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _55_3171 -> begin
(FStar_All.failwith "impossible")
end)
in (let _144_1501 = (
# 2172 "FStar.TypeChecker.Rel.fst"
let _55_3173 = g
in (let _144_1500 = (let _144_1499 = (let _144_1498 = (let _144_1492 = (FStar_Syntax_Syntax.mk_binder x)
in (_144_1492)::[])
in (let _144_1497 = (let _144_1496 = (let _144_1495 = (let _144_1493 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _144_1493 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _144_1495 (fun _144_1494 -> FStar_Util.Inl (_144_1494))))
in Some (_144_1496))
in (FStar_Syntax_Util.abs _144_1498 f _144_1497)))
in (FStar_All.pipe_left (fun _144_1491 -> FStar_TypeChecker_Common.NonTrivial (_144_1491)) _144_1499))
in {FStar_TypeChecker_Env.guard_f = _144_1500; FStar_TypeChecker_Env.deferred = _55_3173.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3173.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3173.FStar_TypeChecker_Env.implicits}))
in Some (_144_1501)))
end))

# 2174 "FStar.TypeChecker.Rel.fst"
let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2176 "FStar.TypeChecker.Rel.fst"
let _55_3180 = g
in (let _144_1512 = (let _144_1511 = (let _144_1510 = (let _144_1509 = (let _144_1508 = (let _144_1507 = (FStar_Syntax_Syntax.as_arg e)
in (_144_1507)::[])
in (f, _144_1508))
in FStar_Syntax_Syntax.Tm_app (_144_1509))
in (FStar_Syntax_Syntax.mk _144_1510 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _144_1506 -> FStar_TypeChecker_Common.NonTrivial (_144_1506)) _144_1511))
in {FStar_TypeChecker_Env.guard_f = _144_1512; FStar_TypeChecker_Env.deferred = _55_3180.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3180.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3180.FStar_TypeChecker_Env.implicits}))
end))

# 2178 "FStar.TypeChecker.Rel.fst"
let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_55_3185) -> begin
(FStar_All.failwith "impossible")
end))

# 2182 "FStar.TypeChecker.Rel.fst"
let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _144_1519 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_144_1519))
end))

# 2187 "FStar.TypeChecker.Rel.fst"
let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc) when (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3203 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 2191 "FStar.TypeChecker.Rel.fst"
let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(
# 2195 "FStar.TypeChecker.Rel.fst"
let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2197 "FStar.TypeChecker.Rel.fst"
let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _144_1542 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _144_1542; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 2201 "FStar.TypeChecker.Rel.fst"
let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2202 "FStar.TypeChecker.Rel.fst"
let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2204 "FStar.TypeChecker.Rel.fst"
let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2206 "FStar.TypeChecker.Rel.fst"
let _55_3230 = g
in (let _144_1557 = (let _144_1556 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _144_1556 (fun _144_1555 -> FStar_TypeChecker_Common.NonTrivial (_144_1555))))
in {FStar_TypeChecker_Env.guard_f = _144_1557; FStar_TypeChecker_Env.deferred = _55_3230.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3230.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3230.FStar_TypeChecker_Env.implicits}))
end))

# 2211 "FStar.TypeChecker.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2212 "FStar.TypeChecker.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _144_1565 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _144_1564 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _144_1565 (rel_to_string rel) _144_1564)))
end else begin
"TOP"
end
in (
# 2217 "FStar.TypeChecker.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2220 "FStar.TypeChecker.Rel.fst"
let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (
# 2221 "FStar.TypeChecker.Rel.fst"
let x = (let _144_1576 = (let _144_1575 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _144_1574 -> Some (_144_1574)) _144_1575))
in (FStar_Syntax_Syntax.new_bv _144_1576 t1))
in (
# 2222 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.push_bv env x)
in (
# 2223 "FStar.TypeChecker.Rel.fst"
let p = (let _144_1580 = (let _144_1578 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _144_1577 -> Some (_144_1577)) _144_1578))
in (let _144_1579 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _144_1580 _144_1579)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 2226 "FStar.TypeChecker.Rel.fst"
let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (
# 2227 "FStar.TypeChecker.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2227 "FStar.TypeChecker.Rel.fst"
let _55_3250 = probs
in {attempting = _55_3250.attempting; wl_deferred = _55_3250.wl_deferred; ctr = _55_3250.ctr; defer_ok = false; smt_ok = _55_3250.smt_ok; tcenv = _55_3250.tcenv})
end else begin
probs
end
in (
# 2228 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2229 "FStar.TypeChecker.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(
# 2232 "FStar.TypeChecker.Rel.fst"
let _55_3257 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2235 "FStar.TypeChecker.Rel.fst"
let _55_3263 = (FStar_Unionfind.rollback tx)
in (
# 2236 "FStar.TypeChecker.Rel.fst"
let _55_3265 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _144_1592 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _144_1592))
end else begin
()
end
in (err (d, s))))
end)))))

# 2240 "FStar.TypeChecker.Rel.fst"
let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(
# 2243 "FStar.TypeChecker.Rel.fst"
let _55_3272 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _144_1597 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _144_1597))
end else begin
()
end
in (
# 2244 "FStar.TypeChecker.Rel.fst"
let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (
# 2245 "FStar.TypeChecker.Rel.fst"
let _55_3275 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _144_1598 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _144_1598))
end else begin
()
end
in (
# 2246 "FStar.TypeChecker.Rel.fst"
let f = (match ((let _144_1599 = (FStar_Syntax_Util.unmeta f)
in _144_1599.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _55_3280 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (
# 2249 "FStar.TypeChecker.Rel.fst"
let _55_3282 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _55_3282.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3282.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3282.FStar_TypeChecker_Env.implicits})))))
end))

# 2251 "FStar.TypeChecker.Rel.fst"
let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _144_1611 = (let _144_1610 = (let _144_1609 = (let _144_1608 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _144_1608 (fun _144_1607 -> FStar_TypeChecker_Common.NonTrivial (_144_1607))))
in {FStar_TypeChecker_Env.guard_f = _144_1609; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _144_1610))
in (FStar_All.pipe_left (fun _144_1606 -> Some (_144_1606)) _144_1611))
end))

# 2256 "FStar.TypeChecker.Rel.fst"
let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2257 "FStar.TypeChecker.Rel.fst"
let _55_3293 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1619 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1618 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _144_1619 _144_1618)))
end else begin
()
end
in (
# 2259 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_1622 = (let _144_1621 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _144_1621))
in (FStar_All.pipe_left (fun _144_1620 -> FStar_TypeChecker_Common.TProb (_144_1620)) _144_1622))
in (
# 2260 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1624 = (solve_and_commit env (singleton env prob) (fun _55_3296 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1624))
in g))))

# 2263 "FStar.TypeChecker.Rel.fst"
let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _144_1634 = (let _144_1633 = (let _144_1632 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _144_1631 = (FStar_TypeChecker_Env.get_range env)
in (_144_1632, _144_1631)))
in FStar_Syntax_Syntax.Error (_144_1633))
in (Prims.raise _144_1634))
end
| Some (g) -> begin
(
# 2267 "FStar.TypeChecker.Rel.fst"
let _55_3305 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1637 = (FStar_Syntax_Print.term_to_string t1)
in (let _144_1636 = (FStar_Syntax_Print.term_to_string t2)
in (let _144_1635 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _144_1637 _144_1636 _144_1635))))
end else begin
()
end
in g)
end))

# 2274 "FStar.TypeChecker.Rel.fst"
let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (
# 2275 "FStar.TypeChecker.Rel.fst"
let _55_3310 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1645 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _144_1644 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _144_1645 _144_1644)))
end else begin
()
end
in (
# 2277 "FStar.TypeChecker.Rel.fst"
let _55_3314 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_55_3314) with
| (prob, x) -> begin
(
# 2278 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1647 = (solve_and_commit env (singleton env prob) (fun _55_3315 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1647))
in (
# 2279 "FStar.TypeChecker.Rel.fst"
let _55_3318 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _144_1651 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _144_1650 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _144_1649 = (let _144_1648 = (FStar_Util.must g)
in (guard_to_string env _144_1648))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _144_1651 _144_1650 _144_1649))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 2287 "FStar.TypeChecker.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _144_1658 = (let _144_1657 = (let _144_1656 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _144_1655 = (FStar_TypeChecker_Env.get_range env)
in (_144_1656, _144_1655)))
in FStar_Syntax_Syntax.Error (_144_1657))
in (Prims.raise _144_1658)))

# 2291 "FStar.TypeChecker.Rel.fst"
let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (
# 2292 "FStar.TypeChecker.Rel.fst"
let _55_3326 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1666 = (FStar_Syntax_Print.comp_to_string c1)
in (let _144_1665 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _144_1666 _144_1665)))
end else begin
()
end
in (
# 2294 "FStar.TypeChecker.Rel.fst"
let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (
# 2295 "FStar.TypeChecker.Rel.fst"
let prob = (let _144_1669 = (let _144_1668 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _144_1668 "sub_comp"))
in (FStar_All.pipe_left (fun _144_1667 -> FStar_TypeChecker_Common.CProb (_144_1667)) _144_1669))
in (let _144_1671 = (solve_and_commit env (singleton env prob) (fun _55_3330 -> None))
in (FStar_All.pipe_left (with_guard env prob) _144_1671))))))

# 2299 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (
# 2300 "FStar.TypeChecker.Rel.fst"
let fail = (fun msg u1 u2 -> (
# 2301 "FStar.TypeChecker.Rel.fst"
let _55_3339 = (FStar_Unionfind.rollback tx)
in (
# 2302 "FStar.TypeChecker.Rel.fst"
let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _144_1689 = (let _144_1688 = (let _144_1687 = (let _144_1685 = (FStar_Syntax_Print.univ_to_string u1)
in (let _144_1684 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _144_1685 _144_1684 msg)))
in (let _144_1686 = (FStar_TypeChecker_Env.get_range env)
in (_144_1687, _144_1686)))
in FStar_Syntax_Syntax.Error (_144_1688))
in (Prims.raise _144_1689)))))
in (
# 2311 "FStar.TypeChecker.Rel.fst"
let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(
# 2314 "FStar.TypeChecker.Rel.fst"
let _55_3355 = hd
in (match (_55_3355) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _144_1696 = (insert uv u1 tl)
in (hd)::_144_1696)
end
end))
end))
in (
# 2319 "FStar.TypeChecker.Rel.fst"
let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(
# 2322 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(
# 2325 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _144_1701 = (insert uv u1 out)
in (group_by _144_1701 rest))
end)
end
| _55_3370 -> begin
None
end))
end))
in (
# 2332 "FStar.TypeChecker.Rel.fst"
let ad_hoc_fallback = (fun _55_3372 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _55_3375 -> begin
(
# 2337 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2337 "FStar.TypeChecker.Rel.fst"
let _55_3376 = (empty_worklist env)
in {attempting = _55_3376.attempting; wl_deferred = _55_3376.wl_deferred; ctr = _55_3376.ctr; defer_ok = true; smt_ok = _55_3376.smt_ok; tcenv = _55_3376.tcenv})
in (FStar_All.pipe_right ineqs (FStar_List.iter (fun _55_3381 -> (match (_55_3381) with
| (u1, u2) -> begin
(
# 2339 "FStar.TypeChecker.Rel.fst"
let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (
# 2340 "FStar.TypeChecker.Rel.fst"
let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _55_3386 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(
# 2346 "FStar.TypeChecker.Rel.fst"
let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _55_3396 -> begin
(u1)::[]
end)
in (
# 2349 "FStar.TypeChecker.Rel.fst"
let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _55_3401 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _55_29 -> (match (_55_29) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(
# 2355 "FStar.TypeChecker.Rel.fst"
let _55_3408 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_3408) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (
# 2357 "FStar.TypeChecker.Rel.fst"
let _55_3412 = (FStar_Syntax_Util.univ_kernel u')
in (match (_55_3412) with
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
| USolved (_55_3414) -> begin
()
end)
end)))
end)))))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(
# 2367 "FStar.TypeChecker.Rel.fst"
let wl = (
# 2367 "FStar.TypeChecker.Rel.fst"
let _55_3418 = (empty_worklist env)
in {attempting = _55_3418.attempting; wl_deferred = _55_3418.wl_deferred; ctr = _55_3418.ctr; defer_ok = false; smt_ok = _55_3418.smt_ok; tcenv = _55_3418.tcenv})
in (
# 2368 "FStar.TypeChecker.Rel.fst"
let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _55_3433 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2380 "FStar.TypeChecker.Rel.fst"
let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (
# 2381 "FStar.TypeChecker.Rel.fst"
let tx = (FStar_Unionfind.new_transaction ())
in (
# 2382 "FStar.TypeChecker.Rel.fst"
let _55_3438 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2385 "FStar.TypeChecker.Rel.fst"
let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (
# 2386 "FStar.TypeChecker.Rel.fst"
let fail = (fun _55_3445 -> (match (_55_3445) with
| (d, s) -> begin
(
# 2387 "FStar.TypeChecker.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2389 "FStar.TypeChecker.Rel.fst"
let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (
# 2390 "FStar.TypeChecker.Rel.fst"
let _55_3448 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1722 = (wl_to_string wl)
in (let _144_1721 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _144_1722 _144_1721)))
end else begin
()
end
in (
# 2392 "FStar.TypeChecker.Rel.fst"
let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(
# 2393 "FStar.TypeChecker.Rel.fst"
let _55_3452 = g
in {FStar_TypeChecker_Env.guard_f = _55_3452.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _55_3452.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3452.FStar_TypeChecker_Env.implicits})
end
| _55_3455 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (
# 2395 "FStar.TypeChecker.Rel.fst"
let _55_3457 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (
# 2396 "FStar.TypeChecker.Rel.fst"
let _55_3459 = g
in {FStar_TypeChecker_Env.guard_f = _55_3459.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3459.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _55_3459.FStar_TypeChecker_Env.implicits})))))))

# 2398 "FStar.TypeChecker.Rel.fst"
let discharge_guard' : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun use_env_range_msg env g -> (
# 2399 "FStar.TypeChecker.Rel.fst"
let g = (solve_deferred_constraints env g)
in (
# 2400 "FStar.TypeChecker.Rel.fst"
let _55_3474 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2404 "FStar.TypeChecker.Rel.fst"
let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(
# 2408 "FStar.TypeChecker.Rel.fst"
let _55_3472 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _144_1739 = (FStar_TypeChecker_Env.get_range env)
in (let _144_1738 = (let _144_1737 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _144_1737))
in (FStar_TypeChecker_Errors.diag _144_1739 _144_1738)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve use_env_range_msg env vc))
end))
end)
end
in (
# 2413 "FStar.TypeChecker.Rel.fst"
let _55_3476 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3476.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3476.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3476.FStar_TypeChecker_Env.implicits}))))

# 2415 "FStar.TypeChecker.Rel.fst"
let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (discharge_guard' None env g))

# 2417 "FStar.TypeChecker.Rel.fst"
let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (
# 2418 "FStar.TypeChecker.Rel.fst"
let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _55_3485 -> begin
false
end))
in (
# 2421 "FStar.TypeChecker.Rel.fst"
let rec until_fixpoint = (fun _55_3489 implicits -> (match (_55_3489) with
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
# 2425 "FStar.TypeChecker.Rel.fst"
let _55_3502 = hd
in (match (_55_3502) with
| (_55_3496, env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(
# 2428 "FStar.TypeChecker.Rel.fst"
let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (
# 2429 "FStar.TypeChecker.Rel.fst"
let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (
# 2430 "FStar.TypeChecker.Rel.fst"
let _55_3505 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _144_1755 = (FStar_Syntax_Print.uvar_to_string u)
in (let _144_1754 = (FStar_Syntax_Print.term_to_string tm)
in (let _144_1753 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _144_1755 _144_1754 _144_1753))))
end else begin
()
end
in (
# 2433 "FStar.TypeChecker.Rel.fst"
let _55_3514 = (env.FStar_TypeChecker_Env.type_of (
# 2433 "FStar.TypeChecker.Rel.fst"
let _55_3507 = env
in {FStar_TypeChecker_Env.solver = _55_3507.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_3507.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_3507.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_3507.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_3507.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_3507.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _55_3507.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _55_3507.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_3507.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_3507.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_3507.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_3507.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_3507.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_3507.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_3507.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_3507.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_3507.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_3507.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.type_of = _55_3507.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_3507.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_55_3514) with
| (_55_3510, _55_3512, g) -> begin
(
# 2434 "FStar.TypeChecker.Rel.fst"
let g = if env.FStar_TypeChecker_Env.is_pattern then begin
(
# 2435 "FStar.TypeChecker.Rel.fst"
let _55_3515 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _55_3515.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3515.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _55_3515.FStar_TypeChecker_Env.implicits})
end else begin
g
end
in (
# 2437 "FStar.TypeChecker.Rel.fst"
let g' = (discharge_guard' (Some ((fun _55_3518 -> (match (()) with
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
# 2439 "FStar.TypeChecker.Rel.fst"
let _55_3520 = g
in (let _144_1759 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _55_3520.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3520.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _55_3520.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _144_1759})))))

# 2441 "FStar.TypeChecker.Rel.fst"
let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (
# 2442 "FStar.TypeChecker.Rel.fst"
let g = (let _144_1764 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _144_1764 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _144_1765 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _144_1765))
end
| (reason, _55_3530, _55_3532, e, t, r)::_55_3527 -> begin
(let _144_1770 = (let _144_1769 = (let _144_1768 = (let _144_1767 = (FStar_Syntax_Print.term_to_string t)
in (let _144_1766 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format3 "Failed to resolve implicit argument of type \'%s\' introduced in %s because %s" _144_1767 _144_1766 reason)))
in (_144_1768, r))
in FStar_Syntax_Syntax.Error (_144_1769))
in (Prims.raise _144_1770))
end)))

# 2453 "FStar.TypeChecker.Rel.fst"
let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (
# 2455 "FStar.TypeChecker.Rel.fst"
let _55_3540 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _55_3540.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _55_3540.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _55_3540.FStar_TypeChecker_Env.implicits}))





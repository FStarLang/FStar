
open Prims
# 41 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Syntax_Syntax.is_null_binder x) Prims.op_Negation))))
in (let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _90_37 -> begin
(let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (let k' = (let _192_8 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _192_8))
in (let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _192_9 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_192_9, uv)))))
end))))

# 58 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)

# 59 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___TERM____0 : uvi  ->  ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_90_43) -> begin
_90_43
end))

# 60 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_90_46) -> begin
_90_46
end))

# 63 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

# 63 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

# 73 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)

# 74 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

# 75 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___Success____0 : solution  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| Success (_90_56) -> begin
_90_56
end))

# 75 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_90_59) -> begin
_90_59
end))

# 77 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

# 78 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 79 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

# 83 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

# 84 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

# 93 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _90_1 -> (match (_90_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))

# 98 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

# 100 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _90_2 -> (match (_90_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _192_108 = (let _192_107 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _192_106 = (let _192_105 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _192_104 = (let _192_103 = (let _192_102 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _192_101 = (let _192_100 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _192_99 = (let _192_98 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _192_97 = (let _192_96 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_192_96)::[])
in (_192_98)::_192_97))
in (_192_100)::_192_99))
in (_192_102)::_192_101))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_192_103)
in (_192_105)::_192_104))
in (_192_107)::_192_106))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _192_108))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _192_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _192_109 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _192_110 (rel_to_string p.FStar_TypeChecker_Common.relation) _192_109)))
end))

# 116 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _90_3 -> (match (_90_3) with
| UNIV (u, t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _192_115 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _192_115 FStar_Util.string_of_int))
end
in (let _192_116 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _192_116)))
end
| TERM ((u, _90_83), t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _192_117 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _192_117 FStar_Util.string_of_int))
end
in (let _192_118 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _192_118)))
end))

# 124 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _192_123 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _192_123 (FStar_String.concat ", "))))

# 125 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _192_133 = (let _192_132 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _192_132 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _192_133 (FStar_String.concat ", "))))

# 126 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let args_to_string = (fun args -> (let _192_136 = (FStar_All.pipe_right args (FStar_List.map (fun _90_96 -> (match (_90_96) with
| (x, _90_95) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _192_136 (FStar_String.concat " "))))

# 135 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

# 143 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (let _90_100 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _90_100.wl_deferred; ctr = _90_100.ctr; defer_ok = _90_100.defer_ok; smt_ok = _90_100.smt_ok; tcenv = _90_100.tcenv}))

# 144 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let wl_of_guard = (fun env g -> (let _90_104 = (empty_worklist env)
in (let _192_145 = (FStar_List.map Prims.snd g)
in {attempting = _192_145; wl_deferred = _90_104.wl_deferred; ctr = _90_104.ctr; defer_ok = false; smt_ok = _90_104.smt_ok; tcenv = _90_104.tcenv})))

# 145 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (let _90_109 = wl
in {attempting = _90_109.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _90_109.ctr; defer_ok = _90_109.defer_ok; smt_ok = _90_109.smt_ok; tcenv = _90_109.tcenv}))

# 146 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (let _90_113 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _90_113.wl_deferred; ctr = _90_113.ctr; defer_ok = _90_113.defer_ok; smt_ok = _90_113.smt_ok; tcenv = _90_113.tcenv}))

# 148 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (let _90_118 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_162 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _192_162))
end else begin
()
end
in Failed ((prob, reason))))

# 159 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _90_4 -> (match (_90_4) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))

# 163 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let invert = (fun p -> (let _90_125 = p
in {FStar_TypeChecker_Common.pid = _90_125.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _90_125.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_125.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_125.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_125.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_125.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_125.FStar_TypeChecker_Common.rank}))

# 164 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

# 165 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _90_5 -> (match (_90_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _192_169 -> FStar_TypeChecker_Common.TProb (_192_169)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _192_170 -> FStar_TypeChecker_Common.CProb (_192_170)))
end))

# 168 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _90_6 -> (match (_90_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

# 172 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _90_7 -> (match (_90_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

# 175 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _90_8 -> (match (_90_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

# 178 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _90_9 -> (match (_90_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

# 181 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _90_10 -> (match (_90_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

# 184 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _90_11 -> (match (_90_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

# 187 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _90_12 -> (match (_90_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

# 190 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _90_13 -> (match (_90_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _192_189 -> FStar_TypeChecker_Common.TProb (_192_189)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _192_190 -> FStar_TypeChecker_Common.CProb (_192_190)) (invert p))
end))

# 193 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 194 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let next_pid : Prims.unit  ->  Prims.int = (let ctr = (FStar_ST.alloc 0)
in (fun _90_175 -> (match (()) with
| () -> begin
(let _90_176 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

# 198 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _192_203 = (next_pid ())
in (let _192_202 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _192_203; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _192_202; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

# 210 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let new_problem = (fun env lhs rel rhs elt loc reason -> (let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _192_212 = (next_pid ())
in (let _192_211 = (new_uvar (FStar_TypeChecker_Env.get_range env) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _192_212; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _192_211; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

# 224 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _192_219 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _192_219; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

# 236 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

# 240 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _192_231 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _192_230 = (prob_to_string env d)
in (let _192_229 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _192_231 _192_230 _192_229 s)))))

# 254 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _90_14 -> (match (_90_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _90_217 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _90_220), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

# 262 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _90_15 -> (match (_90_15) with
| UNIV (_90_229) -> begin
None
end
| TERM ((u, _90_233), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

# 266 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _90_16 -> (match (_90_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _90_246 -> begin
None
end))))

# 278 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env t -> (let _192_250 = (let _192_249 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _192_249))
in (FStar_Syntax_Subst.compress _192_250)))

# 279 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env t -> (let _192_255 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _192_255)))

# 280 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let norm_arg = (fun env t -> (let _192_258 = (sn env (Prims.fst t))
in (_192_258, (Prims.snd t))))

# 281 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _90_257 -> (match (_90_257) with
| (x, imp) -> begin
(let _192_265 = (let _90_258 = x
in (let _192_264 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _90_258.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_258.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _192_264}))
in (_192_265, imp))
end)))))

# 288 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _192_272 = (aux u)
in FStar_Syntax_Syntax.U_succ (_192_272))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _192_273 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_192_273))
end
| _90_270 -> begin
u
end)))
in (let _192_274 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _192_274))))

# 301 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let normalize_refinement = (fun steps env wl t0 -> (let _192_279 = (whnf env t0)
in (FStar_TypeChecker_Normalize.normalize_refinement steps env _192_279)))

# 303 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let base_and_refinement = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _90_290; FStar_Syntax_Syntax.pos = _90_288; FStar_Syntax_Syntax.vars = _90_286} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _192_289 = (let _192_288 = (FStar_Syntax_Print.term_to_string tt)
in (let _192_287 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _192_288 _192_287)))
in (FStar_All.failwith _192_289))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _90_308 = (let _192_290 = (normalize_refinement [] env wl t1)
in (aux true _192_290))
in (match (_90_308) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _90_311 -> begin
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
(let _192_293 = (let _192_292 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_291 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _192_292 _192_291)))
in (FStar_All.failwith _192_293))
end))
in (let _192_294 = (whnf env t1)
in (aux false _192_294))))

# 343 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _192_299 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _192_299 Prims.fst)))

# 345 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax) = (fun t -> ((FStar_Syntax_Syntax.null_bv t), FStar_Syntax_Util.t_true))

# 347 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let as_refinement = (fun env wl t -> (let _90_357 = (base_and_refinement env wl t)
in (match (_90_357) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

# 353 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let force_refinement = (fun _90_365 -> (match (_90_365) with
| (t_base, refopt) -> begin
(let _90_373 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_90_373) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

# 367 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _90_17 -> (match (_90_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _192_314 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _192_313 = (let _192_310 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _192_310))
in (let _192_312 = (let _192_311 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _192_311))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _192_314 _192_313 (rel_to_string p.FStar_TypeChecker_Common.relation) _192_312))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _192_317 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _192_316 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _192_315 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _192_317 _192_316 (rel_to_string p.FStar_TypeChecker_Common.relation) _192_315))))
end))

# 382 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _192_323 = (let _192_322 = (let _192_321 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _90_386 -> (match (_90_386) with
| (_90_382, _90_384, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _192_321))
in (FStar_List.map (wl_prob_to_string wl) _192_322))
in (FStar_All.pipe_right _192_323 (FStar_String.concat "\n\t"))))

# 392 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let u_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun x y -> (FStar_Syntax_Util.abs x y None))

# 394 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _90_401 = (p_guard prob)
in (match (_90_401) with
| (_90_399, uv) -> begin
(let _90_414 = (match ((let _192_338 = (FStar_Syntax_Subst.compress uv)
in _192_338.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(let bs = (p_scope prob)
in (let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Syntax_Syntax.is_null_binder x) Prims.op_Negation))))
in (let phi = (u_abs bs phi)
in (let _90_410 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _192_342 = (FStar_Util.string_of_int (p_pid prob))
in (let _192_341 = (FStar_Syntax_Print.term_to_string uv)
in (let _192_340 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _192_342 _192_341 _192_340))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _90_413 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (let _90_416 = (commit uvis)
in (let _90_418 = wl
in {attempting = _90_418.attempting; wl_deferred = _90_418.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _90_418.defer_ok; smt_ok = _90_418.smt_ok; tcenv = _90_418.tcenv})))
end))))

# 414 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (let _90_423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_351 = (FStar_Util.string_of_int pid)
in (let _192_350 = (let _192_349 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _192_349 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _192_351 _192_350)))
end else begin
()
end
in (let _90_425 = (commit sol)
in (let _90_427 = wl
in {attempting = _90_427.attempting; wl_deferred = _90_427.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _90_427.defer_ok; smt_ok = _90_427.smt_ok; tcenv = _90_427.tcenv}))))

# 420 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let solve_prob : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (let conj_guard = (fun t g -> (match ((t, g)) with
| (_90_437, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _192_364 = (FStar_Syntax_Util.mk_conj t f)
in Some (_192_364))
end))
in (let _90_449 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_367 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _192_366 = (let _192_365 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _192_365 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _192_367 _192_366)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

# 437 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec occurs = (fun wl uk t -> (let _192_377 = (let _192_375 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _192_375 FStar_Util.set_elements))
in (FStar_All.pipe_right _192_377 (FStar_Util.for_some (fun _90_458 -> (match (_90_458) with
| (uv, _90_457) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

# 443 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let occurs_check = (fun env wl uk t -> (let occurs_ok = (not ((occurs wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _192_384 = (let _192_383 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _192_382 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _192_383 _192_382)))
in Some (_192_384))
end
in (occurs_ok, msg))))

# 452 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let occurs_and_freevars_check = (fun env wl uk fvs t -> (let fvs_t = (FStar_Syntax_Free.names t)
in (let _90_473 = (occurs_check env wl uk t)
in (match (_90_473) with
| (occurs_ok, msg) -> begin
(let _192_438 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _192_438, (msg, fvs, fvs_t)))
end))))

# 457 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let intersect_vars = (fun v1 v2 -> (let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (let v1_set = (as_set v1)
in (let _90_491 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _90_483 _90_486 -> (match ((_90_483, _90_486)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _192_447 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _192_447)) then begin
(isect, isect_set)
end else begin
(let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _192_452 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _192_452))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_90_491) with
| (isect, _90_490) -> begin
(FStar_List.rev isect)
end)))))

# 474 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _90_497 _90_501 -> (match ((_90_497, _90_501)) with
| ((a, _90_496), (b, _90_500)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

# 478 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _90_511 -> (match (_90_511) with
| (b, _90_510) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _90_513 -> begin
None
end)))

# 488 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _90_522 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_471 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _192_471))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 496 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _90_536; FStar_Syntax_Syntax.pos = _90_534; FStar_Syntax_Syntax.vars = _90_532}, args) -> begin
(t, uv, k, args)
end
| _90_546 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 501 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let destruct_flex_pattern = (fun env t -> (let _90_553 = (destruct_flex_t t)
in (match (_90_553) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _90_557 -> begin
((t, uv, k, args), None)
end)
end)))

# 576 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type match_result =
| MisMatch
| HeadMatch
| FullMatch

# 577 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 578 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 579 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 581 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let head_match : match_result  ->  match_result = (fun _90_18 -> (match (_90_18) with
| MisMatch -> begin
MisMatch
end
| _90_561 -> begin
HeadMatch
end))

# 585 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec head_matches : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun t1 t2 -> (match ((let _192_487 = (let _192_484 = (FStar_Syntax_Util.unmeta t1)
in _192_484.FStar_Syntax_Syntax.n)
in (let _192_486 = (let _192_485 = (FStar_Syntax_Util.unmeta t2)
in _192_485.FStar_Syntax_Syntax.n)
in (_192_487, _192_486)))) with
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _90_576), FStar_Syntax_Syntax.Tm_uinst (g, _90_581)) -> begin
(let _192_488 = (head_matches f g)
in (FStar_All.pipe_right _192_488 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _90_592), FStar_Syntax_Syntax.Tm_uvar (uv', _90_597)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _90_603), FStar_Syntax_Syntax.Tm_refine (y, _90_608)) -> begin
(let _192_489 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _192_489 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _90_614), _90_618) -> begin
(let _192_490 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _192_490 head_match))
end
| (_90_621, FStar_Syntax_Syntax.Tm_refine (x, _90_624)) -> begin
(let _192_491 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _192_491 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _90_644), FStar_Syntax_Syntax.Tm_app (head', _90_649)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _90_655), _90_659) -> begin
(head_matches head t2)
end
| (_90_662, FStar_Syntax_Syntax.Tm_app (head, _90_665)) -> begin
(head_matches t1 head)
end
| _90_670 -> begin
MisMatch
end))

# 611 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let head_matches_delta = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun _90_681 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 2) then begin
(fail ())
end else begin
if (d = 1) then begin
(let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t1)
in (let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t2)
in (aux 2 t1' t2')))
end else begin
(let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t1)
in (let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t2)
in (aux (d + 1) t1 t2)))
end
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux 0 t1 t2)))))

# 628 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

# 629 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

# 630 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

# 629 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_90_694) -> begin
_90_694
end))

# 630 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_90_697) -> begin
_90_697
end))

# 631 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type tcs =
tc Prims.list

# 633 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec decompose = (fun env t -> (let t = (FStar_Syntax_Util.unmeta t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_90_712, imp), T (t)) -> begin
(t, imp)
end
| _90_719 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _90_724 -> (match (_90_724) with
| (t, _90_723) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let fail = (fun _90_731 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let _90_734 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_90_734) with
| (bs, c) -> begin
(let rebuild = (fun tcs -> (let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((let _90_751 = x
in {FStar_Syntax_Syntax.ppname = _90_751.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_751.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _90_759 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (let rec decompose = (fun out _90_19 -> (match (_90_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _192_585 = (decompose [] bs)
in (rebuild, matches, _192_585))))
end)))
end
| _90_769 -> begin
(let rebuild = (fun _90_20 -> (match (_90_20) with
| [] -> begin
t
end
| _90_773 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 677 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _90_21 -> (match (_90_21) with
| T (t) -> begin
t
end
| _90_780 -> begin
(FStar_All.failwith "Impossible")
end))

# 681 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let arg_of_tc : tc  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier Prims.option) = (fun _90_22 -> (match (_90_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _90_785 -> begin
(FStar_All.failwith "Impossible")
end))

# 685 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_90_798, variance, T (ti)) -> begin
(let k = (let _90_806 = (FStar_Syntax_Util.type_u ())
in (match (_90_806) with
| (t, _90_805) -> begin
(let _192_607 = (new_uvar r scope t)
in (Prims.fst _192_607))
end))
in (let _90_810 = (new_uvar r scope k)
in (match (_90_810) with
| (gi_xs, gi) -> begin
(let gi_ps = (match (args) with
| [] -> begin
gi
end
| _90_813 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _192_610 = (let _192_609 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _192_608 -> FStar_TypeChecker_Common.TProb (_192_608)) _192_609))
in (T (gi_xs), _192_610)))
end)))
end
| (_90_816, _90_818, C (_90_820)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(let _90_898 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _90_838; FStar_Syntax_Syntax.pos = _90_836; FStar_Syntax_Syntax.vars = _90_834})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _192_619 = (let _192_618 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _192_617 -> C (_192_617)) _192_618))
in (_192_619, (prob)::[]))
end
| _90_849 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _90_857; FStar_Syntax_Syntax.pos = _90_855; FStar_Syntax_Syntax.vars = _90_853})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _192_622 = (let _192_621 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _192_620 -> C (_192_620)) _192_621))
in (_192_622, (prob)::[]))
end
| _90_868 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_90_870, _90_872, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _90_878; FStar_Syntax_Syntax.pos = _90_876; FStar_Syntax_Syntax.vars = _90_874})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (let _90_889 = (let _192_624 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _192_624 FStar_List.unzip))
in (match (_90_889) with
| (tcs, sub_probs) -> begin
(let gi_xs = (let _192_629 = (let _192_628 = (let _192_625 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _192_625 un_T))
in (let _192_627 = (let _192_626 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _192_626 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _192_628; FStar_Syntax_Syntax.effect_args = _192_627; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _192_629))
in (C (gi_xs), sub_probs))
end))))
end
| _90_892 -> begin
(let _90_895 = (sub_prob scope args q)
in (match (_90_895) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_90_898) with
| (tc, probs) -> begin
(let _90_911 = (match (q) with
| (Some (b), _90_902, _90_904) -> begin
(let _192_631 = (let _192_630 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_192_630)::args)
in (Some (b), (b)::scope, _192_631))
end
| _90_907 -> begin
(None, scope, args)
end)
in (match (_90_911) with
| (bopt, scope, args) -> begin
(let _90_915 = (aux scope args qs)
in (match (_90_915) with
| (sub_probs, tcs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _192_634 = (let _192_633 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_192_633)
in (FStar_Syntax_Util.mk_conj_l _192_634))
end
| Some (b) -> begin
(let _192_638 = (let _192_637 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _192_636 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_192_637)::_192_636))
in (FStar_Syntax_Util.mk_conj_l _192_638))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 760 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (let t1 = (FStar_Syntax_Subst.compress t1)
in (let t2 = (FStar_Syntax_Subst.compress t2)
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _90_943), FStar_Syntax_Syntax.Tm_uvar (u2, _90_948)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _90_962 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _90_968 _90_972 -> (match ((_90_968, _90_972)) with
| ((a1, _90_967), (a2, _90_971)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

# 779 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

# 780 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

# 782 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rigid_rigid : Prims.int = 0

# 783 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let flex_rigid_eq : Prims.int = 1

# 784 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let flex_refine_inner : Prims.int = 2

# 785 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let flex_refine : Prims.int = 3

# 786 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let flex_rigid : Prims.int = 4

# 787 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rigid_flex : Prims.int = 5

# 788 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let refine_flex : Prims.int = 6

# 789 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let flex_flex : Prims.int = 7

# 790 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let compress_tprob = (fun wl p -> (let _90_975 = p
in (let _192_660 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _192_659 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _90_975.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _192_660; FStar_TypeChecker_Common.relation = _90_975.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _192_659; FStar_TypeChecker_Common.element = _90_975.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_975.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_975.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_975.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_975.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_975.FStar_TypeChecker_Common.rank}))))

# 792 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _192_666 = (compress_tprob wl p)
in (FStar_All.pipe_right _192_666 (fun _192_665 -> FStar_TypeChecker_Common.TProb (_192_665))))
end
| FStar_TypeChecker_Common.CProb (_90_982) -> begin
p
end))

# 797 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (let prob = (let _192_671 = (compress_prob wl pr)
in (FStar_All.pipe_right _192_671 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _90_992 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_90_992) with
| (lh, _90_991) -> begin
(let _90_996 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_90_996) with
| (rh, _90_995) -> begin
(let _90_1052 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_90_998), FStar_Syntax_Syntax.Tm_uvar (_90_1001)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_90_1017), _90_1020) -> begin
(let _90_1024 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_90_1024) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _90_1027 -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _192_673 = (let _90_1029 = tp
in (let _192_672 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _90_1029.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_1029.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_1029.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _192_672; FStar_TypeChecker_Common.element = _90_1029.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_1029.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_1029.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_1029.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_1029.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_1029.FStar_TypeChecker_Common.rank}))
in (rank, _192_673)))
end)
end))
end
| (_90_1032, FStar_Syntax_Syntax.Tm_uvar (_90_1034)) -> begin
(let _90_1039 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_90_1039) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _90_1042 -> begin
(let _192_675 = (let _90_1043 = tp
in (let _192_674 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _90_1043.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _192_674; FStar_TypeChecker_Common.relation = _90_1043.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_1043.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_1043.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_1043.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_1043.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_1043.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_1043.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_1043.FStar_TypeChecker_Common.rank}))
in (refine_flex, _192_675))
end)
end))
end
| (_90_1046, _90_1048) -> begin
(rigid_rigid, tp)
end)
in (match (_90_1052) with
| (rank, tp) -> begin
(let _192_677 = (FStar_All.pipe_right (let _90_1053 = tp
in {FStar_TypeChecker_Common.pid = _90_1053.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_1053.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_1053.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_1053.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_1053.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_1053.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_1053.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_1053.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_1053.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _192_676 -> FStar_TypeChecker_Common.TProb (_192_676)))
in (rank, _192_677))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _192_679 = (FStar_All.pipe_right (let _90_1057 = cp
in {FStar_TypeChecker_Common.pid = _90_1057.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_1057.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_1057.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_1057.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_1057.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_1057.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_1057.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_1057.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_1057.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _192_678 -> FStar_TypeChecker_Common.CProb (_192_678)))
in (rigid_rigid, _192_679))
end)))

# 836 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (let rec aux = (fun _90_1064 probs -> (match (_90_1064) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _90_1072 = (rank wl hd)
in (match (_90_1072) with
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

# 856 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 858 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

# 859 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

# 860 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

# 861 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

# 859 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_90_1082) -> begin
_90_1082
end))

# 860 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_90_1085) -> begin
_90_1085
end))

# 861 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_90_1088) -> begin
_90_1088
end))

# 863 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (let _90_1104 = (FStar_Syntax_Util.univ_kernel u)
in (match (_90_1104) with
| (k, _90_1103) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _90_1108 -> begin
false
end)
end)))))
end
| _90_1110 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_90_1116), FStar_Syntax_Syntax.U_max (_90_1119)) -> begin
(let _192_751 = (let _192_750 = (FStar_Syntax_Print.univ_to_string u1)
in (let _192_749 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _192_750 _192_749)))
in UFailed (_192_751))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(let rec aux = (fun wl us -> (match (us) with
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
| _90_1139 -> begin
(let _192_758 = (let _192_757 = (FStar_Syntax_Print.univ_to_string u1)
in (let _192_756 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _192_757 _192_756 msg)))
in UFailed (_192_758))
end))
in (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _192_761 = (let _192_760 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _192_759 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _192_760 _192_759)))
in (try_umax_components u1 u2 _192_761))
end else begin
(let _192_762 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_192_762))
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
(let u1 = (norm_univ wl u1)
in (let u2 = (norm_univ wl u2)
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

# 946 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (let _90_1234 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_805 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _192_805))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _90_1241 = probs
in {attempting = tl; wl_deferred = _90_1241.wl_deferred; ctr = _90_1241.ctr; defer_ok = _90_1241.defer_ok; smt_ok = _90_1241.smt_ok; tcenv = _90_1241.tcenv})
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
| (None, _90_1253, _90_1255) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _90_1259 -> begin
(let _90_1268 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _90_1265 -> (match (_90_1265) with
| (c, _90_1262, _90_1264) -> begin
(c < probs.ctr)
end))))
in (match (_90_1268) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _192_808 = (FStar_List.map (fun _90_1274 -> (match (_90_1274) with
| (_90_1271, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_192_808))
end
| _90_1276 -> begin
(let _192_811 = (let _90_1277 = probs
in (let _192_810 = (FStar_All.pipe_right attempt (FStar_List.map (fun _90_1284 -> (match (_90_1284) with
| (_90_1280, _90_1282, y) -> begin
y
end))))
in {attempting = _192_810; wl_deferred = rest; ctr = _90_1277.ctr; defer_ok = _90_1277.defer_ok; smt_ok = _90_1277.smt_ok; tcenv = _90_1277.tcenv}))
in (solve env _192_811))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _192_817 = (solve_prob orig None [] wl)
in (solve env _192_817))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
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
| _90_1319 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _192_832 = (let _192_829 = (whnf env t1)
in _192_829.FStar_Syntax_Syntax.n)
in (let _192_831 = (let _192_830 = (whnf env t2)
in _192_830.FStar_Syntax_Syntax.n)
in (_192_832, _192_831)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _90_1325; FStar_Syntax_Syntax.pos = _90_1323; FStar_Syntax_Syntax.vars = _90_1321}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _90_1337; FStar_Syntax_Syntax.pos = _90_1335; FStar_Syntax_Syntax.vars = _90_1333}, us2)) -> begin
(let b = (FStar_Syntax_Syntax.fv_eq f g)
in (let _90_1346 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _90_1361 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(let _90_1366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_837 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _192_837 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (let _90_1371 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_841 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _192_841))
end else begin
()
end
in (let _90_1375 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_90_1375) with
| (u, args) -> begin
(let _90_1381 = (0, 1, 2, 3, 4)
in (match (_90_1381) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun t1 t2 -> (let _90_1390 = (FStar_Syntax_Util.head_and_args t1)
in (match (_90_1390) with
| (h1, args1) -> begin
(let _90_1394 = (FStar_Syntax_Util.head_and_args t2)
in (match (_90_1394) with
| (h2, _90_1393) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _192_853 = (let _192_852 = (let _192_851 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _192_850 -> FStar_TypeChecker_Common.TProb (_192_850)) _192_851))
in (_192_852)::[])
in Some (_192_853))
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
| _90_1406 -> begin
None
end)
end))
end)))
in (let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(let x = (FStar_Syntax_Syntax.freshen_bv x)
in (let subst = (let _192_860 = (let _192_859 = (let _192_858 = (FStar_Syntax_Syntax.bv_to_name x)
in (0, _192_858))
in FStar_Syntax_Syntax.DB (_192_859))
in (_192_860)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _192_863 = (let _192_862 = (let _192_861 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _192_861))
in (_192_862, m))
in Some (_192_863))))))
end))
end
| (_90_1428, FStar_Syntax_Syntax.Tm_refine (y, _90_1431)) -> begin
(let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _90_1441), _90_1445) -> begin
(let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _90_1452 -> begin
(let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _90_1460) -> begin
(let _90_1485 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _90_23 -> (match (_90_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _90_1471 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_90_1471) with
| (u', _90_1470) -> begin
(match ((let _192_865 = (whnf env u')
in _192_865.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _90_1474) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _90_1478 -> begin
false
end)
end))
end
| _90_1480 -> begin
false
end)
end
| _90_1482 -> begin
false
end))))
in (match (_90_1485) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _90_1489 tps -> (match (_90_1489) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _192_870 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _192_870))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _90_1502 -> begin
None
end)
end))
in (match ((let _192_872 = (let _192_871 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_192_871, []))
in (make_upper_bound _192_872 upper_bounds))) with
| None -> begin
(let _90_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (let _90_1514 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let wl' = (let _90_1511 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _90_1511.wl_deferred; ctr = _90_1511.ctr; defer_ok = _90_1511.defer_ok; smt_ok = _90_1511.smt_ok; tcenv = _90_1511.tcenv})
in (let _192_873 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _192_873)))
end else begin
()
end
in (match ((solve_t env eq_prob (let _90_1516 = wl
in {attempting = sub_probs; wl_deferred = _90_1516.wl_deferred; ctr = _90_1516.ctr; defer_ok = _90_1516.defer_ok; smt_ok = _90_1516.smt_ok; tcenv = _90_1516.tcenv}))) with
| Success (_90_1519) -> begin
(let wl = (let _90_1521 = wl
in {attempting = rest; wl_deferred = _90_1521.wl_deferred; ctr = _90_1521.ctr; defer_ok = _90_1521.defer_ok; smt_ok = _90_1521.smt_ok; tcenv = _90_1521.tcenv})
in (let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (let _90_1527 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _90_1530 -> begin
None
end)))
end))
end))
end
| _90_1532 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (let _90_1549 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_901 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _192_901))
end else begin
()
end
in (let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(let hd1 = (let _90_1563 = hd1
in (let _192_902 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _90_1563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _192_902}))
in (let hd2 = (let _90_1566 = hd2
in (let _192_903 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _90_1566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_1566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _192_903}))
in (let prob = (let _192_906 = (let _192_905 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _192_905 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _192_904 -> FStar_TypeChecker_Common.TProb (_192_904)) _192_906))
in (let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (let subst = (let _192_910 = (let _192_908 = (let _192_907 = (FStar_Syntax_Syntax.bv_to_name hd1)
in (0, _192_907))
in FStar_Syntax_Syntax.DB (_192_908))
in (let _192_909 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (_192_910)::_192_909))
in (let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _192_912 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _192_911 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _192_912 _192_911)))
in (let _90_1578 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_914 = (FStar_Syntax_Print.term_to_string phi)
in (let _192_913 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _192_914 _192_913)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _90_1582 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _192_918 = (compress_tprob wl problem)
in (solve_t' env _192_918 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (let imitate = (fun orig env wl p -> (let _90_1615 = p
in (match (_90_1615) with
| ((u, k), ps, xs, (h, _90_1612, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _90_1621 = (imitation_sub_probs orig env xs ps qs)
in (match (_90_1621) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _192_936 = (h gs_xs)
in (u_abs xs _192_936))
in (let _90_1623 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_941 = (FStar_Syntax_Print.term_to_string im)
in (let _192_940 = (FStar_Syntax_Print.tag_of_term im)
in (let _192_939 = (let _192_937 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _192_937 (FStar_String.concat ", ")))
in (let _192_938 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _192_941 _192_940 _192_939 _192_938)))))
end else begin
()
end
in (let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project = (fun orig env wl i p -> (let _90_1639 = p
in (match (_90_1639) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_TypeChecker_Env.get_range env)
in (let _90_1644 = (FStar_List.nth ps i)
in (match (_90_1644) with
| (pi, _90_1643) -> begin
(let _90_1648 = (FStar_List.nth xs i)
in (match (_90_1648) with
| (xi, _90_1647) -> begin
(let rec gs = (fun k -> (let _90_1653 = (FStar_Syntax_Util.arrow_formals k)
in (match (_90_1653) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _90_1661)::tl -> begin
(let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (let _90_1667 = (new_uvar r xs k_a)
in (match (_90_1667) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (let _90_1673 = (aux subst tl)
in (match (_90_1673) with
| (gi_xs', gi_ps') -> begin
(((FStar_Syntax_Syntax.as_arg gi_xs))::gi_xs', ((FStar_Syntax_Syntax.as_arg gi_ps))::gi_ps')
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _192_960 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _192_960)) then begin
None
end else begin
(let _90_1677 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_90_1677) with
| (g_xs, _90_1676) -> begin
(let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (let proj = (let _192_961 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _192_961))
in (let sub = (let _192_967 = (let _192_966 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _192_965 = (let _192_964 = (FStar_List.map (fun _90_1685 -> (match (_90_1685) with
| (_90_1681, _90_1683, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _192_964))
in (mk_problem (p_scope orig) orig _192_966 (p_rel orig) _192_965 None "projection")))
in (FStar_All.pipe_left (fun _192_962 -> FStar_TypeChecker_Common.TProb (_192_962)) _192_967))
in (let _90_1687 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_969 = (FStar_Syntax_Print.term_to_string proj)
in (let _192_968 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _192_969 _192_968)))
end else begin
()
end
in (let wl = (let _192_971 = (let _192_970 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_192_970))
in (solve_prob orig _192_971 ((TERM ((u, proj)))::[]) wl))
in (let _192_973 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _192_972 -> Some (_192_972)) _192_973)))))))
end))
end)
end))
end)))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _90_1701 = lhs
in (match (_90_1701) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _192_1000 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _192_1000 Prims.fst))
in (let _192_1005 = (decompose env t2)
in ((uv, k), ps, xs, _192_1005))))
in (let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_90_1711) -> begin
(let _90_1713 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(let _90_1721 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (let check_head = (fun fvs1 t2 -> (let _90_1731 = (FStar_Syntax_Util.head_and_args t2)
in (match (_90_1731) with
| (hd, _90_1730) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _90_1742 -> begin
(let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(let _90_1744 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1020 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _192_1020))
end else begin
()
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _192_1032 = (let _192_1031 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _192_1031 Prims.fst))
in (FStar_All.pipe_right _192_1032 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (FStar_Syntax_Free.names t1)
in (let fvs2 = (FStar_Syntax_Free.names t2)
in (let _90_1757 = (occurs_check env wl (uv, k) t2)
in (match (_90_1757) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _192_1042 = (let _192_1041 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _192_1041))
in (giveup_or_defer orig _192_1042))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _192_1043 = (subterms args_lhs)
in (imitate orig env wl _192_1043))
end else begin
(let _90_1758 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1046 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1045 = (names_to_string fvs1)
in (let _192_1044 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _192_1046 _192_1045 _192_1044))))
end else begin
()
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _90_1762 -> begin
(let _192_1047 = (sn_binders env vars)
in (u_abs _192_1047 t2))
end)
in (let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _90_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1050 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1049 = (names_to_string fvs1)
in (let _192_1048 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _192_1050 _192_1049 _192_1048))))
end else begin
()
end
in (let _192_1051 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _192_1051 (- (1)))))
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
if (let _192_1052 = (FStar_Syntax_Free.names t1)
in (check_head _192_1052 t2)) then begin
(let im_ok = (imitate_ok t2)
in (let _90_1769 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1053 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _192_1053 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _192_1054 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _192_1054 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun xs_opt _90_1781 -> (match (_90_1781) with
| (t, u, k, args) -> begin
(let _90_1785 = (FStar_Syntax_Util.arrow_formals k)
in (match (_90_1785) with
| (all_formals, _90_1784) -> begin
(let _90_1786 = ()
in (let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _90_1799 -> (match (_90_1799) with
| (x, imp) -> begin
(let _192_1076 = (FStar_Syntax_Syntax.bv_to_name x)
in (_192_1076, imp))
end))))
in (let pattern_vars = (FStar_List.rev pattern_vars)
in (let kk = (let _90_1805 = (FStar_Syntax_Util.type_u ())
in (match (_90_1805) with
| (t, _90_1804) -> begin
(let _192_1077 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _192_1077))
end))
in (let _90_1809 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_90_1809) with
| (t', tm_u1) -> begin
(let _90_1816 = (destruct_flex_t t')
in (match (_90_1816) with
| (_90_1811, u1, k1, _90_1815) -> begin
(let sol = (let _192_1079 = (let _192_1078 = (u_abs all_formals t')
in ((u, k), _192_1078))
in TERM (_192_1079))
in (let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
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
(let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _90_1835 -> (match (_90_1835) with
| (x, _90_1834) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _192_1085 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _192_1085 formals tl))
end)
end)
end)
end
| _90_1839 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _192_1086 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _192_1086 all_formals args))))
end))
end))
in (let solve_both_pats = (fun wl _90_1845 _90_1849 r -> (match ((_90_1845, _90_1849)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _192_1095 = (solve_prob orig None [] wl)
in (solve env _192_1095))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _90_1854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1098 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _192_1097 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _192_1096 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _192_1098 _192_1097 _192_1096))))
end else begin
()
end
in (let _90_1867 = (let _90_1859 = (FStar_Syntax_Util.type_u ())
in (match (_90_1859) with
| (t, _90_1858) -> begin
(let _90_1863 = (new_uvar r zs t)
in (match (_90_1863) with
| (k, _90_1862) -> begin
(new_uvar r zs k)
end))
end))
in (match (_90_1867) with
| (u_zs, _90_1866) -> begin
(let sub1 = (u_abs xs u_zs)
in (let _90_1871 = (occurs_check env wl (u1, k1) sub1)
in (match (_90_1871) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(let sub2 = (u_abs ys u_zs)
in (let _90_1877 = (occurs_check env wl (u2, k2) sub2)
in (match (_90_1877) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(let sol2 = TERM (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end))))))
end
end))
in (let solve_one_pat = (fun _90_1885 _90_1890 -> (match ((_90_1885, _90_1890)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _90_1891 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1104 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1103 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _192_1104 _192_1103)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let sub_probs = (FStar_List.map2 (fun _90_1896 _90_1900 -> (match ((_90_1896, _90_1900)) with
| ((a, _90_1895), (t2, _90_1899)) -> begin
(let _192_1109 = (let _192_1107 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _192_1107 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _192_1109 (fun _192_1108 -> FStar_TypeChecker_Common.TProb (_192_1108))))
end)) xs args2)
in (let guard = (let _192_1111 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _192_1111))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Syntax_Free.names t2)
in (let _90_1910 = (occurs_check env wl (u1, k1) t2)
in (match (_90_1910) with
| (occurs_ok, _90_1909) -> begin
(let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(let sol = (let _192_1121 = (let _192_1120 = (u_abs xs t2)
in ((u1, k1), _192_1120))
in TERM (_192_1121))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(let _90_1921 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_90_1921) with
| (sol, (_90_1916, u2, k2, ys)) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _90_1923 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _192_1122 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _192_1122))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _90_1928 -> begin
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
in (let _90_1933 = lhs
in (match (_90_1933) with
| (t1, u1, k1, args1) -> begin
(let _90_1938 = rhs
in (match (_90_1938) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.FStar_Syntax_Syntax.pos
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
| _90_1956 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _90_1960 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_90_1960) with
| (sol, _90_1959) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _90_1962 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _192_1123 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _192_1123))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _90_1967 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _192_1124 = (solve_prob orig None [] wl)
in (solve env _192_1124))
end else begin
(let t1 = problem.FStar_TypeChecker_Common.lhs
in (let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _192_1125 = (solve_prob orig None [] wl)
in (solve env _192_1125))
end else begin
(let _90_1971 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _192_1126 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _192_1126))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let match_num_binders = (fun _90_1976 _90_1979 -> (match ((_90_1976, _90_1979)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _90_1986 = (FStar_Util.first_N n bs)
in (match (_90_1986) with
| (bs, rest) -> begin
(let _192_1156 = (mk_cod rest)
in (bs, _192_1156))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _192_1160 = (let _192_1157 = (mk_cod1 [])
in (bs1, _192_1157))
in (let _192_1159 = (let _192_1158 = (mk_cod2 [])
in (bs2, _192_1158))
in (_192_1160, _192_1159)))
end else begin
if (l1 > l2) then begin
(let _192_1163 = (curry l2 bs1 mk_cod1)
in (let _192_1162 = (let _192_1161 = (mk_cod2 [])
in (bs2, _192_1161))
in (_192_1163, _192_1162)))
end else begin
(let _192_1166 = (let _192_1164 = (mk_cod1 [])
in (bs1, _192_1164))
in (let _192_1165 = (curry l1 bs2 mk_cod2)
in (_192_1166, _192_1165)))
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
(let mk_c = (fun c _90_24 -> (match (_90_24) with
| [] -> begin
c
end
| bs -> begin
(let _192_1171 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _192_1171))
end))
in (let _90_2029 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_90_2029) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _192_1178 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _192_1177 -> FStar_TypeChecker_Common.CProb (_192_1177)) _192_1178)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _90_2039), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _90_2045)) -> begin
(let mk_t = (fun t _90_25 -> (match (_90_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (let _90_2060 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_90_2060) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _192_1191 = (let _192_1190 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _192_1189 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _192_1190 problem.FStar_TypeChecker_Common.relation _192_1189 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _192_1188 -> FStar_TypeChecker_Common.TProb (_192_1188)) _192_1191))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_90_2065), FStar_Syntax_Syntax.Tm_refine (_90_2068)) -> begin
(let _90_2073 = (as_refinement env wl t1)
in (match (_90_2073) with
| (x1, phi1) -> begin
(let _90_2076 = (as_refinement env wl t2)
in (match (_90_2076) with
| (x2, phi2) -> begin
(let base_prob = (let _192_1193 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _192_1192 -> FStar_TypeChecker_Common.TProb (_192_1192)) _192_1193))
in (let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (let subst = (let _192_1196 = (let _192_1195 = (let _192_1194 = (FStar_Syntax_Syntax.bv_to_name x1)
in (0, _192_1194))
in FStar_Syntax_Syntax.DB (_192_1195))
in (_192_1196)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let env = (FStar_TypeChecker_Env.push_bv env x1)
in (let mk_imp = (fun imp phi1 phi2 -> (let _192_1213 = (imp phi1 phi2)
in (FStar_All.pipe_right _192_1213 (guard_on_element problem x1))))
in (let fallback = (fun _90_2088 -> (match (()) with
| () -> begin
(let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (let guard = (let _192_1216 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _192_1216 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let ref_prob = (let _192_1218 = (mk_problem (p_scope orig) orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _192_1217 -> FStar_TypeChecker_Common.TProb (_192_1217)) _192_1218))
in (match ((solve env (let _90_2093 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _90_2093.ctr; defer_ok = false; smt_ok = _90_2093.smt_ok; tcenv = _90_2093.tcenv}))) with
| Failed (_90_2096) -> begin
(fallback ())
end
| Success (_90_2099) -> begin
(let guard = (let _192_1221 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _192_1220 = (let _192_1219 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _192_1219 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _192_1221 _192_1220)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _90_2103 = wl
in {attempting = _90_2103.attempting; wl_deferred = _90_2103.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _90_2103.defer_ok; smt_ok = _90_2103.smt_ok; tcenv = _90_2103.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _192_1223 = (destruct_flex_t t1)
in (let _192_1222 = (destruct_flex_t t2)
in (flex_flex orig _192_1223 _192_1222)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _192_1224 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _192_1224 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _192_1225 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _192_1225)) then begin
(let _192_1228 = (FStar_All.pipe_left (fun _192_1226 -> FStar_TypeChecker_Common.TProb (_192_1226)) (let _90_2248 = problem
in {FStar_TypeChecker_Common.pid = _90_2248.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_2248.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _90_2248.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2248.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2248.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2248.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2248.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2248.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2248.FStar_TypeChecker_Common.rank}))
in (let _192_1227 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _192_1228 _192_1227 t2 wl)))
end else begin
(let _90_2252 = (base_and_refinement env wl t2)
in (match (_90_2252) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _192_1231 = (FStar_All.pipe_left (fun _192_1229 -> FStar_TypeChecker_Common.TProb (_192_1229)) (let _90_2254 = problem
in {FStar_TypeChecker_Common.pid = _90_2254.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_2254.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _90_2254.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2254.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2254.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2254.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2254.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2254.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2254.FStar_TypeChecker_Common.rank}))
in (let _192_1230 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _192_1231 _192_1230 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _90_2260 = y
in {FStar_Syntax_Syntax.ppname = _90_2260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_2260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _192_1233 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _192_1232 -> FStar_TypeChecker_Common.TProb (_192_1232)) _192_1233))
in (let guard = (let _192_1234 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _192_1234 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
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
(let _90_2293 = (base_and_refinement env wl t1)
in (match (_90_2293) with
| (t_base, _90_2292) -> begin
(solve_t env (let _90_2294 = problem
in {FStar_TypeChecker_Common.pid = _90_2294.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _90_2294.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2294.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2294.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2294.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2294.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2294.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2294.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_90_2297), _90_2300) -> begin
(let t2 = (let _192_1235 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _192_1235))
in (solve_t env (let _90_2303 = problem
in {FStar_TypeChecker_Common.pid = _90_2303.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_2303.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_2303.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _90_2303.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2303.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2303.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2303.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2303.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2303.FStar_TypeChecker_Common.rank}) wl))
end
| (_90_2306, FStar_Syntax_Syntax.Tm_refine (_90_2308)) -> begin
(let t1 = (let _192_1236 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _192_1236))
in (solve_t env (let _90_2312 = problem
in {FStar_TypeChecker_Common.pid = _90_2312.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _90_2312.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_2312.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2312.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2312.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2312.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2312.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2312.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2312.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_90_2329) -> begin
t
end
| _90_2332 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _192_1241 = (let _90_2333 = problem
in (let _192_1240 = (maybe_eta t1)
in (let _192_1239 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _90_2333.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _192_1240; FStar_TypeChecker_Common.relation = _90_2333.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _192_1239; FStar_TypeChecker_Common.element = _90_2333.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2333.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2333.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2333.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2333.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2333.FStar_TypeChecker_Common.rank})))
in (solve_t env _192_1241 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(let _90_2397 = (head_matches_delta env wl t1 t2)
in (match (_90_2397) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _90_2400) -> begin
(let head1 = (let _192_1242 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _192_1242 Prims.fst))
in (let head2 = (let _192_1243 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _192_1243 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_90_2407) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _90_2411) -> begin
(FStar_TypeChecker_Env.is_projector env tc.FStar_Syntax_Syntax.v)
end
| _90_2415 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _192_1249 = (let _192_1248 = (let _192_1247 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _192_1246 -> Some (_192_1246)) _192_1247))
in (solve_prob orig _192_1248 [] wl))
in (solve env _192_1249))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_90_2417, Some (t1, t2)) -> begin
(solve_t env (let _90_2423 = problem
in {FStar_TypeChecker_Common.pid = _90_2423.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _90_2423.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _90_2423.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2423.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2423.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2423.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2423.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2423.FStar_TypeChecker_Common.rank}) wl)
end
| (_90_2426, None) -> begin
(let _90_2429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1253 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1252 = (FStar_Syntax_Print.tag_of_term t1)
in (let _192_1251 = (FStar_Syntax_Print.term_to_string t2)
in (let _192_1250 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _192_1253 _192_1252 _192_1251 _192_1250)))))
end else begin
()
end
in (let _90_2433 = (FStar_Syntax_Util.head_and_args t1)
in (match (_90_2433) with
| (head, args) -> begin
(let _90_2436 = (FStar_Syntax_Util.head_and_args t2)
in (match (_90_2436) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _192_1258 = (let _192_1257 = (FStar_Syntax_Print.term_to_string head)
in (let _192_1256 = (args_to_string args)
in (let _192_1255 = (FStar_Syntax_Print.term_to_string head')
in (let _192_1254 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _192_1257 _192_1256 _192_1255 _192_1254)))))
in (giveup env _192_1258 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _192_1259 = (solve_prob orig None [] wl)
in (solve env _192_1259))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(let _90_2446 = (base_and_refinement env wl t1)
in (match (_90_2446) with
| (base1, refinement1) -> begin
(let _90_2449 = (base_and_refinement env wl t2)
in (match (_90_2449) with
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
(let subprobs = (FStar_List.map2 (fun _90_2462 _90_2466 -> (match ((_90_2462, _90_2466)) with
| ((a, _90_2461), (a', _90_2465)) -> begin
(let _192_1263 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _192_1262 -> FStar_TypeChecker_Common.TProb (_192_1262)) _192_1263))
end)) args args')
in (let formula = (let _192_1265 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _192_1265))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _90_2472 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _90_2475 = problem
in {FStar_TypeChecker_Common.pid = _90_2475.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _90_2475.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _90_2475.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2475.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2475.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2475.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2475.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2475.FStar_TypeChecker_Common.rank}) wl)))
end)
end))
end))
end
end)
end))
end)))
end)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _90_2479, _90_2481), _90_2485) -> begin
(solve_t' env (let _90_2487 = problem
in {FStar_TypeChecker_Common.pid = _90_2487.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _90_2487.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_2487.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2487.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2487.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2487.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2487.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2487.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2487.FStar_TypeChecker_Common.rank}) wl)
end
| (_90_2490, FStar_Syntax_Syntax.Tm_ascribed (t2, _90_2493, _90_2495)) -> begin
(solve_t' env (let _90_2499 = problem
in {FStar_TypeChecker_Common.pid = _90_2499.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_2499.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_2499.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _90_2499.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2499.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2499.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2499.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2499.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2499.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _192_1268 = (let _192_1267 = (FStar_Syntax_Print.tag_of_term t1)
in (let _192_1266 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _192_1267 _192_1266)))
in (FStar_All.failwith _192_1268))
end
| _90_2538 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (let c1 = problem.FStar_TypeChecker_Common.lhs
in (let c2 = problem.FStar_TypeChecker_Common.rhs
in (let orig = FStar_TypeChecker_Common.CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _90_2555 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (let sub_probs = (FStar_List.map2 (fun _90_2560 _90_2564 -> (match ((_90_2560, _90_2564)) with
| ((a1, _90_2559), (a2, _90_2563)) -> begin
(let _192_1283 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _192_1282 -> FStar_TypeChecker_Common.TProb (_192_1282)) _192_1283))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (let guard = (let _192_1285 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _192_1285))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _192_1286 = (solve_prob orig None [] wl)
in (solve env _192_1286))
end else begin
(let _90_2569 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1288 = (FStar_Syntax_Print.comp_to_string c1)
in (let _192_1287 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _192_1288 (rel_to_string problem.FStar_TypeChecker_Common.relation) _192_1287)))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _90_2574 = (c1, c2)
in (match (_90_2574) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_90_2576), FStar_Syntax_Syntax.Total (_90_2579)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _192_1289 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _192_1289 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _192_1291 = (let _90_2607 = problem
in (let _192_1290 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _90_2607.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _192_1290; FStar_TypeChecker_Common.relation = _90_2607.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _90_2607.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _90_2607.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2607.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2607.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2607.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2607.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2607.FStar_TypeChecker_Common.rank}))
in (solve_c env _192_1291 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _192_1293 = (let _90_2623 = problem
in (let _192_1292 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _90_2623.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _90_2623.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _90_2623.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _192_1292; FStar_TypeChecker_Common.element = _90_2623.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _90_2623.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _90_2623.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _90_2623.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _90_2623.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _90_2623.FStar_TypeChecker_Common.rank}))
in (solve_c env _192_1293 wl))
end
| (FStar_Syntax_Syntax.Comp (_90_2626), FStar_Syntax_Syntax.Comp (_90_2629)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _192_1294 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _192_1294 wl))
end else begin
(let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _90_2636 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _192_1295 = (FStar_Util.format2 "incompatible monad ordering: %s </: %s" (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name) (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name))
in (giveup env _192_1295 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let _90_2654 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _90_2647)::(wlp1, _90_2643)::[] -> begin
(wp1, wlp1)
end
| _90_2651 -> begin
(let _192_1297 = (let _192_1296 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _192_1296))
in (FStar_All.failwith _192_1297))
end)
in (match (_90_2654) with
| (wp, wlp) -> begin
(let c1 = (let _192_1303 = (let _192_1302 = (let _192_1298 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _192_1298))
in (let _192_1301 = (let _192_1300 = (let _192_1299 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _192_1299))
in (_192_1300)::[])
in (_192_1302)::_192_1301))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _192_1303; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _90_26 -> (match (_90_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _90_2661 -> begin
false
end))))
in (let _90_2682 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _90_2667)::_90_2664, (wp2, _90_2674)::_90_2671) -> begin
(wp1, wp2)
end
| _90_2679 -> begin
(let _192_1305 = (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name) (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name))
in (FStar_All.failwith _192_1305))
end)
in (match (_90_2682) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _192_1306 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _192_1306 wl))
end else begin
(let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _90_2684 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _192_1313 = (let _192_1312 = (let _192_1311 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (let _192_1310 = (let _192_1309 = (let _192_1308 = (let _192_1307 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _192_1307))
in (_192_1308)::[])
in ((FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ))::_192_1309)
in (_192_1311, _192_1310)))
in FStar_Syntax_Syntax.Tm_app (_192_1312))
in (FStar_Syntax_Syntax.mk _192_1313 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let wp2_imp_wp1 = (let _192_1324 = (let _192_1323 = (let _192_1322 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop)
in (let _192_1321 = (let _192_1320 = (let _192_1319 = (let _192_1318 = (let _192_1314 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid r)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _192_1314))
in (let _192_1317 = (let _192_1316 = (let _192_1315 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _192_1315))
in (_192_1316)::[])
in (_192_1318)::_192_1317))
in ((FStar_Syntax_Syntax.as_arg wpc2))::_192_1319)
in ((FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ))::_192_1320)
in (_192_1322, _192_1321)))
in FStar_Syntax_Syntax.Tm_app (_192_1323))
in (FStar_Syntax_Syntax.mk _192_1324 None r))
in (let _192_1327 = (let _192_1326 = (let _192_1325 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type)
in (_192_1325, ((FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ))::((FStar_Syntax_Syntax.as_arg wp2_imp_wp1))::[]))
in FStar_Syntax_Syntax.Tm_app (_192_1326))
in (FStar_Syntax_Syntax.mk _192_1327 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (let base_prob = (let _192_1329 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _192_1328 -> FStar_TypeChecker_Common.TProb (_192_1328)) _192_1329))
in (let wl = (let _192_1333 = (let _192_1332 = (let _192_1331 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _192_1331 g))
in (FStar_All.pipe_left (fun _192_1330 -> Some (_192_1330)) _192_1332))
in (solve_prob orig _192_1333 [] wl))
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

# 1837 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _192_1337 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _90_2700 -> (match (_90_2700) with
| (_90_2692, u, _90_2695, _90_2697, _90_2699) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _192_1337 (FStar_String.concat ", "))))

# 1839 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _90_2707 -> begin
(let form = (match (g.FStar_TypeChecker_Env.guard_f) with
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
in (let carry = (let _192_1343 = (FStar_List.map (fun _90_2715 -> (match (_90_2715) with
| (_90_2713, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _192_1343 (FStar_String.concat ",\n")))
in (let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

# 1857 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

# 1859 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

# 1861 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _90_2724; FStar_TypeChecker_Env.implicits = _90_2722} -> begin
true
end
| _90_2729 -> begin
false
end))

# 1865 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

# 1867 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _90_2747 -> begin
(FStar_All.failwith "impossible")
end)
in (let _192_1357 = (let _90_2749 = g
in (let _192_1356 = (let _192_1355 = (u_abs (((FStar_Syntax_Syntax.mk_binder x))::[]) f)
in (FStar_All.pipe_left (fun _192_1354 -> FStar_TypeChecker_Common.NonTrivial (_192_1354)) _192_1355))
in {FStar_TypeChecker_Env.guard_f = _192_1356; FStar_TypeChecker_Env.deferred = _90_2749.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_2749.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_2749.FStar_TypeChecker_Env.implicits}))
in Some (_192_1357)))
end))

# 1876 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let apply_guard : FStar_TypeChecker_Env.guard_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _90_2756 = g
in (let _192_1364 = (let _192_1363 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((f, ((FStar_Syntax_Syntax.as_arg e))::[]))) (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos)
in (FStar_All.pipe_left (fun _192_1362 -> FStar_TypeChecker_Common.NonTrivial (_192_1362)) _192_1363))
in {FStar_TypeChecker_Env.guard_f = _192_1364; FStar_TypeChecker_Env.deferred = _90_2756.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_2756.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_2756.FStar_TypeChecker_Env.implicits}))
end))

# 1880 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_90_2761) -> begin
(FStar_All.failwith "impossible")
end))

# 1884 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _192_1371 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_192_1371))
end))

# 1889 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _90_2778) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _90_2782 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

# 1893 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 1899 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _192_1394 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _192_1394; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

# 1903 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 1904 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 1906 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let close_guard : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _90_2809 = g
in (let _192_1409 = (let _192_1408 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _192_1408 (fun _192_1407 -> FStar_TypeChecker_Common.NonTrivial (_192_1407))))
in {FStar_TypeChecker_Env.guard_f = _192_1409; FStar_TypeChecker_Env.deferred = _90_2809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_2809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_2809.FStar_TypeChecker_Env.implicits}))
end))

# 1913 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _192_1417 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _192_1416 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _192_1417 (rel_to_string rel) _192_1416)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 1922 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (let x = (let _192_1427 = (FStar_All.pipe_left (fun _192_1426 -> Some (_192_1426)) (FStar_TypeChecker_Env.get_range env))
in (FStar_Syntax_Syntax.new_bv _192_1427 t1))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let p = (let _192_1430 = (let _192_1429 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _192_1428 -> Some (_192_1428)) _192_1429))
in (new_t_problem env t1 rel t2 _192_1430 (FStar_TypeChecker_Env.get_range env)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

# 1928 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(let _90_2829 = probs
in {attempting = _90_2829.attempting; wl_deferred = _90_2829.wl_deferred; ctr = _90_2829.ctr; defer_ok = false; smt_ok = _90_2829.smt_ok; tcenv = _90_2829.tcenv})
end else begin
probs
end
in (let tx = (FStar_Unionfind.new_transaction ())
in (let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(let _90_2836 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _90_2842 = (FStar_Unionfind.rollback tx)
in (let _90_2844 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _192_1442 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _192_1442))
end else begin
()
end
in (err (d, s))))
end)))))

# 1942 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _90_2851 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _192_1447 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _192_1447))
end else begin
()
end
in (let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (let _90_2854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _192_1448 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _192_1448))
end else begin
()
end
in (let f = (match ((let _192_1449 = (FStar_Syntax_Util.unmeta f)
in _192_1449.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _90_2858) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _90_2862 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (let _90_2864 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _90_2864.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_2864.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_2864.FStar_TypeChecker_Env.implicits})))))
end))

# 1953 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _192_1461 = (let _192_1460 = (let _192_1459 = (let _192_1458 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _192_1458 (fun _192_1457 -> FStar_TypeChecker_Common.NonTrivial (_192_1457))))
in {FStar_TypeChecker_Env.guard_f = _192_1459; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _192_1460))
in (FStar_All.pipe_left (fun _192_1456 -> Some (_192_1456)) _192_1461))
end))

# 1958 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (let _90_2875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1469 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1468 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _192_1469 _192_1468)))
end else begin
()
end
in (let prob = (let _192_1471 = (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None (FStar_TypeChecker_Env.get_range env))
in (FStar_All.pipe_left (fun _192_1470 -> FStar_TypeChecker_Common.TProb (_192_1470)) _192_1471))
in (let g = (let _192_1473 = (solve_and_commit env (singleton env prob) (fun _90_2878 -> None))
in (FStar_All.pipe_left (with_guard env prob) _192_1473))
in g))))

# 1965 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _192_1482 = (let _192_1481 = (let _192_1480 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (_192_1480, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_192_1481))
in (Prims.raise _192_1482))
end
| Some (g) -> begin
(let _90_2887 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1485 = (FStar_Syntax_Print.term_to_string t1)
in (let _192_1484 = (FStar_Syntax_Print.term_to_string t2)
in (let _192_1483 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _192_1485 _192_1484 _192_1483))))
end else begin
()
end
in g)
end))

# 1976 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (let _90_2892 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1493 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _192_1492 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _192_1493 _192_1492)))
end else begin
()
end
in (let _90_2896 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_90_2896) with
| (prob, x) -> begin
(let g = (let _192_1495 = (solve_and_commit env (singleton env prob) (fun _90_2897 -> None))
in (FStar_All.pipe_left (with_guard env prob) _192_1495))
in (let _90_2900 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _192_1499 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _192_1498 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _192_1497 = (let _192_1496 = (FStar_Util.must g)
in (guard_to_string env _192_1496))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _192_1499 _192_1498 _192_1497))))
end else begin
()
end
in (abstract_guard x g)))
end))))

# 1989 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let subtype_fail = (fun env t1 t2 -> (let _192_1505 = (let _192_1504 = (let _192_1503 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (_192_1503, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_192_1504))
in (Prims.raise _192_1505)))

# 1993 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (let _90_2908 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1513 = (FStar_Syntax_Print.comp_to_string c1)
in (let _192_1512 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _192_1513 _192_1512)))
end else begin
()
end
in (let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (let prob = (let _192_1515 = (new_problem env c1 rel c2 None (FStar_TypeChecker_Env.get_range env) "sub_comp")
in (FStar_All.pipe_left (fun _192_1514 -> FStar_TypeChecker_Common.CProb (_192_1514)) _192_1515))
in (let _192_1517 = (solve_and_commit env (singleton env prob) (fun _90_2912 -> None))
in (FStar_All.pipe_left (with_guard env prob) _192_1517))))))

# 2001 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (let fail = (fun msg u1 u2 -> (let _90_2921 = (FStar_Unionfind.rollback tx)
in (let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _192_1534 = (let _192_1533 = (let _192_1532 = (let _192_1531 = (FStar_Syntax_Print.univ_to_string u1)
in (let _192_1530 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _192_1531 _192_1530 msg)))
in (_192_1532, (FStar_TypeChecker_Env.get_range env)))
in FStar_Syntax_Syntax.Error (_192_1533))
in (Prims.raise _192_1534)))))
in (let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(let _90_2937 = hd
in (match (_90_2937) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _192_1541 = (insert uv u1 tl)
in (hd)::_192_1541)
end
end))
end))
in (let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _192_1546 = (insert uv u1 out)
in (group_by _192_1546 rest))
end)
end
| _90_2952 -> begin
None
end))
end))
in (let ad_hoc_fallback = (fun _90_2954 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _90_2957 -> begin
(let wl = (let _90_2958 = (empty_worklist env)
in {attempting = _90_2958.attempting; wl_deferred = _90_2958.wl_deferred; ctr = _90_2958.ctr; defer_ok = true; smt_ok = _90_2958.smt_ok; tcenv = _90_2958.tcenv})
in (let _90_2998 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _90_2963 -> (match (_90_2963) with
| (u1, u2) -> begin
(let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _90_2968 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _90_2978 -> begin
(u1)::[]
end)
in (let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _90_2983 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _90_27 -> (match (_90_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(let _90_2990 = (FStar_Syntax_Util.univ_kernel u)
in (match (_90_2990) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (let _90_2994 = (FStar_Syntax_Util.univ_kernel u')
in (match (_90_2994) with
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
| USolved (_90_2996) -> begin
()
end)
end)))
end))))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange "Universe inequality check not fully implemented")))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(let wl = (let _90_3002 = (empty_worklist env)
in {attempting = _90_3002.attempting; wl_deferred = _90_3002.wl_deferred; ctr = _90_3002.ctr; defer_ok = false; smt_ok = _90_3002.smt_ok; tcenv = _90_3002.tcenv})
in (let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _90_3017 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

# 2083 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (let tx = (FStar_Unionfind.new_transaction ())
in (let _90_3022 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

# 2088 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (let fail = (fun _90_3029 -> (match (_90_3029) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (let _90_3032 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_1567 = (wl_to_string wl)
in (let _192_1566 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _192_1567 _192_1566)))
end else begin
()
end
in (let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(let _90_3036 = g
in {FStar_TypeChecker_Env.guard_f = _90_3036.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _90_3036.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_3036.FStar_TypeChecker_Env.implicits})
end
| _90_3039 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (let _90_3041 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (let _90_3043 = g
in {FStar_TypeChecker_Env.guard_f = _90_3043.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_3043.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _90_3043.FStar_TypeChecker_Env.implicits})))))))

# 2101 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (let g = (solve_deferred_constraints env g)
in (let _90_3057 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(let _90_3055 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _192_1573 = (let _192_1572 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _192_1572))
in (FStar_TypeChecker_Errors.diag (FStar_TypeChecker_Env.get_range env) _192_1573))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (let _90_3059 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _90_3059.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_3059.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _90_3059.FStar_TypeChecker_Env.implicits}))))

# 2118 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _90_3066 -> begin
false
end))
in (let rec until_fixpoint = (fun _90_3070 implicits -> (match (_90_3070) with
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
(let _90_3081 = hd
in (match (_90_3081) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (let _90_3084 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _192_1584 = (FStar_Syntax_Print.uvar_to_string u)
in (let _192_1583 = (FStar_Syntax_Print.term_to_string tm)
in (let _192_1582 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _192_1584 _192_1583 _192_1582))))
end else begin
()
end
in (let _90_3091 = (env.FStar_TypeChecker_Env.type_of (let _90_3086 = env
in {FStar_TypeChecker_Env.solver = _90_3086.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_3086.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_3086.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_3086.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_3086.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_3086.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_3086.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_3086.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_3086.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_3086.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_3086.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_3086.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_3086.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_3086.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_3086.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_3086.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_3086.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_3086.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _90_3086.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _90_3086.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_90_3091) with
| (_90_3089, g) -> begin
(let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl))
end)))))
end
end))
end)
end))
in (let _90_3093 = g
in (let _192_1585 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _90_3093.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_3093.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _90_3093.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _192_1585})))))

# 2139 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (let g = (let _192_1590 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _192_1590 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _192_1591 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _192_1591))
end
| (_90_3102, _90_3104, _90_3106, _90_3108, r)::_90_3100 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

# 2145 "D:\\workspace\\universes\\FStar\\src\\typechecker\\rel.fs"

let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (let _90_3114 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _90_3114.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _90_3114.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _90_3114.FStar_TypeChecker_Env.implicits}))





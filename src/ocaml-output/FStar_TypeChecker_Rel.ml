
open Prims
let new_uvar = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _177_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _177_8 Prims.op_Negation)))))
in (let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _86_37 -> begin
(let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (let k' = (let _177_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _177_9))
in (let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _177_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_177_10, uv)))))
end))))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)

let is_TERM = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))

let is_UNIV = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))

let ___TERM____0 = (fun projectee -> (match (projectee) with
| TERM (_86_43) -> begin
_86_43
end))

let ___UNIV____0 = (fun projectee -> (match (projectee) with
| UNIV (_86_46) -> begin
_86_46
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

let is_Mkworklist = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)

let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_86_56) -> begin
_86_56
end))

let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_86_59) -> begin
_86_59
end))

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT -> begin
true
end
| _ -> begin
false
end))

type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

let rel_to_string = (fun _86_1 -> (match (_86_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))

let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

let prob_to_string = (fun env _86_2 -> (match (_86_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _177_109 = (let _177_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _177_107 = (let _177_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _177_105 = (let _177_104 = (let _177_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _177_102 = (let _177_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _177_100 = (let _177_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _177_98 = (let _177_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_177_97)::[])
in (_177_99)::_177_98))
in (_177_101)::_177_100))
in (_177_103)::_177_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_177_104)
in (_177_106)::_177_105))
in (_177_108)::_177_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _177_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _177_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _177_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _177_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _177_110)))
end))

let uvi_to_string = (fun env _86_3 -> (match (_86_3) with
| UNIV (u, t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _177_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _177_116 FStar_Util.string_of_int))
end
in (let _177_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _177_117)))
end
| TERM ((u, _86_83), t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _177_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _177_118 FStar_Util.string_of_int))
end
in (let _177_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _177_119)))
end))

let uvis_to_string = (fun env uvis -> (let _177_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _177_124 (FStar_String.concat ", "))))

let names_to_string = (fun nms -> (let _177_134 = (let _177_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _177_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _177_134 (FStar_String.concat ", "))))

let args_to_string = (fun args -> (let _177_137 = (FStar_All.pipe_right args (FStar_List.map (fun _86_96 -> (match (_86_96) with
| (x, _86_95) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _177_137 (FStar_String.concat " "))))

let empty_worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun env prob -> (let _86_100 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _86_100.wl_deferred; ctr = _86_100.ctr; defer_ok = _86_100.defer_ok; smt_ok = _86_100.smt_ok; tcenv = _86_100.tcenv}))

let wl_of_guard = (fun env g -> (let _86_104 = (empty_worklist env)
in (let _177_146 = (FStar_List.map Prims.snd g)
in {attempting = _177_146; wl_deferred = _86_104.wl_deferred; ctr = _86_104.ctr; defer_ok = false; smt_ok = _86_104.smt_ok; tcenv = _86_104.tcenv})))

let defer = (fun reason prob wl -> (let _86_109 = wl
in {attempting = _86_109.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _86_109.ctr; defer_ok = _86_109.defer_ok; smt_ok = _86_109.smt_ok; tcenv = _86_109.tcenv}))

let attempt = (fun probs wl -> (let _86_113 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _86_113.wl_deferred; ctr = _86_113.ctr; defer_ok = _86_113.defer_ok; smt_ok = _86_113.smt_ok; tcenv = _86_113.tcenv}))

let giveup = (fun env reason prob -> (let _86_118 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _177_163))
end else begin
()
end
in Failed ((prob, reason))))

let invert_rel = (fun _86_4 -> (match (_86_4) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))

let invert = (fun p -> (let _86_125 = p
in {FStar_TypeChecker_Common.pid = _86_125.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _86_125.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_125.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_125.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_125.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_125.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_125.FStar_TypeChecker_Common.rank}))

let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

let maybe_invert_p = (fun _86_5 -> (match (_86_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _177_170 -> FStar_TypeChecker_Common.TProb (_177_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _177_171 -> FStar_TypeChecker_Common.CProb (_177_171)))
end))

let vary_rel = (fun rel _86_6 -> (match (_86_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_pid = (fun _86_7 -> (match (_86_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

let p_rel = (fun _86_8 -> (match (_86_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

let p_reason = (fun _86_9 -> (match (_86_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

let p_loc = (fun _86_10 -> (match (_86_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

let p_guard = (fun _86_11 -> (match (_86_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

let p_scope = (fun _86_12 -> (match (_86_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

let p_invert = (fun _86_13 -> (match (_86_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _177_190 -> FStar_TypeChecker_Common.TProb (_177_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _177_191 -> FStar_TypeChecker_Common.CProb (_177_191)) (invert p))
end))

let is_top_level_prob = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

let next_pid = (let ctr = (FStar_ST.alloc 0)
in (fun _86_175 -> (match (()) with
| () -> begin
(let _86_176 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _177_204 = (next_pid ())
in (let _177_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _177_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _177_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

let new_problem = (fun env lhs rel rhs elt loc reason -> (let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _177_214 = (next_pid ())
in (let _177_213 = (let _177_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _177_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _177_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _177_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _177_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _177_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

let explain = (fun env d s -> (let _177_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _177_232 = (prob_to_string env d)
in (let _177_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _177_233 _177_232 _177_231 s)))))

let commit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _86_14 -> (match (_86_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _86_217 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _86_220), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

let find_term_uvar = (fun uv s -> (FStar_Util.find_map s (fun _86_15 -> (match (_86_15) with
| UNIV (_86_229) -> begin
None
end
| TERM ((u, _86_233), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

let find_univ_uvar = (fun u s -> (FStar_Util.find_map s (fun _86_16 -> (match (_86_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _86_246 -> begin
None
end))))

let whnf = (fun env t -> (let _177_252 = (let _177_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _177_251))
in (FStar_Syntax_Subst.compress _177_252)))

let sn = (fun env t -> (let _177_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _177_257)))

let norm_arg = (fun env t -> (let _177_260 = (sn env (Prims.fst t))
in (_177_260, (Prims.snd t))))

let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _86_257 -> (match (_86_257) with
| (x, imp) -> begin
(let _177_267 = (let _86_258 = x
in (let _177_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_258.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_258.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_266}))
in (_177_267, imp))
end)))))

let norm_univ = (fun wl u -> (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _177_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_177_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _177_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_177_275))
end
| _86_270 -> begin
u
end)))
in (let _177_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _177_276))))

let normalize_refinement = (fun steps env wl t0 -> (let _177_281 = (whnf env t0)
in (FStar_TypeChecker_Normalize.normalize_refinement steps env _177_281)))

let base_and_refinement = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _86_290; FStar_Syntax_Syntax.pos = _86_288; FStar_Syntax_Syntax.vars = _86_286} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _177_291 = (let _177_290 = (FStar_Syntax_Print.term_to_string tt)
in (let _177_289 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _177_290 _177_289)))
in (FStar_All.failwith _177_291))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _86_308 = (let _177_292 = (normalize_refinement [] env wl t1)
in (aux true _177_292))
in (match (_86_308) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _86_311 -> begin
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
(let _177_295 = (let _177_294 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_293 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _177_294 _177_293)))
in (FStar_All.failwith _177_295))
end))
in (let _177_296 = (whnf env t1)
in (aux false _177_296))))

let unrefine = (fun env t -> (let _177_301 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _177_301 Prims.fst)))

let trivial_refinement = (fun t -> (let _177_304 = (FStar_Syntax_Syntax.null_bv t)
in (_177_304, FStar_Syntax_Util.t_true)))

let as_refinement = (fun env wl t -> (let _86_357 = (base_and_refinement env wl t)
in (match (_86_357) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun _86_365 -> (match (_86_365) with
| (t_base, refopt) -> begin
(let _86_373 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_86_373) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

let wl_prob_to_string = (fun wl _86_17 -> (match (_86_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _177_317 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _177_316 = (let _177_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _177_313))
in (let _177_315 = (let _177_314 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _177_314))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _177_317 _177_316 (rel_to_string p.FStar_TypeChecker_Common.relation) _177_315))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _177_320 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _177_319 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _177_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _177_320 _177_319 (rel_to_string p.FStar_TypeChecker_Common.relation) _177_318))))
end))

let wl_to_string = (fun wl -> (let _177_326 = (let _177_325 = (let _177_324 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _86_386 -> (match (_86_386) with
| (_86_382, _86_384, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _177_324))
in (FStar_List.map (wl_prob_to_string wl) _177_325))
in (FStar_All.pipe_right _177_326 (FStar_String.concat "\n\t"))))

let u_abs = (fun x y -> (FStar_Syntax_Util.abs x y None))

let solve_prob' = (fun resolve_ok prob logical_guard uvis wl -> (let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _86_401 = (p_guard prob)
in (match (_86_401) with
| (_86_399, uv) -> begin
(let _86_414 = (match ((let _177_341 = (FStar_Syntax_Subst.compress uv)
in _177_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(let bs = (p_scope prob)
in (let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _177_343 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _177_343 Prims.op_Negation)))))
in (let phi = (u_abs bs phi)
in (let _86_410 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _177_346 = (FStar_Util.string_of_int (p_pid prob))
in (let _177_345 = (FStar_Syntax_Print.term_to_string uv)
in (let _177_344 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _177_346 _177_345 _177_344))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _86_413 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (let _86_416 = (commit uvis)
in (let _86_418 = wl
in {attempting = _86_418.attempting; wl_deferred = _86_418.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _86_418.defer_ok; smt_ok = _86_418.smt_ok; tcenv = _86_418.tcenv})))
end))))

let extend_solution = (fun pid sol wl -> (let _86_423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_355 = (FStar_Util.string_of_int pid)
in (let _177_354 = (let _177_353 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _177_353 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _177_355 _177_354)))
end else begin
()
end
in (let _86_425 = (commit sol)
in (let _86_427 = wl
in {attempting = _86_427.attempting; wl_deferred = _86_427.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _86_427.defer_ok; smt_ok = _86_427.smt_ok; tcenv = _86_427.tcenv}))))

let solve_prob = (fun prob logical_guard uvis wl -> (let conj_guard = (fun t g -> (match ((t, g)) with
| (_86_437, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _177_368 = (FStar_Syntax_Util.mk_conj t f)
in Some (_177_368))
end))
in (let _86_449 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_371 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _177_370 = (let _177_369 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _177_369 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _177_371 _177_370)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

let rec occurs = (fun wl uk t -> (let _177_381 = (let _177_379 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _177_379 FStar_Util.set_elements))
in (FStar_All.pipe_right _177_381 (FStar_Util.for_some (fun _86_458 -> (match (_86_458) with
| (uv, _86_457) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

let occurs_check = (fun env wl uk t -> (let occurs_ok = (not ((occurs wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _177_388 = (let _177_387 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _177_386 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _177_387 _177_386)))
in Some (_177_388))
end
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun env wl uk fvs t -> (let fvs_t = (FStar_Syntax_Free.names t)
in (let _86_473 = (occurs_check env wl uk t)
in (match (_86_473) with
| (occurs_ok, msg) -> begin
(let _177_420 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _177_420, (msg, fvs, fvs_t)))
end))))

let intersect_vars = (fun v1 v2 -> (let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (let v1_set = (as_set v1)
in (let _86_491 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _86_483 _86_486 -> (match ((_86_483, _86_486)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _177_429 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _177_429)) then begin
(isect, isect_set)
end else begin
(let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _177_430 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _177_430))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_86_491) with
| (isect, _86_490) -> begin
(FStar_List.rev isect)
end)))))

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _86_497 _86_501 -> (match ((_86_497, _86_501)) with
| ((a, _86_496), (b, _86_500)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _86_511 -> (match (_86_511) with
| (b, _86_510) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _86_513 -> begin
None
end)))

let rec pat_vars = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _86_522 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_445 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _177_445))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _86_536; FStar_Syntax_Syntax.pos = _86_534; FStar_Syntax_Syntax.vars = _86_532}, args) -> begin
(t, uv, k, args)
end
| _86_546 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun env t -> (let _86_553 = (destruct_flex_t t)
in (match (_86_553) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _86_557 -> begin
((t, uv, k, args), None)
end)
end)))

type match_result =
| MisMatch
| HeadMatch
| FullMatch

let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch -> begin
true
end
| _ -> begin
false
end))

let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch -> begin
true
end
| _ -> begin
false
end))

let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch -> begin
true
end
| _ -> begin
false
end))

let head_match = (fun _86_18 -> (match (_86_18) with
| MisMatch -> begin
MisMatch
end
| _86_561 -> begin
HeadMatch
end))

let rec head_matches = (fun t1 t2 -> (match ((let _177_461 = (let _177_458 = (FStar_Syntax_Util.unmeta t1)
in _177_458.FStar_Syntax_Syntax.n)
in (let _177_460 = (let _177_459 = (FStar_Syntax_Util.unmeta t2)
in _177_459.FStar_Syntax_Syntax.n)
in (_177_461, _177_460)))) with
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
| (FStar_Syntax_Syntax.Tm_uinst (f, _86_576), FStar_Syntax_Syntax.Tm_uinst (g, _86_581)) -> begin
(let _177_462 = (head_matches f g)
in (FStar_All.pipe_right _177_462 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _86_592), FStar_Syntax_Syntax.Tm_uvar (uv', _86_597)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _86_603), FStar_Syntax_Syntax.Tm_refine (y, _86_608)) -> begin
(let _177_463 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _177_463 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _86_614), _86_618) -> begin
(let _177_464 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _177_464 head_match))
end
| (_86_621, FStar_Syntax_Syntax.Tm_refine (x, _86_624)) -> begin
(let _177_465 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _177_465 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _86_644), FStar_Syntax_Syntax.Tm_app (head', _86_649)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _86_655), _86_659) -> begin
(head_matches head t2)
end
| (_86_662, FStar_Syntax_Syntax.Tm_app (head, _86_665)) -> begin
(head_matches t1 head)
end
| _86_670 -> begin
MisMatch
end))

let head_matches_delta = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun _86_681 -> (match (()) with
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

type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

let is_T = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_C = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

let ___T____0 = (fun projectee -> (match (projectee) with
| T (_86_694) -> begin
_86_694
end))

let ___C____0 = (fun projectee -> (match (projectee) with
| C (_86_697) -> begin
_86_697
end))

type tcs =
tc Prims.list

let rec decompose = (fun env t -> (let t = (FStar_Syntax_Util.unmeta t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_86_712, imp), T (t)) -> begin
(t, imp)
end
| _86_719 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _86_724 -> (match (_86_724) with
| (t, _86_723) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let fail = (fun _86_731 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let _86_734 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_86_734) with
| (bs, c) -> begin
(let rebuild = (fun tcs -> (let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((let _86_751 = x
in {FStar_Syntax_Syntax.ppname = _86_751.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_751.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _86_759 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (let rec decompose = (fun out _86_19 -> (match (_86_19) with
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
in (let _177_559 = (decompose [] bs)
in (rebuild, matches, _177_559))))
end)))
end
| _86_769 -> begin
(let rebuild = (fun _86_20 -> (match (_86_20) with
| [] -> begin
t
end
| _86_773 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

let un_T = (fun _86_21 -> (match (_86_21) with
| T (t) -> begin
t
end
| _86_780 -> begin
(FStar_All.failwith "Impossible")
end))

let arg_of_tc = (fun _86_22 -> (match (_86_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _86_785 -> begin
(FStar_All.failwith "Impossible")
end))

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_86_798, variance, T (ti)) -> begin
(let k = (let _86_806 = (FStar_Syntax_Util.type_u ())
in (match (_86_806) with
| (t, _86_805) -> begin
(let _177_581 = (new_uvar r scope t)
in (Prims.fst _177_581))
end))
in (let _86_810 = (new_uvar r scope k)
in (match (_86_810) with
| (gi_xs, gi) -> begin
(let gi_ps = (match (args) with
| [] -> begin
gi
end
| _86_813 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _177_584 = (let _177_583 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _177_582 -> FStar_TypeChecker_Common.TProb (_177_582)) _177_583))
in (T (gi_xs), _177_584)))
end)))
end
| (_86_816, _86_818, C (_86_820)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(let _86_898 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _86_838; FStar_Syntax_Syntax.pos = _86_836; FStar_Syntax_Syntax.vars = _86_834})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _177_593 = (let _177_592 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _177_591 -> C (_177_591)) _177_592))
in (_177_593, (prob)::[]))
end
| _86_849 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _86_857; FStar_Syntax_Syntax.pos = _86_855; FStar_Syntax_Syntax.vars = _86_853})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _177_596 = (let _177_595 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _177_594 -> C (_177_594)) _177_595))
in (_177_596, (prob)::[]))
end
| _86_868 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_86_870, _86_872, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _86_878; FStar_Syntax_Syntax.pos = _86_876; FStar_Syntax_Syntax.vars = _86_874})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (let _86_889 = (let _177_598 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _177_598 FStar_List.unzip))
in (match (_86_889) with
| (tcs, sub_probs) -> begin
(let gi_xs = (let _177_603 = (let _177_602 = (let _177_599 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _177_599 un_T))
in (let _177_601 = (let _177_600 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _177_600 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _177_602; FStar_Syntax_Syntax.effect_args = _177_601; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _177_603))
in (C (gi_xs), sub_probs))
end))))
end
| _86_892 -> begin
(let _86_895 = (sub_prob scope args q)
in (match (_86_895) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_86_898) with
| (tc, probs) -> begin
(let _86_911 = (match (q) with
| (Some (b), _86_902, _86_904) -> begin
(let _177_605 = (let _177_604 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_177_604)::args)
in (Some (b), (b)::scope, _177_605))
end
| _86_907 -> begin
(None, scope, args)
end)
in (match (_86_911) with
| (bopt, scope, args) -> begin
(let _86_915 = (aux scope args qs)
in (match (_86_915) with
| (sub_probs, tcs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _177_608 = (let _177_607 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_177_607)
in (FStar_Syntax_Util.mk_conj_l _177_608))
end
| Some (b) -> begin
(let _177_612 = (let _177_611 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _177_610 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_177_611)::_177_610))
in (FStar_Syntax_Util.mk_conj_l _177_612))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

let rec eq_tm = (fun t1 t2 -> (let t1 = (FStar_Syntax_Subst.compress t1)
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
| (FStar_Syntax_Syntax.Tm_uvar (u1, _86_943), FStar_Syntax_Syntax.Tm_uvar (u2, _86_948)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _86_962 -> begin
false
end))))
and eq_args = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _86_968 _86_972 -> (match ((_86_968, _86_972)) with
| ((a1, _86_967), (a2, _86_971)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

let rigid_rigid = 0

let flex_rigid_eq = 1

let flex_refine_inner = 2

let flex_refine = 3

let flex_rigid = 4

let rigid_flex = 5

let refine_flex = 6

let flex_flex = 7

let compress_tprob = (fun wl p -> (let _86_975 = p
in (let _177_634 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _177_633 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _86_975.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _177_634; FStar_TypeChecker_Common.relation = _86_975.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _177_633; FStar_TypeChecker_Common.element = _86_975.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_975.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_975.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_975.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_975.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_975.FStar_TypeChecker_Common.rank}))))

let compress_prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _177_640 = (compress_tprob wl p)
in (FStar_All.pipe_right _177_640 (fun _177_639 -> FStar_TypeChecker_Common.TProb (_177_639))))
end
| FStar_TypeChecker_Common.CProb (_86_982) -> begin
p
end))

let rank = (fun wl pr -> (let prob = (let _177_645 = (compress_prob wl pr)
in (FStar_All.pipe_right _177_645 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _86_992 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_86_992) with
| (lh, _86_991) -> begin
(let _86_996 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_86_996) with
| (rh, _86_995) -> begin
(let _86_1052 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_86_998), FStar_Syntax_Syntax.Tm_uvar (_86_1001)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_86_1017), _86_1020) -> begin
(let _86_1024 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_86_1024) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _86_1027 -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _177_647 = (let _86_1029 = tp
in (let _177_646 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _86_1029.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_1029.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_1029.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _177_646; FStar_TypeChecker_Common.element = _86_1029.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_1029.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_1029.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_1029.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_1029.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_1029.FStar_TypeChecker_Common.rank}))
in (rank, _177_647)))
end)
end))
end
| (_86_1032, FStar_Syntax_Syntax.Tm_uvar (_86_1034)) -> begin
(let _86_1039 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_86_1039) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _86_1042 -> begin
(let _177_649 = (let _86_1043 = tp
in (let _177_648 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _86_1043.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _177_648; FStar_TypeChecker_Common.relation = _86_1043.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_1043.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_1043.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_1043.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_1043.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_1043.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_1043.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_1043.FStar_TypeChecker_Common.rank}))
in (refine_flex, _177_649))
end)
end))
end
| (_86_1046, _86_1048) -> begin
(rigid_rigid, tp)
end)
in (match (_86_1052) with
| (rank, tp) -> begin
(let _177_651 = (FStar_All.pipe_right (let _86_1053 = tp
in {FStar_TypeChecker_Common.pid = _86_1053.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_1053.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_1053.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_1053.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_1053.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_1053.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_1053.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_1053.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_1053.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _177_650 -> FStar_TypeChecker_Common.TProb (_177_650)))
in (rank, _177_651))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _177_653 = (FStar_All.pipe_right (let _86_1057 = cp
in {FStar_TypeChecker_Common.pid = _86_1057.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_1057.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_1057.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_1057.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_1057.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_1057.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_1057.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_1057.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_1057.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _177_652 -> FStar_TypeChecker_Common.CProb (_177_652)))
in (rigid_rigid, _177_653))
end)))

let next_prob = (fun wl -> (let rec aux = (fun _86_1064 probs -> (match (_86_1064) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _86_1072 = (rank wl hd)
in (match (_86_1072) with
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

let is_flex_rigid = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

let is_UDeferred = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

let is_USolved = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

let is_UFailed = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

let ___UDeferred____0 = (fun projectee -> (match (projectee) with
| UDeferred (_86_1082) -> begin
_86_1082
end))

let ___USolved____0 = (fun projectee -> (match (projectee) with
| USolved (_86_1085) -> begin
_86_1085
end))

let ___UFailed____0 = (fun projectee -> (match (projectee) with
| UFailed (_86_1088) -> begin
_86_1088
end))

let rec solve_universe_eq = (fun orig wl u1 u2 -> (let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (let _86_1104 = (FStar_Syntax_Util.univ_kernel u)
in (match (_86_1104) with
| (k, _86_1103) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _86_1108 -> begin
false
end)
end)))))
end
| _86_1110 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_86_1116), FStar_Syntax_Syntax.U_max (_86_1119)) -> begin
(let _177_725 = (let _177_724 = (FStar_Syntax_Print.univ_to_string u1)
in (let _177_723 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _177_724 _177_723)))
in UFailed (_177_725))
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
| _86_1139 -> begin
(let _177_732 = (let _177_731 = (FStar_Syntax_Print.univ_to_string u1)
in (let _177_730 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _177_731 _177_730 msg)))
in UFailed (_177_732))
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
(let _177_735 = (let _177_734 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _177_733 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _177_734 _177_733)))
in (try_umax_components u1 u2 _177_735))
end else begin
(let _177_736 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_177_736))
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

let rec solve = (fun env probs -> (let _86_1234 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_779 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _177_779))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _86_1241 = probs
in {attempting = tl; wl_deferred = _86_1241.wl_deferred; ctr = _86_1241.ctr; defer_ok = _86_1241.defer_ok; smt_ok = _86_1241.smt_ok; tcenv = _86_1241.tcenv})
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
| (None, _86_1253, _86_1255) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _86_1259 -> begin
(let _86_1268 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _86_1265 -> (match (_86_1265) with
| (c, _86_1262, _86_1264) -> begin
(c < probs.ctr)
end))))
in (match (_86_1268) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _177_782 = (FStar_List.map (fun _86_1274 -> (match (_86_1274) with
| (_86_1271, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_177_782))
end
| _86_1276 -> begin
(let _177_785 = (let _86_1277 = probs
in (let _177_784 = (FStar_All.pipe_right attempt (FStar_List.map (fun _86_1284 -> (match (_86_1284) with
| (_86_1280, _86_1282, y) -> begin
y
end))))
in {attempting = _177_784; wl_deferred = rest; ctr = _86_1277.ctr; defer_ok = _86_1277.defer_ok; smt_ok = _86_1277.smt_ok; tcenv = _86_1277.tcenv}))
in (solve env _177_785))
end)
end))
end)
end)))
and solve_one_universe_eq = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _177_791 = (solve_prob orig None [] wl)
in (solve env _177_791))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts = (fun env orig t1 t2 wl -> (let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
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
| _86_1319 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _177_806 = (let _177_803 = (whnf env t1)
in _177_803.FStar_Syntax_Syntax.n)
in (let _177_805 = (let _177_804 = (whnf env t2)
in _177_804.FStar_Syntax_Syntax.n)
in (_177_806, _177_805)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _86_1325; FStar_Syntax_Syntax.pos = _86_1323; FStar_Syntax_Syntax.vars = _86_1321}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _86_1337; FStar_Syntax_Syntax.pos = _86_1335; FStar_Syntax_Syntax.vars = _86_1333}, us2)) -> begin
(let b = (FStar_Syntax_Syntax.fv_eq f g)
in (let _86_1346 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _86_1361 -> begin
USolved (wl)
end)))
and giveup_or_defer = (fun env orig wl msg -> if wl.defer_ok then begin
(let _86_1366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_811 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _177_811 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join = (fun env tp wl -> (let _86_1371 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_815 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _177_815))
end else begin
()
end
in (let _86_1375 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_86_1375) with
| (u, args) -> begin
(let _86_1381 = (0, 1, 2, 3, 4)
in (match (_86_1381) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun t1 t2 -> (let _86_1390 = (FStar_Syntax_Util.head_and_args t1)
in (match (_86_1390) with
| (h1, args1) -> begin
(let _86_1394 = (FStar_Syntax_Util.head_and_args t2)
in (match (_86_1394) with
| (h2, _86_1393) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _177_827 = (let _177_826 = (let _177_825 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _177_824 -> FStar_TypeChecker_Common.TProb (_177_824)) _177_825))
in (_177_826)::[])
in Some (_177_827))
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
| _86_1406 -> begin
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
in (let subst = (let _177_834 = (let _177_833 = (let _177_832 = (FStar_Syntax_Syntax.bv_to_name x)
in (0, _177_832))
in FStar_Syntax_Syntax.DB (_177_833))
in (_177_834)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _177_837 = (let _177_836 = (let _177_835 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _177_835))
in (_177_836, m))
in Some (_177_837))))))
end))
end
| (_86_1428, FStar_Syntax_Syntax.Tm_refine (y, _86_1431)) -> begin
(let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _86_1441), _86_1445) -> begin
(let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _86_1452 -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (uv, _86_1460) -> begin
(let _86_1485 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _86_23 -> (match (_86_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _86_1471 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_86_1471) with
| (u', _86_1470) -> begin
(match ((let _177_839 = (whnf env u')
in _177_839.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _86_1474) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _86_1478 -> begin
false
end)
end))
end
| _86_1480 -> begin
false
end)
end
| _86_1482 -> begin
false
end))))
in (match (_86_1485) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _86_1489 tps -> (match (_86_1489) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _177_844 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _177_844))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _86_1502 -> begin
None
end)
end))
in (match ((let _177_846 = (let _177_845 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_177_845, []))
in (make_upper_bound _177_846 upper_bounds))) with
| None -> begin
(let _86_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (let _86_1514 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let wl' = (let _86_1511 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _86_1511.wl_deferred; ctr = _86_1511.ctr; defer_ok = _86_1511.defer_ok; smt_ok = _86_1511.smt_ok; tcenv = _86_1511.tcenv})
in (let _177_847 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _177_847)))
end else begin
()
end
in (match ((solve_t env eq_prob (let _86_1516 = wl
in {attempting = sub_probs; wl_deferred = _86_1516.wl_deferred; ctr = _86_1516.ctr; defer_ok = _86_1516.defer_ok; smt_ok = _86_1516.smt_ok; tcenv = _86_1516.tcenv}))) with
| Success (_86_1519) -> begin
(let wl = (let _86_1521 = wl
in {attempting = rest; wl_deferred = _86_1521.wl_deferred; ctr = _86_1521.ctr; defer_ok = _86_1521.defer_ok; smt_ok = _86_1521.smt_ok; tcenv = _86_1521.tcenv})
in (let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (let _86_1527 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _86_1530 -> begin
None
end)))
end))
end))
end
| _86_1532 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders = (fun env bs1 bs2 orig wl rhs -> (let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (let _86_1549 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_875 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _177_875))
end else begin
()
end
in (let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(let hd1 = (let _86_1563 = hd1
in (let _177_876 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_1563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_1563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_876}))
in (let hd2 = (let _86_1566 = hd2
in (let _177_877 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_1566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_1566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_877}))
in (let prob = (let _177_880 = (let _177_879 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _177_879 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _177_878 -> FStar_TypeChecker_Common.TProb (_177_878)) _177_880))
in (let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (let subst = (let _177_884 = (let _177_882 = (let _177_881 = (FStar_Syntax_Syntax.bv_to_name hd1)
in (0, _177_881))
in FStar_Syntax_Syntax.DB (_177_882))
in (let _177_883 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (_177_884)::_177_883))
in (let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _177_886 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _177_885 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _177_886 _177_885)))
in (let _86_1578 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_888 = (FStar_Syntax_Print.term_to_string phi)
in (let _177_887 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _177_888 _177_887)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _86_1582 -> begin
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
and solve_t = (fun env problem wl -> (let _177_892 = (compress_tprob wl problem)
in (solve_t' env _177_892 wl)))
and solve_t' = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (let imitate = (fun orig env wl p -> (let _86_1615 = p
in (match (_86_1615) with
| ((u, k), ps, xs, (h, _86_1612, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _86_1621 = (imitation_sub_probs orig env xs ps qs)
in (match (_86_1621) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _177_910 = (h gs_xs)
in (u_abs xs _177_910))
in (let _86_1623 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_915 = (FStar_Syntax_Print.term_to_string im)
in (let _177_914 = (FStar_Syntax_Print.tag_of_term im)
in (let _177_913 = (let _177_911 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _177_911 (FStar_String.concat ", ")))
in (let _177_912 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _177_915 _177_914 _177_913 _177_912)))))
end else begin
()
end
in (let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project = (fun orig env wl i p -> (let _86_1639 = p
in (match (_86_1639) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_TypeChecker_Env.get_range env)
in (let _86_1644 = (FStar_List.nth ps i)
in (match (_86_1644) with
| (pi, _86_1643) -> begin
(let _86_1648 = (FStar_List.nth xs i)
in (match (_86_1648) with
| (xi, _86_1647) -> begin
(let rec gs = (fun k -> (let _86_1653 = (FStar_Syntax_Util.arrow_formals k)
in (match (_86_1653) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _86_1661)::tl -> begin
(let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (let _86_1667 = (new_uvar r xs k_a)
in (match (_86_1667) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (let _86_1673 = (aux subst tl)
in (match (_86_1673) with
| (gi_xs', gi_ps') -> begin
(let _177_937 = (let _177_934 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_177_934)::gi_xs')
in (let _177_936 = (let _177_935 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_177_935)::gi_ps')
in (_177_937, _177_936)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _177_938 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _177_938)) then begin
None
end else begin
(let _86_1677 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_86_1677) with
| (g_xs, _86_1676) -> begin
(let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (let proj = (let _177_939 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _177_939))
in (let sub = (let _177_945 = (let _177_944 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _177_943 = (let _177_942 = (FStar_List.map (fun _86_1685 -> (match (_86_1685) with
| (_86_1681, _86_1683, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _177_942))
in (mk_problem (p_scope orig) orig _177_944 (p_rel orig) _177_943 None "projection")))
in (FStar_All.pipe_left (fun _177_940 -> FStar_TypeChecker_Common.TProb (_177_940)) _177_945))
in (let _86_1687 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_947 = (FStar_Syntax_Print.term_to_string proj)
in (let _177_946 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _177_947 _177_946)))
end else begin
()
end
in (let wl = (let _177_949 = (let _177_948 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_177_948))
in (solve_prob orig _177_949 ((TERM ((u, proj)))::[]) wl))
in (let _177_951 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _177_950 -> Some (_177_950)) _177_951)))))))
end))
end)
end))
end)))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _86_1701 = lhs
in (match (_86_1701) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _177_978 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _177_978 Prims.fst))
in (let _177_983 = (decompose env t2)
in ((uv, k), ps, xs, _177_983))))
in (let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_86_1711) -> begin
(let _86_1713 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(let _86_1721 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (let check_head = (fun fvs1 t2 -> (let _86_1731 = (FStar_Syntax_Util.head_and_args t2)
in (match (_86_1731) with
| (hd, _86_1730) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _86_1742 -> begin
(let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(let _86_1744 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_994 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _177_994))
end else begin
()
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _177_998 = (let _177_997 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _177_997 Prims.fst))
in (FStar_All.pipe_right _177_998 FStar_Syntax_Free.names))
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
in (let _86_1757 = (occurs_check env wl (uv, k) t2)
in (match (_86_1757) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _177_1000 = (let _177_999 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _177_999))
in (giveup_or_defer orig _177_1000))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _177_1001 = (subterms args_lhs)
in (imitate orig env wl _177_1001))
end else begin
(let _86_1758 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1004 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1003 = (names_to_string fvs1)
in (let _177_1002 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _177_1004 _177_1003 _177_1002))))
end else begin
()
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _86_1762 -> begin
(let _177_1005 = (sn_binders env vars)
in (u_abs _177_1005 t2))
end)
in (let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _86_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1008 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1007 = (names_to_string fvs1)
in (let _177_1006 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _177_1008 _177_1007 _177_1006))))
end else begin
()
end
in (let _177_1009 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _177_1009 (- (1)))))
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
if (let _177_1010 = (FStar_Syntax_Free.names t1)
in (check_head _177_1010 t2)) then begin
(let im_ok = (imitate_ok t2)
in (let _86_1769 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1011 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _177_1011 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _177_1012 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _177_1012 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun xs_opt _86_1781 -> (match (_86_1781) with
| (t, u, k, args) -> begin
(let _86_1785 = (FStar_Syntax_Util.arrow_formals k)
in (match (_86_1785) with
| (all_formals, _86_1784) -> begin
(let _86_1786 = ()
in (let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _86_1799 -> (match (_86_1799) with
| (x, imp) -> begin
(let _177_1034 = (FStar_Syntax_Syntax.bv_to_name x)
in (_177_1034, imp))
end))))
in (let pattern_vars = (FStar_List.rev pattern_vars)
in (let kk = (let _86_1805 = (FStar_Syntax_Util.type_u ())
in (match (_86_1805) with
| (t, _86_1804) -> begin
(let _177_1035 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _177_1035))
end))
in (let _86_1809 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_86_1809) with
| (t', tm_u1) -> begin
(let _86_1816 = (destruct_flex_t t')
in (match (_86_1816) with
| (_86_1811, u1, k1, _86_1815) -> begin
(let sol = (let _177_1037 = (let _177_1036 = (u_abs all_formals t')
in ((u, k), _177_1036))
in TERM (_177_1037))
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
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _86_1835 -> (match (_86_1835) with
| (x, _86_1834) -> begin
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
(let _177_1039 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _177_1039 formals tl))
end)
end)
end)
end
| _86_1839 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _177_1040 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _177_1040 all_formals args))))
end))
end))
in (let solve_both_pats = (fun wl _86_1845 _86_1849 r -> (match ((_86_1845, _86_1849)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _177_1049 = (solve_prob orig None [] wl)
in (solve env _177_1049))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _86_1854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1052 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _177_1051 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _177_1050 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _177_1052 _177_1051 _177_1050))))
end else begin
()
end
in (let _86_1867 = (let _86_1859 = (FStar_Syntax_Util.type_u ())
in (match (_86_1859) with
| (t, _86_1858) -> begin
(let _86_1863 = (new_uvar r zs t)
in (match (_86_1863) with
| (k, _86_1862) -> begin
(new_uvar r zs k)
end))
end))
in (match (_86_1867) with
| (u_zs, _86_1866) -> begin
(let sub1 = (u_abs xs u_zs)
in (let _86_1871 = (occurs_check env wl (u1, k1) sub1)
in (match (_86_1871) with
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
in (let _86_1877 = (occurs_check env wl (u2, k2) sub2)
in (match (_86_1877) with
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
in (let solve_one_pat = (fun _86_1885 _86_1890 -> (match ((_86_1885, _86_1890)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _86_1891 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1058 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1057 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _177_1058 _177_1057)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let sub_probs = (FStar_List.map2 (fun _86_1896 _86_1900 -> (match ((_86_1896, _86_1900)) with
| ((a, _86_1895), (t2, _86_1899)) -> begin
(let _177_1063 = (let _177_1061 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _177_1061 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _177_1063 (fun _177_1062 -> FStar_TypeChecker_Common.TProb (_177_1062))))
end)) xs args2)
in (let guard = (let _177_1065 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _177_1065))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Syntax_Free.names t2)
in (let _86_1910 = (occurs_check env wl (u1, k1) t2)
in (match (_86_1910) with
| (occurs_ok, _86_1909) -> begin
(let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(let sol = (let _177_1067 = (let _177_1066 = (u_abs xs t2)
in ((u1, k1), _177_1066))
in TERM (_177_1067))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(let _86_1921 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_86_1921) with
| (sol, (_86_1916, u2, k2, ys)) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _86_1923 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _177_1068 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _177_1068))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _86_1928 -> begin
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
in (let _86_1933 = lhs
in (match (_86_1933) with
| (t1, u1, k1, args1) -> begin
(let _86_1938 = rhs
in (match (_86_1938) with
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
| _86_1956 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _86_1960 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_86_1960) with
| (sol, _86_1959) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _86_1962 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _177_1069 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _177_1069))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _86_1967 -> begin
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
(let _177_1070 = (solve_prob orig None [] wl)
in (solve env _177_1070))
end else begin
(let t1 = problem.FStar_TypeChecker_Common.lhs
in (let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _177_1071 = (solve_prob orig None [] wl)
in (solve env _177_1071))
end else begin
(let _86_1971 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _177_1072 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _177_1072))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let match_num_binders = (fun _86_1976 _86_1979 -> (match ((_86_1976, _86_1979)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _86_1986 = (FStar_Util.first_N n bs)
in (match (_86_1986) with
| (bs, rest) -> begin
(let _177_1102 = (mk_cod rest)
in (bs, _177_1102))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _177_1106 = (let _177_1103 = (mk_cod1 [])
in (bs1, _177_1103))
in (let _177_1105 = (let _177_1104 = (mk_cod2 [])
in (bs2, _177_1104))
in (_177_1106, _177_1105)))
end else begin
if (l1 > l2) then begin
(let _177_1109 = (curry l2 bs1 mk_cod1)
in (let _177_1108 = (let _177_1107 = (mk_cod2 [])
in (bs2, _177_1107))
in (_177_1109, _177_1108)))
end else begin
(let _177_1112 = (let _177_1110 = (mk_cod1 [])
in (bs1, _177_1110))
in (let _177_1111 = (curry l1 bs2 mk_cod2)
in (_177_1112, _177_1111)))
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
(let mk_c = (fun c _86_24 -> (match (_86_24) with
| [] -> begin
c
end
| bs -> begin
(let _177_1117 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _177_1117))
end))
in (let _86_2029 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_86_2029) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _177_1124 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _177_1123 -> FStar_TypeChecker_Common.CProb (_177_1123)) _177_1124)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _86_2039), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _86_2045)) -> begin
(let mk_t = (fun t _86_25 -> (match (_86_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (let _86_2060 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_86_2060) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _177_1137 = (let _177_1136 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _177_1135 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _177_1136 problem.FStar_TypeChecker_Common.relation _177_1135 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _177_1134 -> FStar_TypeChecker_Common.TProb (_177_1134)) _177_1137))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_86_2065), FStar_Syntax_Syntax.Tm_refine (_86_2068)) -> begin
(let _86_2073 = (as_refinement env wl t1)
in (match (_86_2073) with
| (x1, phi1) -> begin
(let _86_2076 = (as_refinement env wl t2)
in (match (_86_2076) with
| (x2, phi2) -> begin
(let base_prob = (let _177_1139 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _177_1138 -> FStar_TypeChecker_Common.TProb (_177_1138)) _177_1139))
in (let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (let subst = (let _177_1142 = (let _177_1141 = (let _177_1140 = (FStar_Syntax_Syntax.bv_to_name x1)
in (0, _177_1140))
in FStar_Syntax_Syntax.DB (_177_1141))
in (_177_1142)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let env = (FStar_TypeChecker_Env.push_bv env x1)
in (let mk_imp = (fun imp phi1 phi2 -> (let _177_1159 = (imp phi1 phi2)
in (FStar_All.pipe_right _177_1159 (guard_on_element problem x1))))
in (let fallback = (fun _86_2088 -> (match (()) with
| () -> begin
(let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (let guard = (let _177_1162 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _177_1162 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let ref_prob = (let _177_1164 = (mk_problem (p_scope orig) orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _177_1163 -> FStar_TypeChecker_Common.TProb (_177_1163)) _177_1164))
in (match ((solve env (let _86_2093 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _86_2093.ctr; defer_ok = false; smt_ok = _86_2093.smt_ok; tcenv = _86_2093.tcenv}))) with
| Failed (_86_2096) -> begin
(fallback ())
end
| Success (_86_2099) -> begin
(let guard = (let _177_1167 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _177_1166 = (let _177_1165 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _177_1165 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _177_1167 _177_1166)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _86_2103 = wl
in {attempting = _86_2103.attempting; wl_deferred = _86_2103.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _86_2103.defer_ok; smt_ok = _86_2103.smt_ok; tcenv = _86_2103.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _177_1169 = (destruct_flex_t t1)
in (let _177_1168 = (destruct_flex_t t2)
in (flex_flex orig _177_1169 _177_1168)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _177_1170 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _177_1170 t2 wl))
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
in if (let _177_1171 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _177_1171)) then begin
(let _177_1174 = (FStar_All.pipe_left (fun _177_1172 -> FStar_TypeChecker_Common.TProb (_177_1172)) (let _86_2248 = problem
in {FStar_TypeChecker_Common.pid = _86_2248.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_2248.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _86_2248.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2248.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2248.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2248.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2248.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2248.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2248.FStar_TypeChecker_Common.rank}))
in (let _177_1173 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _177_1174 _177_1173 t2 wl)))
end else begin
(let _86_2252 = (base_and_refinement env wl t2)
in (match (_86_2252) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _177_1177 = (FStar_All.pipe_left (fun _177_1175 -> FStar_TypeChecker_Common.TProb (_177_1175)) (let _86_2254 = problem
in {FStar_TypeChecker_Common.pid = _86_2254.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_2254.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _86_2254.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2254.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2254.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2254.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2254.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2254.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2254.FStar_TypeChecker_Common.rank}))
in (let _177_1176 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _177_1177 _177_1176 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _86_2260 = y
in {FStar_Syntax_Syntax.ppname = _86_2260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_2260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _177_1179 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _177_1178 -> FStar_TypeChecker_Common.TProb (_177_1178)) _177_1179))
in (let guard = (let _177_1180 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _177_1180 impl))
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
(let _86_2293 = (base_and_refinement env wl t1)
in (match (_86_2293) with
| (t_base, _86_2292) -> begin
(solve_t env (let _86_2294 = problem
in {FStar_TypeChecker_Common.pid = _86_2294.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _86_2294.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2294.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2294.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2294.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2294.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2294.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2294.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_86_2297), _86_2300) -> begin
(let t2 = (let _177_1181 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _177_1181))
in (solve_t env (let _86_2303 = problem
in {FStar_TypeChecker_Common.pid = _86_2303.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_2303.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_2303.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _86_2303.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2303.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2303.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2303.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2303.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2303.FStar_TypeChecker_Common.rank}) wl))
end
| (_86_2306, FStar_Syntax_Syntax.Tm_refine (_86_2308)) -> begin
(let t1 = (let _177_1182 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _177_1182))
in (solve_t env (let _86_2312 = problem
in {FStar_TypeChecker_Common.pid = _86_2312.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _86_2312.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_2312.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2312.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2312.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2312.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2312.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2312.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2312.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_86_2329) -> begin
t
end
| _86_2332 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _177_1187 = (let _86_2333 = problem
in (let _177_1186 = (maybe_eta t1)
in (let _177_1185 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _86_2333.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _177_1186; FStar_TypeChecker_Common.relation = _86_2333.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _177_1185; FStar_TypeChecker_Common.element = _86_2333.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2333.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2333.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2333.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2333.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2333.FStar_TypeChecker_Common.rank})))
in (solve_t env _177_1187 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(let _86_2397 = (head_matches_delta env wl t1 t2)
in (match (_86_2397) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _86_2400) -> begin
(let head1 = (let _177_1188 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _177_1188 Prims.fst))
in (let head2 = (let _177_1189 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _177_1189 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_86_2407) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _86_2411) -> begin
(FStar_TypeChecker_Env.is_projector env tc.FStar_Syntax_Syntax.v)
end
| _86_2415 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _177_1195 = (let _177_1194 = (let _177_1193 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _177_1192 -> Some (_177_1192)) _177_1193))
in (solve_prob orig _177_1194 [] wl))
in (solve env _177_1195))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_86_2417, Some (t1, t2)) -> begin
(solve_t env (let _86_2423 = problem
in {FStar_TypeChecker_Common.pid = _86_2423.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _86_2423.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _86_2423.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2423.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2423.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2423.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2423.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2423.FStar_TypeChecker_Common.rank}) wl)
end
| (_86_2426, None) -> begin
(let _86_2429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1199 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1198 = (FStar_Syntax_Print.tag_of_term t1)
in (let _177_1197 = (FStar_Syntax_Print.term_to_string t2)
in (let _177_1196 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _177_1199 _177_1198 _177_1197 _177_1196)))))
end else begin
()
end
in (let _86_2433 = (FStar_Syntax_Util.head_and_args t1)
in (match (_86_2433) with
| (head, args) -> begin
(let _86_2436 = (FStar_Syntax_Util.head_and_args t2)
in (match (_86_2436) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _177_1204 = (let _177_1203 = (FStar_Syntax_Print.term_to_string head)
in (let _177_1202 = (args_to_string args)
in (let _177_1201 = (FStar_Syntax_Print.term_to_string head')
in (let _177_1200 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _177_1203 _177_1202 _177_1201 _177_1200)))))
in (giveup env _177_1204 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _177_1205 = (solve_prob orig None [] wl)
in (solve env _177_1205))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(let _86_2446 = (base_and_refinement env wl t1)
in (match (_86_2446) with
| (base1, refinement1) -> begin
(let _86_2449 = (base_and_refinement env wl t2)
in (match (_86_2449) with
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
(let subprobs = (FStar_List.map2 (fun _86_2462 _86_2466 -> (match ((_86_2462, _86_2466)) with
| ((a, _86_2461), (a', _86_2465)) -> begin
(let _177_1209 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _177_1208 -> FStar_TypeChecker_Common.TProb (_177_1208)) _177_1209))
end)) args args')
in (let formula = (let _177_1211 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _177_1211))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _86_2472 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _86_2475 = problem
in {FStar_TypeChecker_Common.pid = _86_2475.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _86_2475.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _86_2475.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2475.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2475.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2475.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2475.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2475.FStar_TypeChecker_Common.rank}) wl)))
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
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _86_2479, _86_2481), _86_2485) -> begin
(solve_t' env (let _86_2487 = problem
in {FStar_TypeChecker_Common.pid = _86_2487.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _86_2487.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_2487.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2487.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2487.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2487.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2487.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2487.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2487.FStar_TypeChecker_Common.rank}) wl)
end
| (_86_2490, FStar_Syntax_Syntax.Tm_ascribed (t2, _86_2493, _86_2495)) -> begin
(solve_t' env (let _86_2499 = problem
in {FStar_TypeChecker_Common.pid = _86_2499.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_2499.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_2499.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _86_2499.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2499.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2499.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2499.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2499.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2499.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _177_1214 = (let _177_1213 = (FStar_Syntax_Print.tag_of_term t1)
in (let _177_1212 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _177_1213 _177_1212)))
in (FStar_All.failwith _177_1214))
end
| _86_2538 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c = (fun env problem wl -> (let c1 = problem.FStar_TypeChecker_Common.lhs
in (let c2 = problem.FStar_TypeChecker_Common.rhs
in (let orig = FStar_TypeChecker_Common.CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _86_2555 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (let sub_probs = (FStar_List.map2 (fun _86_2560 _86_2564 -> (match ((_86_2560, _86_2564)) with
| ((a1, _86_2559), (a2, _86_2563)) -> begin
(let _177_1229 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _177_1228 -> FStar_TypeChecker_Common.TProb (_177_1228)) _177_1229))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (let guard = (let _177_1231 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _177_1231))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _177_1232 = (solve_prob orig None [] wl)
in (solve env _177_1232))
end else begin
(let _86_2569 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1234 = (FStar_Syntax_Print.comp_to_string c1)
in (let _177_1233 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _177_1234 (rel_to_string problem.FStar_TypeChecker_Common.relation) _177_1233)))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _86_2574 = (c1, c2)
in (match (_86_2574) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_86_2576), FStar_Syntax_Syntax.Total (_86_2579)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _177_1235 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _177_1235 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _177_1237 = (let _86_2607 = problem
in (let _177_1236 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _86_2607.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _177_1236; FStar_TypeChecker_Common.relation = _86_2607.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _86_2607.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _86_2607.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2607.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2607.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2607.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2607.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2607.FStar_TypeChecker_Common.rank}))
in (solve_c env _177_1237 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _177_1239 = (let _86_2623 = problem
in (let _177_1238 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _86_2623.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _86_2623.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _86_2623.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _177_1238; FStar_TypeChecker_Common.element = _86_2623.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _86_2623.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _86_2623.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _86_2623.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _86_2623.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _86_2623.FStar_TypeChecker_Common.rank}))
in (solve_c env _177_1239 wl))
end
| (FStar_Syntax_Syntax.Comp (_86_2626), FStar_Syntax_Syntax.Comp (_86_2629)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _177_1240 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _177_1240 wl))
end else begin
(let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _86_2636 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _177_1243 = (let _177_1242 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _177_1241 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _177_1242 _177_1241)))
in (giveup env _177_1243 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let _86_2654 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _86_2647)::(wlp1, _86_2643)::[] -> begin
(wp1, wlp1)
end
| _86_2651 -> begin
(let _177_1245 = (let _177_1244 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _177_1244))
in (FStar_All.failwith _177_1245))
end)
in (match (_86_2654) with
| (wp, wlp) -> begin
(let c1 = (let _177_1251 = (let _177_1250 = (let _177_1246 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _177_1246))
in (let _177_1249 = (let _177_1248 = (let _177_1247 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _177_1247))
in (_177_1248)::[])
in (_177_1250)::_177_1249))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _177_1251; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _86_26 -> (match (_86_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _86_2661 -> begin
false
end))))
in (let _86_2682 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _86_2667)::_86_2664, (wp2, _86_2674)::_86_2671) -> begin
(wp1, wp2)
end
| _86_2679 -> begin
(let _177_1255 = (let _177_1254 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _177_1253 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _177_1254 _177_1253)))
in (FStar_All.failwith _177_1255))
end)
in (match (_86_2682) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _177_1256 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _177_1256 wl))
end else begin
(let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _86_2684 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _177_1264 = (let _177_1263 = (let _177_1262 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (let _177_1261 = (let _177_1260 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _177_1259 = (let _177_1258 = (let _177_1257 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _177_1257))
in (_177_1258)::[])
in (_177_1260)::_177_1259))
in (_177_1262, _177_1261)))
in FStar_Syntax_Syntax.Tm_app (_177_1263))
in (FStar_Syntax_Syntax.mk _177_1264 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let wp2_imp_wp1 = (let _177_1277 = (let _177_1276 = (let _177_1275 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop)
in (let _177_1274 = (let _177_1273 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _177_1272 = (let _177_1271 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _177_1270 = (let _177_1269 = (let _177_1265 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid r)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _177_1265))
in (let _177_1268 = (let _177_1267 = (let _177_1266 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _177_1266))
in (_177_1267)::[])
in (_177_1269)::_177_1268))
in (_177_1271)::_177_1270))
in (_177_1273)::_177_1272))
in (_177_1275, _177_1274)))
in FStar_Syntax_Syntax.Tm_app (_177_1276))
in (FStar_Syntax_Syntax.mk _177_1277 None r))
in (let _177_1284 = (let _177_1283 = (let _177_1282 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type)
in (let _177_1281 = (let _177_1280 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _177_1279 = (let _177_1278 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_177_1278)::[])
in (_177_1280)::_177_1279))
in (_177_1282, _177_1281)))
in FStar_Syntax_Syntax.Tm_app (_177_1283))
in (FStar_Syntax_Syntax.mk _177_1284 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (let base_prob = (let _177_1286 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _177_1285 -> FStar_TypeChecker_Common.TProb (_177_1285)) _177_1286))
in (let wl = (let _177_1290 = (let _177_1289 = (let _177_1288 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _177_1288 g))
in (FStar_All.pipe_left (fun _177_1287 -> Some (_177_1287)) _177_1289))
in (solve_prob orig _177_1290 [] wl))
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

let print_pending_implicits = (fun g -> (let _177_1294 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _86_2700 -> (match (_86_2700) with
| (_86_2692, u, _86_2695, _86_2697, _86_2699) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _177_1294 (FStar_String.concat ", "))))

let guard_to_string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _86_2707 -> begin
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
in (let carry = (let _177_1300 = (FStar_List.map (fun _86_2715 -> (match (_86_2715) with
| (_86_2713, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _177_1300 (FStar_String.concat ",\n")))
in (let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

let guard_of_guard_formula = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

let guard_form = (fun g -> g.FStar_TypeChecker_Env.guard_f)

let is_trivial = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _86_2724; FStar_TypeChecker_Env.implicits = _86_2722} -> begin
true
end
| _86_2729 -> begin
false
end))

let trivial_guard = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

let abstract_guard = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _86_2747 -> begin
(FStar_All.failwith "impossible")
end)
in (let _177_1316 = (let _86_2749 = g
in (let _177_1315 = (let _177_1314 = (let _177_1313 = (let _177_1312 = (FStar_Syntax_Syntax.mk_binder x)
in (_177_1312)::[])
in (u_abs _177_1313 f))
in (FStar_All.pipe_left (fun _177_1311 -> FStar_TypeChecker_Common.NonTrivial (_177_1311)) _177_1314))
in {FStar_TypeChecker_Env.guard_f = _177_1315; FStar_TypeChecker_Env.deferred = _86_2749.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_2749.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_2749.FStar_TypeChecker_Env.implicits}))
in Some (_177_1316)))
end))

let apply_guard = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _86_2756 = g
in (let _177_1327 = (let _177_1326 = (let _177_1325 = (let _177_1324 = (let _177_1323 = (let _177_1322 = (FStar_Syntax_Syntax.as_arg e)
in (_177_1322)::[])
in (f, _177_1323))
in FStar_Syntax_Syntax.Tm_app (_177_1324))
in (FStar_Syntax_Syntax.mk _177_1325 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _177_1321 -> FStar_TypeChecker_Common.NonTrivial (_177_1321)) _177_1326))
in {FStar_TypeChecker_Env.guard_f = _177_1327; FStar_TypeChecker_Env.deferred = _86_2756.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_2756.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_2756.FStar_TypeChecker_Env.implicits}))
end))

let trivial = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_86_2761) -> begin
(FStar_All.failwith "impossible")
end))

let conj_guard_f = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _177_1334 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_177_1334))
end))

let check_trivial = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _86_2778) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _86_2782 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

let imp_guard_f = (fun g1 g2 -> (match ((g1, g2)) with
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

let binop_guard = (fun f g1 g2 -> (let _177_1357 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _177_1357; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

let conj_guard = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _86_2809 = g
in (let _177_1372 = (let _177_1371 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _177_1371 (fun _177_1370 -> FStar_TypeChecker_Common.NonTrivial (_177_1370))))
in {FStar_TypeChecker_Env.guard_f = _177_1372; FStar_TypeChecker_Env.deferred = _86_2809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_2809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_2809.FStar_TypeChecker_Env.implicits}))
end))

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _177_1380 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _177_1379 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _177_1380 (rel_to_string rel) _177_1379)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun env t1 rel t2 -> (let x = (let _177_1391 = (let _177_1390 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _177_1389 -> Some (_177_1389)) _177_1390))
in (FStar_Syntax_Syntax.new_bv _177_1391 t1))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let p = (let _177_1395 = (let _177_1393 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _177_1392 -> Some (_177_1392)) _177_1393))
in (let _177_1394 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _177_1395 _177_1394)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

let solve_and_commit = (fun env probs err -> (let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(let _86_2829 = probs
in {attempting = _86_2829.attempting; wl_deferred = _86_2829.wl_deferred; ctr = _86_2829.ctr; defer_ok = false; smt_ok = _86_2829.smt_ok; tcenv = _86_2829.tcenv})
end else begin
probs
end
in (let tx = (FStar_Unionfind.new_transaction ())
in (let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(let _86_2836 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _86_2842 = (FStar_Unionfind.rollback tx)
in (let _86_2844 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _177_1407 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _177_1407))
end else begin
()
end
in (err (d, s))))
end)))))

let simplify_guard = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _86_2851 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _177_1412 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _177_1412))
end else begin
()
end
in (let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (let _86_2854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _177_1413 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _177_1413))
end else begin
()
end
in (let f = (match ((let _177_1414 = (FStar_Syntax_Util.unmeta f)
in _177_1414.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _86_2858) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _86_2862 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (let _86_2864 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _86_2864.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_2864.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_2864.FStar_TypeChecker_Env.implicits})))))
end))

let with_guard = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _177_1426 = (let _177_1425 = (let _177_1424 = (let _177_1423 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _177_1423 (fun _177_1422 -> FStar_TypeChecker_Common.NonTrivial (_177_1422))))
in {FStar_TypeChecker_Env.guard_f = _177_1424; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _177_1425))
in (FStar_All.pipe_left (fun _177_1421 -> Some (_177_1421)) _177_1426))
end))

let try_teq = (fun env t1 t2 -> (let _86_2875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1434 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1433 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _177_1434 _177_1433)))
end else begin
()
end
in (let prob = (let _177_1437 = (let _177_1436 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _177_1436))
in (FStar_All.pipe_left (fun _177_1435 -> FStar_TypeChecker_Common.TProb (_177_1435)) _177_1437))
in (let g = (let _177_1439 = (solve_and_commit env (singleton env prob) (fun _86_2878 -> None))
in (FStar_All.pipe_left (with_guard env prob) _177_1439))
in g))))

let teq = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _177_1449 = (let _177_1448 = (let _177_1447 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _177_1446 = (FStar_TypeChecker_Env.get_range env)
in (_177_1447, _177_1446)))
in FStar_Syntax_Syntax.Error (_177_1448))
in (Prims.raise _177_1449))
end
| Some (g) -> begin
(let _86_2887 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1452 = (FStar_Syntax_Print.term_to_string t1)
in (let _177_1451 = (FStar_Syntax_Print.term_to_string t2)
in (let _177_1450 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _177_1452 _177_1451 _177_1450))))
end else begin
()
end
in g)
end))

let try_subtype = (fun env t1 t2 -> (let _86_2892 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1460 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _177_1459 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _177_1460 _177_1459)))
end else begin
()
end
in (let _86_2896 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_86_2896) with
| (prob, x) -> begin
(let g = (let _177_1462 = (solve_and_commit env (singleton env prob) (fun _86_2897 -> None))
in (FStar_All.pipe_left (with_guard env prob) _177_1462))
in (let _86_2900 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _177_1466 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _177_1465 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _177_1464 = (let _177_1463 = (FStar_Util.must g)
in (guard_to_string env _177_1463))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _177_1466 _177_1465 _177_1464))))
end else begin
()
end
in (abstract_guard x g)))
end))))

let subtype_fail = (fun env t1 t2 -> (let _177_1473 = (let _177_1472 = (let _177_1471 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _177_1470 = (FStar_TypeChecker_Env.get_range env)
in (_177_1471, _177_1470)))
in FStar_Syntax_Syntax.Error (_177_1472))
in (Prims.raise _177_1473)))

let sub_comp = (fun env c1 c2 -> (let _86_2908 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1481 = (FStar_Syntax_Print.comp_to_string c1)
in (let _177_1480 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _177_1481 _177_1480)))
end else begin
()
end
in (let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (let prob = (let _177_1484 = (let _177_1483 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _177_1483 "sub_comp"))
in (FStar_All.pipe_left (fun _177_1482 -> FStar_TypeChecker_Common.CProb (_177_1482)) _177_1484))
in (let _177_1486 = (solve_and_commit env (singleton env prob) (fun _86_2912 -> None))
in (FStar_All.pipe_left (with_guard env prob) _177_1486))))))

let solve_universe_inequalities' = (fun tx env ineqs -> (let fail = (fun msg u1 u2 -> (let _86_2921 = (FStar_Unionfind.rollback tx)
in (let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _177_1504 = (let _177_1503 = (let _177_1502 = (let _177_1500 = (FStar_Syntax_Print.univ_to_string u1)
in (let _177_1499 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _177_1500 _177_1499 msg)))
in (let _177_1501 = (FStar_TypeChecker_Env.get_range env)
in (_177_1502, _177_1501)))
in FStar_Syntax_Syntax.Error (_177_1503))
in (Prims.raise _177_1504)))))
in (let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(let _86_2937 = hd
in (match (_86_2937) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _177_1511 = (insert uv u1 tl)
in (hd)::_177_1511)
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
(let _177_1516 = (insert uv u1 out)
in (group_by _177_1516 rest))
end)
end
| _86_2952 -> begin
None
end))
end))
in (let ad_hoc_fallback = (fun _86_2954 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _86_2957 -> begin
(let wl = (let _86_2958 = (empty_worklist env)
in {attempting = _86_2958.attempting; wl_deferred = _86_2958.wl_deferred; ctr = _86_2958.ctr; defer_ok = true; smt_ok = _86_2958.smt_ok; tcenv = _86_2958.tcenv})
in (let _86_2998 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _86_2963 -> (match (_86_2963) with
| (u1, u2) -> begin
(let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _86_2968 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _86_2978 -> begin
(u1)::[]
end)
in (let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _86_2983 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _86_27 -> (match (_86_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(let _86_2990 = (FStar_Syntax_Util.univ_kernel u)
in (match (_86_2990) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (let _86_2994 = (FStar_Syntax_Util.univ_kernel u')
in (match (_86_2994) with
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
| USolved (_86_2996) -> begin
()
end)
end)))
end))))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange "Universe inequality check not fully implemented")))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(let wl = (let _86_3002 = (empty_worklist env)
in {attempting = _86_3002.attempting; wl_deferred = _86_3002.wl_deferred; ctr = _86_3002.ctr; defer_ok = false; smt_ok = _86_3002.smt_ok; tcenv = _86_3002.tcenv})
in (let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _86_3017 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

let solve_universe_inequalities = (fun env ineqs -> (let tx = (FStar_Unionfind.new_transaction ())
in (let _86_3022 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

let rec solve_deferred_constraints = (fun env g -> (let fail = (fun _86_3029 -> (match (_86_3029) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (let _86_3032 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_1537 = (wl_to_string wl)
in (let _177_1536 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _177_1537 _177_1536)))
end else begin
()
end
in (let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(let _86_3036 = g
in {FStar_TypeChecker_Env.guard_f = _86_3036.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _86_3036.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_3036.FStar_TypeChecker_Env.implicits})
end
| _86_3039 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (let _86_3041 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (let _86_3043 = g
in {FStar_TypeChecker_Env.guard_f = _86_3043.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _86_3043.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _86_3043.FStar_TypeChecker_Env.implicits})))))))

let discharge_guard = (fun env g -> (let g = (solve_deferred_constraints env g)
in (let _86_3057 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
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
(let _86_3055 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _177_1544 = (FStar_TypeChecker_Env.get_range env)
in (let _177_1543 = (let _177_1542 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _177_1542))
in (FStar_TypeChecker_Errors.diag _177_1544 _177_1543)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (let _86_3059 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _86_3059.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_3059.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _86_3059.FStar_TypeChecker_Env.implicits}))))

let resolve_implicits = (fun g -> (let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _86_3066 -> begin
false
end))
in (let rec until_fixpoint = (fun _86_3070 implicits -> (match (_86_3070) with
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
(let _86_3081 = hd
in (match (_86_3081) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (let _86_3084 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _177_1555 = (FStar_Syntax_Print.uvar_to_string u)
in (let _177_1554 = (FStar_Syntax_Print.term_to_string tm)
in (let _177_1553 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _177_1555 _177_1554 _177_1553))))
end else begin
()
end
in (let _86_3091 = (env.FStar_TypeChecker_Env.type_of (let _86_3086 = env
in {FStar_TypeChecker_Env.solver = _86_3086.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _86_3086.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _86_3086.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _86_3086.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _86_3086.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _86_3086.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _86_3086.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _86_3086.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _86_3086.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _86_3086.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _86_3086.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _86_3086.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _86_3086.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _86_3086.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _86_3086.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _86_3086.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _86_3086.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _86_3086.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _86_3086.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _86_3086.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_86_3091) with
| (_86_3089, g) -> begin
(let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl))
end)))))
end
end))
end)
end))
in (let _86_3093 = g
in (let _177_1556 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _86_3093.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _86_3093.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _86_3093.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _177_1556})))))

let force_trivial_guard = (fun env g -> (let g = (let _177_1561 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _177_1561 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _177_1562 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _177_1562))
end
| (_86_3102, _86_3104, _86_3106, _86_3108, r)::_86_3100 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

let universe_inequality = (fun u1 u2 -> (let _86_3114 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _86_3114.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _86_3114.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _86_3114.FStar_TypeChecker_Env.implicits}))





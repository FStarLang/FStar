
open Prims
let new_kvar = (fun r binders -> (let u = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (let _101_7 = (let _101_6 = (let _101_5 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _101_5))
in (FStar_Absyn_Syntax.mk_Kind_uvar _101_6 r))
in (_101_7, u))))

let new_tvar = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _101_15 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _101_15 Prims.op_Negation)))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _36_47 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _101_16 = (FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_101_16, uv)))))
end))))

let new_evar = (fun r binders t -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _101_24 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _101_24 Prims.op_Negation)))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _36_60 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _101_26 = (let _101_25 = (FStar_Absyn_Syntax.mk_Total t)
in (binders, _101_25))
in (FStar_Absyn_Syntax.mk_Typ_fun _101_26 None r))
in (let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _36_66 -> begin
(let _101_27 = (FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_101_27, uv))
end))))
end))))

type rel =
| EQ
| SUB
| SUBINV

let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ -> begin
true
end
| _ -> begin
false
end))

let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB -> begin
true
end
| _ -> begin
false
end))

let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV -> begin
true
end
| _ -> begin
false
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

type ('a, 'b) problem =
{lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); scope : FStar_Absyn_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

let is_Mkproblem = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem")))

type ('a, 'b) problem_t =
('a, 'b) problem

type prob =
| KProb of (FStar_Absyn_Syntax.knd, Prims.unit) problem
| TProb of (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem
| EProb of (FStar_Absyn_Syntax.exp, Prims.unit) problem
| CProb of (FStar_Absyn_Syntax.comp, Prims.unit) problem

let is_KProb = (fun _discr_ -> (match (_discr_) with
| KProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_EProb = (fun _discr_ -> (match (_discr_) with
| EProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

let ___KProb____0 = (fun projectee -> (match (projectee) with
| KProb (_36_83) -> begin
_36_83
end))

let ___TProb____0 = (fun projectee -> (match (projectee) with
| TProb (_36_86) -> begin
_36_86
end))

let ___EProb____0 = (fun projectee -> (match (projectee) with
| EProb (_36_89) -> begin
_36_89
end))

let ___CProb____0 = (fun projectee -> (match (projectee) with
| CProb (_36_92) -> begin
_36_92
end))

type probs =
prob Prims.list

type uvi =
| UK of (FStar_Absyn_Syntax.uvar_k * FStar_Absyn_Syntax.knd)
| UT of ((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.typ)
| UE of ((FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.exp)

let is_UK = (fun _discr_ -> (match (_discr_) with
| UK (_) -> begin
true
end
| _ -> begin
false
end))

let is_UT = (fun _discr_ -> (match (_discr_) with
| UT (_) -> begin
true
end
| _ -> begin
false
end))

let is_UE = (fun _discr_ -> (match (_discr_) with
| UE (_) -> begin
true
end
| _ -> begin
false
end))

let ___UK____0 = (fun projectee -> (match (projectee) with
| UK (_36_95) -> begin
_36_95
end))

let ___UT____0 = (fun projectee -> (match (projectee) with
| UT (_36_98) -> begin
_36_98
end))

let ___UE____0 = (fun projectee -> (match (projectee) with
| UE (_36_101) -> begin
_36_101
end))

type worklist =
{attempting : probs; wl_deferred : (Prims.int * Prims.string * prob) Prims.list; subst : uvi Prims.list; ctr : Prims.int; slack_vars : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_Tc_Env.env}

let is_Mkworklist = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist")))

type deferred =
{carry : (Prims.string * prob) Prims.list; slack : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list}

let is_Mkdeferred = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdeferred")))

let no_deferred = {carry = []; slack = []}

type solution =
| Success of (uvi Prims.list * deferred)
| Failed of (prob * Prims.string)

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
| Success (_36_116) -> begin
_36_116
end))

let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_36_119) -> begin
_36_119
end))

let rel_to_string = (fun _36_1 -> (match (_36_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string = (fun env _36_2 -> (match (_36_2) with
| KProb (p) -> begin
(let _101_229 = (FStar_Absyn_Print.kind_to_string p.lhs)
in (let _101_228 = (FStar_Absyn_Print.kind_to_string p.rhs)
in (FStar_Util.format3 "\t%s\n\t\t%s\n\t%s" _101_229 (rel_to_string p.relation) _101_228)))
end
| TProb (p) -> begin
(let _101_242 = (let _101_241 = (FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _101_240 = (let _101_239 = (FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _101_238 = (let _101_237 = (let _101_236 = (FStar_All.pipe_right p.reason FStar_List.hd)
in (let _101_235 = (let _101_234 = (FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _101_233 = (let _101_232 = (FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _101_231 = (let _101_230 = (FStar_Tc_Normalize.formula_norm_to_string env (Prims.fst p.logical_guard))
in (_101_230)::[])
in (_101_232)::_101_231))
in (_101_234)::_101_233))
in (_101_236)::_101_235))
in ((rel_to_string p.relation))::_101_237)
in (_101_239)::_101_238))
in (_101_241)::_101_240))
in (FStar_Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _101_242))
end
| EProb (p) -> begin
(let _101_244 = (FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _101_243 = (FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _101_244 (rel_to_string p.relation) _101_243)))
end
| CProb (p) -> begin
(let _101_246 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _101_245 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _101_246 (rel_to_string p.relation) _101_245)))
end))

let uvi_to_string = (fun env uvi -> (let str = (fun u -> (match ((FStar_ST.read FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _101_252 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _101_252 FStar_Util.string_of_int))
end))
in (match (uvi) with
| UK (u, _36_141) -> begin
(let _101_253 = (str u)
in (FStar_All.pipe_right _101_253 (FStar_Util.format1 "UK %s")))
end
| UT ((u, _36_146), t) -> begin
(let _101_256 = (str u)
in (FStar_All.pipe_right _101_256 (fun x -> (let _101_255 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "UT %s %s" x _101_255)))))
end
| UE ((u, _36_154), _36_157) -> begin
(let _101_257 = (str u)
in (FStar_All.pipe_right _101_257 (FStar_Util.format1 "UE %s")))
end)))

let invert_rel = (fun _36_3 -> (match (_36_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun p -> (let _36_165 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _36_165.element; logical_guard = _36_165.logical_guard; scope = _36_165.scope; reason = _36_165.reason; loc = _36_165.loc; rank = _36_165.rank}))

let maybe_invert = (fun p -> (match ((p.relation = SUBINV)) with
| true -> begin
(invert p)
end
| false -> begin
p
end))

let maybe_invert_p = (fun _36_4 -> (match (_36_4) with
| KProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _101_264 -> KProb (_101_264)))
end
| TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _101_265 -> TProb (_101_265)))
end
| EProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _101_266 -> EProb (_101_266)))
end
| CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _101_267 -> CProb (_101_267)))
end))

let vary_rel = (fun rel _36_5 -> (match (_36_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel = (fun _36_6 -> (match (_36_6) with
| KProb (p) -> begin
p.relation
end
| TProb (p) -> begin
p.relation
end
| EProb (p) -> begin
p.relation
end
| CProb (p) -> begin
p.relation
end))

let p_reason = (fun _36_7 -> (match (_36_7) with
| KProb (p) -> begin
p.reason
end
| TProb (p) -> begin
p.reason
end
| EProb (p) -> begin
p.reason
end
| CProb (p) -> begin
p.reason
end))

let p_loc = (fun _36_8 -> (match (_36_8) with
| KProb (p) -> begin
p.loc
end
| TProb (p) -> begin
p.loc
end
| EProb (p) -> begin
p.loc
end
| CProb (p) -> begin
p.loc
end))

let p_context = (fun _36_9 -> (match (_36_9) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_guard = (fun _36_10 -> (match (_36_10) with
| KProb (p) -> begin
p.logical_guard
end
| TProb (p) -> begin
p.logical_guard
end
| EProb (p) -> begin
p.logical_guard
end
| CProb (p) -> begin
p.logical_guard
end))

let p_scope = (fun _36_11 -> (match (_36_11) with
| KProb (p) -> begin
p.scope
end
| TProb (p) -> begin
p.scope
end
| EProb (p) -> begin
p.scope
end
| CProb (p) -> begin
p.scope
end))

let p_invert = (fun _36_12 -> (match (_36_12) with
| KProb (p) -> begin
(FStar_All.pipe_left (fun _101_286 -> KProb (_101_286)) (invert p))
end
| TProb (p) -> begin
(FStar_All.pipe_left (fun _101_287 -> TProb (_101_287)) (invert p))
end
| EProb (p) -> begin
(FStar_All.pipe_left (fun _101_288 -> EProb (_101_288)) (invert p))
end
| CProb (p) -> begin
(FStar_All.pipe_left (fun _101_289 -> CProb (_101_289)) (invert p))
end))

let is_top_level_prob = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _101_299 = (new_tvar (p_loc orig) scope FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _101_299; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun env lhs rel rhs elt loc reason -> (let _101_309 = (let _101_308 = (FStar_Tc_Env.get_range env)
in (let _101_307 = (FStar_Tc_Env.binders env)
in (new_tvar _101_308 _101_307 FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _101_309; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun orig lhs rel rhs elt reason -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun problem x phi -> (match (problem.element) with
| None -> begin
(let _101_320 = (let _101_319 = (FStar_Absyn_Syntax.v_binder x)
in (_101_319)::[])
in (FStar_Absyn_Util.close_forall _101_320 phi))
end
| Some (e) -> begin
(FStar_Absyn_Util.subst_typ ((FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::[]) phi)
end))

let solve_prob' = (fun resolve_ok prob logical_guard uvis wl -> (let phi = (match (logical_guard) with
| None -> begin
FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _36_284 = (p_guard prob)
in (match (_36_284) with
| (_36_282, uv) -> begin
(let _36_292 = (match ((let _101_331 = (FStar_Absyn_Util.compress_typ uv)
in _101_331.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uvar, k) -> begin
(let phi = (FStar_Absyn_Util.close_for_kind phi k)
in (FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _36_291 -> begin
(match ((not (resolve_ok))) with
| true -> begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end
| false -> begin
()
end)
end)
in (match (uvis) with
| [] -> begin
wl
end
| _36_296 -> begin
(let _36_297 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug wl.tcenv) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_333 = (let _101_332 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _101_332 (FStar_String.concat ", ")))
in (FStar_Util.fprint1 "Extending solution: %s\n" _101_333))
end
| false -> begin
()
end)
in (let _36_299 = wl
in {attempting = _36_299.attempting; wl_deferred = _36_299.wl_deferred; subst = (FStar_List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _36_299.slack_vars; defer_ok = _36_299.defer_ok; smt_ok = _36_299.smt_ok; tcenv = _36_299.tcenv}))
end))
end))))

let extend_solution = (fun sol wl -> (let _36_303 = wl
in {attempting = _36_303.attempting; wl_deferred = _36_303.wl_deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _36_303.slack_vars; defer_ok = _36_303.defer_ok; smt_ok = _36_303.smt_ok; tcenv = _36_303.tcenv}))

let solve_prob = (fun prob logical_guard uvis wl -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun env d s -> (let _101_354 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _101_353 = (prob_to_string env d)
in (let _101_352 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _101_354 _101_353 _101_352 s)))))

let empty_worklist = (fun env -> {attempting = []; wl_deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun env prob -> (let _36_315 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _36_315.wl_deferred; subst = _36_315.subst; ctr = _36_315.ctr; slack_vars = _36_315.slack_vars; defer_ok = _36_315.defer_ok; smt_ok = _36_315.smt_ok; tcenv = _36_315.tcenv}))

let wl_of_guard = (fun env g -> (let _36_319 = (empty_worklist env)
in (let _101_365 = (FStar_List.map Prims.snd g.carry)
in {attempting = _101_365; wl_deferred = _36_319.wl_deferred; subst = _36_319.subst; ctr = _36_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _36_319.smt_ok; tcenv = _36_319.tcenv})))

let defer = (fun reason prob wl -> (let _36_324 = wl
in {attempting = _36_324.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; subst = _36_324.subst; ctr = _36_324.ctr; slack_vars = _36_324.slack_vars; defer_ok = _36_324.defer_ok; smt_ok = _36_324.smt_ok; tcenv = _36_324.tcenv}))

let attempt = (fun probs wl -> (let _36_328 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _36_328.wl_deferred; subst = _36_328.subst; ctr = _36_328.ctr; slack_vars = _36_328.slack_vars; defer_ok = _36_328.defer_ok; smt_ok = _36_328.smt_ok; tcenv = _36_328.tcenv}))

let add_slack_mul = (fun slack wl -> (let _36_332 = wl
in {attempting = _36_332.attempting; wl_deferred = _36_332.wl_deferred; subst = _36_332.subst; ctr = _36_332.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _36_332.defer_ok; smt_ok = _36_332.smt_ok; tcenv = _36_332.tcenv}))

let add_slack_add = (fun slack wl -> (let _36_336 = wl
in {attempting = _36_336.attempting; wl_deferred = _36_336.wl_deferred; subst = _36_336.subst; ctr = _36_336.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _36_336.defer_ok; smt_ok = _36_336.smt_ok; tcenv = _36_336.tcenv}))

let giveup = (fun env reason prob -> (let _36_341 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_390 = (prob_to_string env prob)
in (FStar_Util.fprint2 "Failed %s:\n%s\n" reason _101_390))
end
| false -> begin
()
end)
in Failed ((prob, reason))))

let commit = (fun env uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _36_13 -> (match (_36_13) with
| UK (u, k) -> begin
(FStar_Absyn_Util.unchecked_unify u k)
end
| UT ((u, k), t) -> begin
(FStar_Absyn_Util.unchecked_unify u t)
end
| UE ((u, _36_358), e) -> begin
(FStar_Absyn_Util.unchecked_unify u e)
end)))))

let find_uvar_k = (fun uv s -> (FStar_Util.find_map s (fun _36_14 -> (match (_36_14) with
| UK (u, t) -> begin
(match ((FStar_Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _36_371 -> begin
None
end))))

let find_uvar_t = (fun uv s -> (FStar_Util.find_map s (fun _36_15 -> (match (_36_15) with
| UT ((u, _36_377), t) -> begin
(match ((FStar_Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _36_383 -> begin
None
end))))

let find_uvar_e = (fun uv s -> (FStar_Util.find_map s (fun _36_16 -> (match (_36_16) with
| UE ((u, _36_389), t) -> begin
(match ((FStar_Unionfind.equivalent uv u)) with
| true -> begin
Some (t)
end
| false -> begin
None
end)
end
| _36_395 -> begin
None
end))))

let simplify_formula = (fun env f -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _101_421 = (let _101_420 = (norm_targ env t)
in (FStar_All.pipe_left (fun _101_419 -> FStar_Util.Inl (_101_419)) _101_420))
in (_101_421, (Prims.snd a)))
end
| FStar_Util.Inr (v) -> begin
(let _101_424 = (let _101_423 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env v)
in (FStar_All.pipe_left (fun _101_422 -> FStar_Util.Inr (_101_422)) _101_423))
in (_101_424, (Prims.snd a)))
end))

let whnf = (fun env t -> (let _101_429 = (FStar_Tc_Normalize.whnf env t)
in (FStar_All.pipe_right _101_429 FStar_Absyn_Util.compress_typ)))

let sn = (fun env t -> (let _101_434 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env t)
in (FStar_All.pipe_right _101_434 FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _36_17 -> (match (_36_17) with
| (FStar_Util.Inl (a), imp) -> begin
(let _101_440 = (let _101_439 = (let _36_417 = a
in (let _101_438 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _36_417.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _101_438; FStar_Absyn_Syntax.p = _36_417.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_101_439))
in (_101_440, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _101_443 = (let _101_442 = (let _36_423 = x
in (let _101_441 = (norm_targ env x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _36_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _101_441; FStar_Absyn_Syntax.p = _36_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_101_442))
in (_101_443, imp))
end)))))

let whnf_k = (fun env k -> (let _101_448 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env k)
in (FStar_All.pipe_right _101_448 FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun env e -> (let _101_453 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env e)
in (FStar_All.pipe_right _101_453 FStar_Absyn_Util.compress_exp)))

let rec compress_k = (fun env wl k -> (let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((find_uvar_k uv wl.subst)) with
| None -> begin
k
end
| Some (k') -> begin
(match (k'.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, body) -> begin
(let k = (let _101_460 = (FStar_Absyn_Util.subst_of_list formals actuals)
in (FStar_Absyn_Util.subst_kind _101_460 body))
in (compress_k env wl k))
end
| _36_446 -> begin
(match (((FStar_List.length actuals) = 0)) with
| true -> begin
(compress_k env wl k')
end
| false -> begin
(FStar_All.failwith "Wrong arity for kind unifier")
end)
end)
end)
end
| _36_448 -> begin
k
end)))

let rec compress = (fun env wl t -> (let t = (let _101_467 = (FStar_Absyn_Util.unmeta_typ t)
in (whnf env _101_467))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _36_455) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _36_471); FStar_Absyn_Syntax.tk = _36_468; FStar_Absyn_Syntax.pos = _36_466; FStar_Absyn_Syntax.fvs = _36_464; FStar_Absyn_Syntax.uvs = _36_462}, args) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _36_482 -> begin
t
end)
end
| _36_484 -> begin
t
end)))

let rec compress_e = (fun env wl e -> (let e = (FStar_Absyn_Util.unmeta_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(compress_e env wl e')
end)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _36_506); FStar_Absyn_Syntax.tk = _36_503; FStar_Absyn_Syntax.pos = _36_501; FStar_Absyn_Syntax.fvs = _36_499; FStar_Absyn_Syntax.uvs = _36_497}, args) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.FStar_Absyn_Syntax.pos))
end)
end
| _36_518 -> begin
e
end)))

let normalize_refinement = (fun env wl t0 -> (let _101_480 = (compress env wl t0)
in (FStar_Tc_Normalize.normalize_refinement env _101_480)))

let base_and_refinement = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
(match (norm) with
| true -> begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| false -> begin
(match ((normalize_refinement env wl t1)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, phi); FStar_Absyn_Syntax.tk = _36_539; FStar_Absyn_Syntax.pos = _36_537; FStar_Absyn_Syntax.fvs = _36_535; FStar_Absyn_Syntax.uvs = _36_533} -> begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _101_493 = (let _101_492 = (FStar_Absyn_Print.typ_to_string tt)
in (let _101_491 = (FStar_Absyn_Print.tag_of_typ tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _101_492 _101_491)))
in (FStar_All.failwith _101_493))
end)
end)
end
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_app (_)) -> begin
(match (norm) with
| true -> begin
(t1, None)
end
| false -> begin
(let _36_554 = (let _101_494 = (normalize_refinement env wl t1)
in (aux true _101_494))
in (match (_36_554) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _36_557 -> begin
(t2', refinement)
end)
end))
end)
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (FStar_Absyn_Syntax.Typ_ascribed (_)) | (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_meta (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _101_497 = (let _101_496 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_495 = (FStar_Absyn_Print.tag_of_typ t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _101_496 _101_495)))
in (FStar_All.failwith _101_497))
end))
in (let _101_498 = (compress env wl t1)
in (aux false _101_498))))

let unrefine = (fun env t -> (let _101_503 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _101_503 Prims.fst)))

let trivial_refinement = (fun t -> (let _101_505 = (FStar_Absyn_Util.gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in (_101_505, FStar_Absyn_Util.t_true)))

let as_refinement = (fun env wl t -> (let _36_588 = (base_and_refinement env wl t)
in (match (_36_588) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun _36_596 -> (match (_36_596) with
| (t_base, refopt) -> begin
(let _36_604 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_36_604) with
| (y, phi) -> begin
(FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun env wl uk t -> (let uvs = (FStar_Absyn_Util.uvars_in_typ t)
in (let _101_525 = (FStar_All.pipe_right uvs.FStar_Absyn_Syntax.uvars_t FStar_Util.set_elements)
in (FStar_All.pipe_right _101_525 (FStar_Util.for_some (fun _36_615 -> (match (_36_615) with
| (uvt, _36_614) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(FStar_Unionfind.equivalent uvt (Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_36_628, t); FStar_Absyn_Syntax.tk = _36_626; FStar_Absyn_Syntax.pos = _36_624; FStar_Absyn_Syntax.fvs = _36_622; FStar_Absyn_Syntax.uvs = _36_620} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))

let occurs_check = (fun env wl uk t -> (let occurs_ok = (not ((occurs env wl uk t)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _101_538 = (let _101_537 = (FStar_Absyn_Print.uvar_t_to_string uk)
in (let _101_536 = (FStar_Absyn_Print.typ_to_string t)
in (let _101_535 = (let _101_534 = (FStar_All.pipe_right wl.subst (FStar_List.map (uvi_to_string env)))
in (FStar_All.pipe_right _101_534 (FStar_String.concat ", ")))
in (FStar_Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _101_537 _101_536 _101_535))))
in Some (_101_538))
end)
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun env wl uk fvs t -> (let fvs_t = (FStar_Absyn_Util.freevars_typ t)
in (let _36_649 = (occurs_check env wl uk t)
in (match (_36_649) with
| (occurs_ok, msg) -> begin
(let _101_549 = (FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _101_549, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun env ut e -> (let uvs = (FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((FStar_Util.set_mem ut uvs.FStar_Absyn_Syntax.uvars_e)))
in (let msg = (match (occurs_ok) with
| true -> begin
None
end
| false -> begin
(let _101_561 = (let _101_560 = (FStar_Absyn_Print.uvar_e_to_string ut)
in (let _101_559 = (let _101_557 = (let _101_556 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _101_556 (FStar_List.map FStar_Absyn_Print.uvar_e_to_string)))
in (FStar_All.pipe_right _101_557 (FStar_String.concat ", ")))
in (let _101_558 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _101_560 _101_559 _101_558))))
in Some (_101_561))
end)
in (occurs_ok, msg)))))

let intersect_vars = (fun v1 v2 -> (let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _101_568 = (let _101_567 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _101_566 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _101_567; FStar_Absyn_Syntax.fxvs = _101_566}))
in (FStar_Absyn_Syntax.binders_of_freevars _101_568)))))

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun ax1 ax2 -> (match (((Prims.fst ax1), (Prims.fst ax2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Util.bvar_eq x y)
end
| _36_675 -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((FStar_All.pipe_left Prims.fst hd)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _36_687; FStar_Absyn_Syntax.pos = _36_685; FStar_Absyn_Syntax.fvs = _36_683; FStar_Absyn_Syntax.uvs = _36_681}) -> begin
(match ((FStar_All.pipe_right seen (FStar_Util.for_some (fun _36_18 -> (match (_36_18) with
| (FStar_Util.Inl (b), _36_696) -> begin
(FStar_Absyn_Syntax.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)
end
| _36_699 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((FStar_Util.Inl (a), (Prims.snd hd)))
end)
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (x); FStar_Absyn_Syntax.tk = _36_707; FStar_Absyn_Syntax.pos = _36_705; FStar_Absyn_Syntax.fvs = _36_703; FStar_Absyn_Syntax.uvs = _36_701}) -> begin
(match ((FStar_All.pipe_right seen (FStar_Util.for_some (fun _36_19 -> (match (_36_19) with
| (FStar_Util.Inr (y), _36_716) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _36_719 -> begin
false
end))))) with
| true -> begin
None
end
| false -> begin
Some ((FStar_Util.Inr (x), (Prims.snd hd)))
end)
end
| _36_721 -> begin
None
end)))

let rec pat_vars = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _36_730 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_584 = (FStar_Absyn_Print.arg_to_string hd)
in (FStar_Util.fprint1 "Not a pattern: %s\n" _101_584))
end
| false -> begin
()
end)
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

let destruct_flex_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, k); FStar_Absyn_Syntax.tk = _36_746; FStar_Absyn_Syntax.pos = _36_744; FStar_Absyn_Syntax.fvs = _36_742; FStar_Absyn_Syntax.uvs = _36_740}, args) -> begin
(t, uv, k, args)
end
| _36_756 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, k) -> begin
(e, uv, k, [])
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, k); FStar_Absyn_Syntax.tk = _36_769; FStar_Absyn_Syntax.pos = _36_767; FStar_Absyn_Syntax.fvs = _36_765; FStar_Absyn_Syntax.uvs = _36_763}, args) -> begin
(e, uv, k, args)
end
| _36_779 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun env t -> (let _36_786 = (destruct_flex_t t)
in (match (_36_786) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _36_790 -> begin
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

let head_match = (fun _36_20 -> (match (_36_20) with
| MisMatch -> begin
MisMatch
end
| _36_794 -> begin
HeadMatch
end))

let rec head_matches = (fun t1 t2 -> (match ((let _101_601 = (let _101_598 = (FStar_Absyn_Util.unmeta_typ t1)
in _101_598.FStar_Absyn_Syntax.n)
in (let _101_600 = (let _101_599 = (FStar_Absyn_Util.unmeta_typ t2)
in _101_599.FStar_Absyn_Syntax.n)
in (_101_601, _101_600)))) with
| (FStar_Absyn_Syntax.Typ_btvar (x), FStar_Absyn_Syntax.Typ_btvar (y)) -> begin
(match ((FStar_Absyn_Util.bvar_eq x y)) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
(match ((FStar_Absyn_Util.fvar_eq f g)) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), FStar_Absyn_Syntax.Typ_const (_))) | ((FStar_Absyn_Syntax.Typ_const (_), FStar_Absyn_Syntax.Typ_btvar (_))) -> begin
MisMatch
end
| (FStar_Absyn_Syntax.Typ_refine (x, _36_823), FStar_Absyn_Syntax.Typ_refine (y, _36_828)) -> begin
(let _101_602 = (head_matches x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _101_602 head_match))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _36_834), _36_838) -> begin
(let _101_603 = (head_matches x.FStar_Absyn_Syntax.sort t2)
in (FStar_All.pipe_right _101_603 head_match))
end
| (_36_841, FStar_Absyn_Syntax.Typ_refine (x, _36_844)) -> begin
(let _101_604 = (head_matches t1 x.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _101_604 head_match))
end
| (FStar_Absyn_Syntax.Typ_fun (_36_849), FStar_Absyn_Syntax.Typ_fun (_36_852)) -> begin
HeadMatch
end
| (FStar_Absyn_Syntax.Typ_app (head, _36_857), FStar_Absyn_Syntax.Typ_app (head', _36_862)) -> begin
(head_matches head head')
end
| (FStar_Absyn_Syntax.Typ_app (head, _36_868), _36_872) -> begin
(head_matches head t2)
end
| (_36_875, FStar_Absyn_Syntax.Typ_app (head, _36_878)) -> begin
(head_matches t1 head)
end
| (FStar_Absyn_Syntax.Typ_uvar (uv, _36_884), FStar_Absyn_Syntax.Typ_uvar (uv', _36_889)) -> begin
(match ((FStar_Unionfind.equivalent uv uv')) with
| true -> begin
FullMatch
end
| false -> begin
MisMatch
end)
end
| (_36_894, FStar_Absyn_Syntax.Typ_lam (_36_896)) -> begin
HeadMatch
end
| _36_900 -> begin
MisMatch
end))

let head_matches_delta = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, (match (d) with
| true -> begin
Some ((t1, t2))
end
| false -> begin
None
end)))
in (let fail = (fun _36_911 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
(match (d) with
| true -> begin
(fail ())
end
| false -> begin
(let t1 = (normalize_refinement env wl t1)
in (let t2 = (normalize_refinement env wl t2)
in (aux true t1 t2)))
end)
end
| r -> begin
(success d r t1 t2)
end))
in (aux false t1 t2)))))

let decompose_binder = (fun bs v_ktec rebuild_base -> (let fail = (fun _36_925 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let rebuild = (fun ktecs -> (let rec aux = (fun new_bs bs ktecs -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (FStar_List.rev new_bs) ktec)
end
| ((FStar_Util.Inl (a), imp)::rest, FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((FStar_Util.Inl ((let _36_947 = a
in {FStar_Absyn_Syntax.v = _36_947.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _36_947.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((FStar_Util.Inr (x), imp)::rest, FStar_Absyn_Syntax.T (t, _36_958)::rest') -> begin
(aux (((FStar_Util.Inr ((let _36_963 = x
in {FStar_Absyn_Syntax.v = _36_963.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _36_963.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _36_966 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun _36_970 _36_21 -> (match (_36_970) with
| (binders, b_ktecs) -> begin
(match (_36_21) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, v_ktec))::b_ktecs))
end
| hd::rest -> begin
(let bopt = (match ((FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
None
end
| false -> begin
Some (hd)
end)
in (let b_ktec = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(bopt, CONTRAVARIANT, FStar_Absyn_Syntax.K (a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
(bopt, CONTRAVARIANT, FStar_Absyn_Syntax.T ((x.FStar_Absyn_Syntax.sort, Some (FStar_Absyn_Syntax.ktype))))
end)
in (let binders' = (match (bopt) with
| None -> begin
binders
end
| Some (hd) -> begin
(FStar_List.append binders ((hd)::[]))
end)
in (mk_b_ktecs (binders', (b_ktec)::b_ktecs) rest))))
end)
end))
in (let _101_658 = (mk_b_ktecs ([], []) bs)
in (rebuild, _101_658))))))

let rec decompose_kind = (fun env k -> (let fail = (fun _36_989 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let k0 = k
in (let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun _36_22 -> (match (_36_22) with
| [] -> begin
k
end
| _36_997 -> begin
(fail ())
end))
in (rebuild, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(decompose_binder bs (FStar_Absyn_Syntax.K (k)) (fun bs _36_23 -> (match (_36_23) with
| FStar_Absyn_Syntax.K (k) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.FStar_Absyn_Syntax.pos)
end
| _36_1008 -> begin
(fail ())
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_36_1010, k) -> begin
(decompose_kind env k)
end
| _36_1015 -> begin
(FStar_All.failwith "Impossible")
end)))))

let rec decompose_typ = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((FStar_Util.Inl (_36_1030), imp), FStar_Absyn_Syntax.T (t, _36_1036)) -> begin
(FStar_Util.Inl (t), imp)
end
| ((FStar_Util.Inr (_36_1041), imp), FStar_Absyn_Syntax.E (e)) -> begin
(FStar_Util.Inr (e), imp)
end
| _36_1049 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (FStar_All.pipe_right args (FStar_List.map (fun _36_24 -> (match (_36_24) with
| (FStar_Util.Inl (t), _36_1055) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _36_1060) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _36_1075 = (decompose_binder bs (FStar_Absyn_Syntax.C (c)) (fun bs _36_25 -> (match (_36_25) with
| FStar_Absyn_Syntax.C (c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end
| _36_1072 -> begin
(FStar_All.failwith "Bad reconstruction")
end)))
in (match (_36_1075) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _36_1077 -> begin
(let rebuild = (fun _36_26 -> (match (_36_26) with
| [] -> begin
t
end
| _36_1081 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

let un_T = (fun _36_27 -> (match (_36_27) with
| FStar_Absyn_Syntax.T (x, _36_1087) -> begin
x
end
| _36_1091 -> begin
(FStar_All.failwith "impossible")
end))

let arg_of_ktec = (fun _36_28 -> (match (_36_28) with
| FStar_Absyn_Syntax.T (t, _36_1095) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Absyn_Syntax.E (e) -> begin
(FStar_Absyn_Syntax.varg e)
end
| _36_1101 -> begin
(FStar_All.failwith "Impossible")
end))

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_36_1114, variance, FStar_Absyn_Syntax.K (ki)) -> begin
(let _36_1121 = (new_kvar r scope)
in (match (_36_1121) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _101_741 = (let _101_740 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (FStar_All.pipe_left (fun _101_739 -> KProb (_101_739)) _101_740))
in (FStar_Absyn_Syntax.K (gi_xs), _101_741)))
end))
end
| (_36_1124, variance, FStar_Absyn_Syntax.T (ti, kopt)) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _36_1137 = (new_tvar r scope k)
in (match (_36_1137) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _101_744 = (let _101_743 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _101_742 -> TProb (_101_742)) _101_743))
in (FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _101_744)))
end)))
end
| (_36_1140, variance, FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (FStar_Tc_Recheck.recompute_typ ei)
in (let _36_1148 = (new_evar r scope t)
in (match (_36_1148) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _101_747 = (let _101_746 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (FStar_All.pipe_left (fun _101_745 -> EProb (_101_745)) _101_746))
in (FStar_Absyn_Syntax.E (gi_xs), _101_747)))
end)))
end
| (_36_1151, _36_1153, FStar_Absyn_Syntax.C (_36_1155)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _36_1231 = (match (q) with
| (bopt, variance, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Total (ti); FStar_Absyn_Syntax.tk = _36_1175; FStar_Absyn_Syntax.pos = _36_1173; FStar_Absyn_Syntax.fvs = _36_1171; FStar_Absyn_Syntax.uvs = _36_1169})) -> begin
(match ((sub_prob scope args (bopt, variance, FStar_Absyn_Syntax.T ((ti, Some (FStar_Absyn_Syntax.ktype)))))) with
| (FStar_Absyn_Syntax.T (gi_xs, _36_1183), prob) -> begin
(let _101_756 = (let _101_755 = (FStar_Absyn_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _101_754 -> FStar_Absyn_Syntax.C (_101_754)) _101_755))
in (_101_756, (prob)::[]))
end
| _36_1189 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_36_1191, _36_1193, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (c); FStar_Absyn_Syntax.tk = _36_1201; FStar_Absyn_Syntax.pos = _36_1199; FStar_Absyn_Syntax.fvs = _36_1197; FStar_Absyn_Syntax.uvs = _36_1195})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map (fun _36_29 -> (match (_36_29) with
| (FStar_Util.Inl (t), _36_1211) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _36_1216) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, FStar_Absyn_Syntax.T ((c.FStar_Absyn_Syntax.result_typ, Some (FStar_Absyn_Syntax.ktype)))))::components
in (let _36_1222 = (let _101_758 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _101_758 FStar_List.unzip))
in (match (_36_1222) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _101_763 = (let _101_762 = (let _101_759 = (FStar_List.hd ktecs)
in (FStar_All.pipe_right _101_759 un_T))
in (let _101_761 = (let _101_760 = (FStar_List.tl ktecs)
in (FStar_All.pipe_right _101_760 (FStar_List.map arg_of_ktec)))
in {FStar_Absyn_Syntax.effect_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _101_762; FStar_Absyn_Syntax.effect_args = _101_761; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _101_763))
in (FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _36_1225 -> begin
(let _36_1228 = (sub_prob scope args q)
in (match (_36_1228) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_36_1231) with
| (ktec, probs) -> begin
(let _36_1244 = (match (q) with
| (Some (b), _36_1235, _36_1237) -> begin
(let _101_765 = (let _101_764 = (FStar_Absyn_Util.arg_of_non_null_binder b)
in (_101_764)::args)
in (Some (b), (b)::scope, _101_765))
end
| _36_1240 -> begin
(None, scope, args)
end)
in (match (_36_1244) with
| (bopt, scope, args) -> begin
(let _36_1248 = (aux scope args qs)
in (match (_36_1248) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _101_768 = (let _101_767 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_101_767)
in (FStar_Absyn_Util.mk_conj_l _101_768))
end
| Some (b) -> begin
(let _101_772 = (let _101_771 = (FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _101_770 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_101_771)::_101_770))
in (FStar_Absyn_Util.mk_conj_l _101_772))
end)
in ((FStar_List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); upper : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); flag : Prims.bool FStar_ST.ref}

let is_Mkslack = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkslack")))

let fix_slack_uv = (fun _36_1261 mul -> (match (_36_1261) with
| (uv, k) -> begin
(let inst = (match (mul) with
| true -> begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_true k)
end
| false -> begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_false k)
end)
in (FStar_Absyn_Util.unchecked_unify uv inst))
end))

let fix_slack_vars = (fun slack -> (FStar_All.pipe_right slack (FStar_List.iter (fun _36_1267 -> (match (_36_1267) with
| (mul, s) -> begin
(match ((let _101_790 = (FStar_Absyn_Util.compress_typ s)
in _101_790.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(fix_slack_uv (uv, k) mul)
end
| _36_1273 -> begin
()
end)
end)))))

let fix_slack = (fun slack -> (let _36_1281 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.lower))
in (match (_36_1281) with
| (_36_1276, ul, kl, _36_1280) -> begin
(let _36_1288 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.upper))
in (match (_36_1288) with
| (_36_1283, uh, kh, _36_1287) -> begin
(let _36_1289 = (fix_slack_uv (ul, kl) false)
in (let _36_1291 = (fix_slack_uv (uh, kh) true)
in (let _36_1293 = (FStar_ST.op_Colon_Equals slack.flag true)
in (FStar_Absyn_Util.mk_conj (Prims.fst slack.lower) (Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun env slack -> (let xs = (let _101_798 = (let _101_797 = (destruct_flex_pattern env (Prims.snd slack.lower))
in (FStar_All.pipe_right _101_797 Prims.snd))
in (FStar_All.pipe_right _101_798 FStar_Util.must))
in (let _101_799 = (new_tvar (Prims.fst slack.lower).FStar_Absyn_Syntax.pos xs FStar_Absyn_Syntax.ktype)
in (_101_799, xs))))

let new_slack_formula = (fun p env wl xs low high -> (let _36_1306 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_36_1306) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _36_1310 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_36_1310) with
| (high_var, uv2) -> begin
(let wl = (add_slack_mul uv2 wl)
in (let low = (match (low) with
| None -> begin
(FStar_Absyn_Util.mk_disj FStar_Absyn_Util.t_false low_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_disj f low_var)
end)
in (let high = (match (high) with
| None -> begin
(FStar_Absyn_Util.mk_conj FStar_Absyn_Util.t_true high_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_conj f high_var)
end)
in (let _101_809 = (let _101_808 = (let _101_807 = (let _101_806 = (FStar_Util.mk_ref false)
in (low, high, _101_806))
in FStar_Absyn_Syntax.Meta_slack_formula (_101_807))
in (FStar_Absyn_Syntax.mk_Typ_meta _101_808))
in (_101_809, wl)))))
end)))
end)))

let destruct_slack = (fun env wl phi -> (let rec destruct = (fun conn_lid mk_conn phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _36_1334; FStar_Absyn_Syntax.pos = _36_1332; FStar_Absyn_Syntax.fvs = _36_1330; FStar_Absyn_Syntax.uvs = _36_1328}, (FStar_Util.Inl (lhs), _36_1346)::(FStar_Util.Inl (rhs), _36_1341)::[]) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
Some ((lhs, rhs))
end
| _36_1372 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some (rest, uvar) -> begin
(let _101_833 = (let _101_832 = (mk_conn lhs rest)
in (_101_832, uvar))
in Some (_101_833))
end)
end))
end
| _36_1379 -> begin
None
end))
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (phi1, phi2, flag)) -> begin
(match ((FStar_ST.read flag)) with
| true -> begin
(let _101_834 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_101_834))
end
| false -> begin
(let low = (let _101_835 = (compress env wl phi1)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.or_lid FStar_Absyn_Util.mk_disj) _101_835))
in (let hi = (let _101_836 = (compress env wl phi2)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.and_lid FStar_Absyn_Util.mk_disj) _101_836))
in (match ((low, hi)) with
| (None, None) -> begin
(let _36_1392 = (FStar_ST.op_Colon_Equals flag true)
in (let _101_837 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_101_837)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(FStar_All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
FStar_Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end)
end
| _36_1410 -> begin
FStar_Util.Inl (phi)
end))))

let rec eq_typ = (fun t1 t2 -> (let t1 = (FStar_Absyn_Util.compress_typ t1)
in (let t2 = (FStar_Absyn_Util.compress_typ t2)
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Typ_uvar (u1, _36_1427), FStar_Absyn_Syntax.Typ_uvar (u2, _36_1432)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Absyn_Syntax.Typ_app (h1, args1), FStar_Absyn_Syntax.Typ_app (h2, args2)) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _36_1446 -> begin
false
end))))
and eq_exp = (fun e1 e2 -> (let e1 = (FStar_Absyn_Util.compress_exp e1)
in (let e2 = (FStar_Absyn_Util.compress_exp e2)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (a), FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _36_1458), FStar_Absyn_Syntax.Exp_fvar (g, _36_1463)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Exp_constant (c), FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (FStar_Absyn_Syntax.Exp_app (h1, args1), FStar_Absyn_Syntax.Exp_app (h2, args2)) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _36_1482 -> begin
false
end))))
and eq_args = (fun a1 a2 -> (match (((FStar_List.length a1) = (FStar_List.length a2))) with
| true -> begin
(FStar_List.forall2 (fun a1 a2 -> (match ((a1, a2)) with
| ((FStar_Util.Inl (t), _36_1490), (FStar_Util.Inl (s), _36_1495)) -> begin
(eq_typ t s)
end
| ((FStar_Util.Inr (e), _36_1501), (FStar_Util.Inr (f), _36_1506)) -> begin
(eq_exp e f)
end
| _36_1510 -> begin
false
end)) a1 a2)
end
| false -> begin
false
end))

type flex_t =
(FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.args)

type im_or_proj_t =
((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.arg Prims.list * FStar_Absyn_Syntax.binders * ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ  ->  Prims.bool) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list))

let rigid_rigid = 0

let flex_rigid_eq = 1

let flex_refine_inner = 2

let flex_refine = 3

let flex_rigid = 4

let rigid_flex = 5

let refine_flex = 6

let flex_flex = 7

let compress_prob = (fun wl p -> (match (p) with
| KProb (p) -> begin
(let _101_867 = (let _36_1515 = p
in (let _101_865 = (compress_k wl.tcenv wl p.lhs)
in (let _101_864 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _101_865; relation = _36_1515.relation; rhs = _101_864; element = _36_1515.element; logical_guard = _36_1515.logical_guard; scope = _36_1515.scope; reason = _36_1515.reason; loc = _36_1515.loc; rank = _36_1515.rank})))
in (FStar_All.pipe_right _101_867 (fun _101_866 -> KProb (_101_866))))
end
| TProb (p) -> begin
(let _101_871 = (let _36_1519 = p
in (let _101_869 = (compress wl.tcenv wl p.lhs)
in (let _101_868 = (compress wl.tcenv wl p.rhs)
in {lhs = _101_869; relation = _36_1519.relation; rhs = _101_868; element = _36_1519.element; logical_guard = _36_1519.logical_guard; scope = _36_1519.scope; reason = _36_1519.reason; loc = _36_1519.loc; rank = _36_1519.rank})))
in (FStar_All.pipe_right _101_871 (fun _101_870 -> TProb (_101_870))))
end
| EProb (p) -> begin
(let _101_875 = (let _36_1523 = p
in (let _101_873 = (compress_e wl.tcenv wl p.lhs)
in (let _101_872 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _101_873; relation = _36_1523.relation; rhs = _101_872; element = _36_1523.element; logical_guard = _36_1523.logical_guard; scope = _36_1523.scope; reason = _36_1523.reason; loc = _36_1523.loc; rank = _36_1523.rank})))
in (FStar_All.pipe_right _101_875 (fun _101_874 -> EProb (_101_874))))
end
| CProb (_36_1526) -> begin
p
end))

let rank = (fun wl prob -> (let prob = (let _101_880 = (compress_prob wl prob)
in (FStar_All.pipe_right _101_880 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.FStar_Absyn_Syntax.n, kp.rhs.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_uvar (_36_1534), FStar_Absyn_Syntax.Kind_uvar (_36_1537)) -> begin
flex_flex
end
| (FStar_Absyn_Syntax.Kind_uvar (_36_1541), _36_1544) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
flex_rigid
end)
end
| (_36_1547, FStar_Absyn_Syntax.Kind_uvar (_36_1549)) -> begin
(match ((kp.relation = EQ)) with
| true -> begin
flex_rigid_eq
end
| false -> begin
rigid_flex
end)
end
| (_36_1553, _36_1555) -> begin
rigid_rigid
end)
in (let _101_882 = (FStar_All.pipe_right (let _36_1558 = kp
in {lhs = _36_1558.lhs; relation = _36_1558.relation; rhs = _36_1558.rhs; element = _36_1558.element; logical_guard = _36_1558.logical_guard; scope = _36_1558.scope; reason = _36_1558.reason; loc = _36_1558.loc; rank = Some (rank)}) (fun _101_881 -> KProb (_101_881)))
in (rank, _101_882)))
end
| TProb (tp) -> begin
(let _36_1565 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_36_1565) with
| (lh, _36_1564) -> begin
(let _36_1569 = (FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_36_1569) with
| (rh, _36_1568) -> begin
(let _36_1625 = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_36_1571), FStar_Absyn_Syntax.Typ_uvar (_36_1574)) -> begin
(flex_flex, tp)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Absyn_Syntax.Typ_uvar (_36_1590), _36_1593) -> begin
(let _36_1597 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_36_1597) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _36_1600 -> begin
(let rank = (match ((is_top_level_prob prob)) with
| true -> begin
flex_refine
end
| false -> begin
flex_refine_inner
end)
in (let _101_884 = (let _36_1602 = tp
in (let _101_883 = (force_refinement (b, ref_opt))
in {lhs = _36_1602.lhs; relation = _36_1602.relation; rhs = _101_883; element = _36_1602.element; logical_guard = _36_1602.logical_guard; scope = _36_1602.scope; reason = _36_1602.reason; loc = _36_1602.loc; rank = _36_1602.rank}))
in (rank, _101_884)))
end)
end))
end
| (_36_1605, FStar_Absyn_Syntax.Typ_uvar (_36_1607)) -> begin
(let _36_1612 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_36_1612) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _36_1615 -> begin
(let _101_886 = (let _36_1616 = tp
in (let _101_885 = (force_refinement (b, ref_opt))
in {lhs = _101_885; relation = _36_1616.relation; rhs = _36_1616.rhs; element = _36_1616.element; logical_guard = _36_1616.logical_guard; scope = _36_1616.scope; reason = _36_1616.reason; loc = _36_1616.loc; rank = _36_1616.rank}))
in (refine_flex, _101_886))
end)
end))
end
| (_36_1619, _36_1621) -> begin
(rigid_rigid, tp)
end)
in (match (_36_1625) with
| (rank, tp) -> begin
(let _101_888 = (FStar_All.pipe_right (let _36_1626 = tp
in {lhs = _36_1626.lhs; relation = _36_1626.relation; rhs = _36_1626.rhs; element = _36_1626.element; logical_guard = _36_1626.logical_guard; scope = _36_1626.scope; reason = _36_1626.reason; loc = _36_1626.loc; rank = Some (rank)}) (fun _101_887 -> TProb (_101_887)))
in (rank, _101_888))
end))
end))
end))
end
| EProb (ep) -> begin
(let _36_1633 = (FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_36_1633) with
| (lh, _36_1632) -> begin
(let _36_1637 = (FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_36_1637) with
| (rh, _36_1636) -> begin
(let rank = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_uvar (_36_1639), FStar_Absyn_Syntax.Exp_uvar (_36_1642)) -> begin
flex_flex
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_36_1658, _36_1660) -> begin
rigid_rigid
end)
in (let _101_890 = (FStar_All.pipe_right (let _36_1663 = ep
in {lhs = _36_1663.lhs; relation = _36_1663.relation; rhs = _36_1663.rhs; element = _36_1663.element; logical_guard = _36_1663.logical_guard; scope = _36_1663.scope; reason = _36_1663.reason; loc = _36_1663.loc; rank = Some (rank)}) (fun _101_889 -> EProb (_101_889)))
in (rank, _101_890)))
end))
end))
end
| CProb (cp) -> begin
(let _101_892 = (FStar_All.pipe_right (let _36_1667 = cp
in {lhs = _36_1667.lhs; relation = _36_1667.relation; rhs = _36_1667.rhs; element = _36_1667.element; logical_guard = _36_1667.logical_guard; scope = _36_1667.scope; reason = _36_1667.reason; loc = _36_1667.loc; rank = Some (rigid_rigid)}) (fun _101_891 -> CProb (_101_891)))
in (rigid_rigid, _101_892))
end)))

let next_prob = (fun wl -> (let rec aux = (fun _36_1674 probs -> (match (_36_1674) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _36_1682 = (rank wl hd)
in (match (_36_1682) with
| (rank, hd) -> begin
(match ((rank <= flex_rigid_eq)) with
| true -> begin
(match (min) with
| None -> begin
(Some (hd), (FStar_List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (FStar_List.append out ((m)::tl)), rank)
end)
end
| false -> begin
(match ((rank < min_rank)) with
| true -> begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end
| false -> begin
(aux (min_rank, min, (hd)::out) tl)
end)
end)
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))

let is_flex_rigid = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

let rec solve_flex_rigid_join = (fun env tp wl -> (let _36_1693 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_942 = (prob_to_string env (TProb (tp)))
in (FStar_Util.fprint1 "Trying to solve by joining refinements:%s\n" _101_942))
end
| false -> begin
()
end)
in (let _36_1697 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_36_1697) with
| (u, args) -> begin
(let _36_1703 = (0, 1, 2, 3, 4)
in (match (_36_1703) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| false -> begin
i
end))
in (let base_types_match = (fun t1 t2 -> (let _36_1712 = (FStar_Absyn_Util.head_and_args t1)
in (match (_36_1712) with
| (h1, args1) -> begin
(let _36_1716 = (FStar_Absyn_Util.head_and_args t2)
in (match (_36_1716) with
| (h2, _36_1715) -> begin
(match ((h1.FStar_Absyn_Syntax.n, h2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (tc1), FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
(match ((FStar_Absyn_Syntax.lid_equals tc1.FStar_Absyn_Syntax.v tc2.FStar_Absyn_Syntax.v)) with
| true -> begin
(match (((FStar_List.length args1) = 0)) with
| true -> begin
Some ([])
end
| false -> begin
(let _101_954 = (let _101_953 = (let _101_952 = (new_problem env t1 EQ t2 None t1.FStar_Absyn_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _101_951 -> TProb (_101_951)) _101_952))
in (_101_953)::[])
in Some (_101_954))
end)
end
| false -> begin
None
end)
end
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((FStar_Absyn_Util.bvar_eq a b)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end
| _36_1728 -> begin
None
end)
end))
end)))
in (let conjoin = (fun t1 t2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_refine (x, phi1), FStar_Absyn_Syntax.Typ_refine (y, phi2)) -> begin
(let m = (base_types_match x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(let phi2 = (let _101_961 = (let _101_960 = (FStar_Absyn_Syntax.v_binder x)
in (let _101_959 = (FStar_Absyn_Syntax.v_binder y)
in (FStar_Absyn_Util.mk_subst_one_binder _101_960 _101_959)))
in (FStar_Absyn_Util.subst_typ _101_961 phi2))
in (let _101_965 = (let _101_964 = (let _101_963 = (let _101_962 = (FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _101_962))
in (FStar_Absyn_Syntax.mk_Typ_refine _101_963 (Some (FStar_Absyn_Syntax.ktype)) t1.FStar_Absyn_Syntax.pos))
in (_101_964, m))
in Some (_101_965)))
end))
end
| (_36_1747, FStar_Absyn_Syntax.Typ_refine (y, _36_1750)) -> begin
(let m = (base_types_match t1 y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _36_1760), _36_1764) -> begin
(let m = (base_types_match x.FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _36_1771 -> begin
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
in (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _36_1779) -> begin
(let _36_1804 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _36_30 -> (match (_36_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _36_1790 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_36_1790) with
| (u', _36_1789) -> begin
(match ((let _101_967 = (compress env wl u')
in _101_967.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv', _36_1793) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _36_1797 -> begin
false
end)
end))
end
| _36_1799 -> begin
false
end)
end
| _36_1801 -> begin
false
end))))
in (match (_36_1804) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _36_1808 tps -> (match (_36_1808) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _101_972 = (compress env wl hd.rhs)
in (conjoin bound _101_972))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _36_1821 -> begin
None
end)
end))
in (match ((let _101_974 = (let _101_973 = (compress env wl tp.rhs)
in (_101_973, []))
in (make_upper_bound _101_974 upper_bounds))) with
| None -> begin
(let _36_1823 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(FStar_Util.print_string "No upper bounds\n")
end
| false -> begin
()
end)
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (let _36_1830 = wl
in {attempting = sub_probs; wl_deferred = _36_1830.wl_deferred; subst = _36_1830.subst; ctr = _36_1830.ctr; slack_vars = _36_1830.slack_vars; defer_ok = _36_1830.defer_ok; smt_ok = _36_1830.smt_ok; tcenv = _36_1830.tcenv}))) with
| Success (subst, _36_1834) -> begin
(let wl = (let _36_1837 = wl
in {attempting = rest; wl_deferred = _36_1837.wl_deferred; subst = []; ctr = _36_1837.ctr; slack_vars = _36_1837.slack_vars; defer_ok = _36_1837.defer_ok; smt_ok = _36_1837.smt_ok; tcenv = _36_1837.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _36_1843 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _36_1846 -> begin
None
end))
end))
end))
end
| _36_1848 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve = (fun env probs -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _36_1856 = probs
in {attempting = tl; wl_deferred = _36_1856.wl_deferred; subst = _36_1856.subst; ctr = _36_1856.ctr; slack_vars = _36_1856.slack_vars; defer_ok = _36_1856.defer_ok; smt_ok = _36_1856.smt_ok; tcenv = _36_1856.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
(match (((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) && (not ((FStar_ST.read FStar_Options.no_slack))))) with
| true -> begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end
| false -> begin
(solve_t' env (maybe_invert tp) probs)
end)
end
| EProb (ep) -> begin
(solve_e' env (maybe_invert ep) probs)
end
| CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end))
end
| (None, _36_1872, _36_1874) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _36_1878 -> begin
(let _36_1887 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _36_1884 -> (match (_36_1884) with
| (c, _36_1881, _36_1883) -> begin
(c < probs.ctr)
end))))
in (match (_36_1887) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _101_983 = (let _101_982 = (let _101_981 = (FStar_List.map (fun _36_1893 -> (match (_36_1893) with
| (_36_1890, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in {carry = _101_981; slack = probs.slack_vars})
in (probs.subst, _101_982))
in Success (_101_983))
end
| _36_1895 -> begin
(let _101_986 = (let _36_1896 = probs
in (let _101_985 = (FStar_All.pipe_right attempt (FStar_List.map (fun _36_1903 -> (match (_36_1903) with
| (_36_1899, _36_1901, y) -> begin
y
end))))
in {attempting = _101_985; wl_deferred = rest; subst = _36_1896.subst; ctr = _36_1896.ctr; slack_vars = _36_1896.slack_vars; defer_ok = _36_1896.defer_ok; smt_ok = _36_1896.smt_ok; tcenv = _36_1896.tcenv}))
in (solve env _101_986))
end)
end))
end)
end))
and solve_binders = (fun env bs1 bs2 orig wl rhs -> (let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs scope env subst)
in (let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula))))
end
| (((FStar_Util.Inl (_), _)::_, (FStar_Util.Inr (_), _)::_)) | (((FStar_Util.Inr (_), _)::_, (FStar_Util.Inl (_), _)::_)) -> begin
FStar_Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(let subst = (let _101_1012 = (FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (FStar_List.append _101_1012 subst))
in (let env = (let _101_1013 = (FStar_Tc_Env.binding_of_binder hd2)
in (FStar_Tc_Env.push_local_binding env _101_1013))
in (let prob = (match (((Prims.fst hd1), (Prims.fst hd2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _101_1017 = (let _101_1016 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _101_1015 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _101_1016 _101_1015 b.FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (FStar_All.pipe_left (fun _101_1014 -> KProb (_101_1014)) _101_1017))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _101_1021 = (let _101_1020 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _101_1019 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _101_1020 _101_1019 y.FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (FStar_All.pipe_left (fun _101_1018 -> TProb (_101_1018)) _101_1021))
end
| _36_1979 -> begin
(FStar_All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| FStar_Util.Inr (msg) -> begin
FStar_Util.Inr (msg)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _101_1023 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _101_1022 = (FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (FStar_Absyn_Util.mk_conj _101_1023 _101_1022)))
in FStar_Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _36_1989 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (let scope = (FStar_Tc_Env.binders env)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_k = (fun env problem wl -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _36_2004 -> begin
(FStar_All.failwith "impossible")
end))
and solve_k' = (fun env problem wl -> (let orig = KProb (problem)
in (match ((FStar_Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _101_1030 = (solve_prob orig None [] wl)
in (solve env _101_1030))
end
| false -> begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in (match ((FStar_Util.physical_equality k1 k2)) with
| true -> begin
(let _101_1031 = (solve_prob orig None [] wl)
in (solve env _101_1031))
end
| false -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let imitate_k = (fun _36_2020 -> (match (_36_2020) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let _36_2025 = (imitation_sub_probs orig env xs ps qs)
in (match (_36_2025) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _101_1047 = (let _101_1046 = (h gs_xs)
in (xs, _101_1046))
in (FStar_Absyn_Syntax.mk_Kind_lam _101_1047 r))
in (let wl = (solve_prob orig (Some (f)) ((UK ((u, im)))::[]) wl)
in (solve env (attempt sub_probs wl))))
end)))
end))
in (let flex_rigid = (fun rel u args k -> (let maybe_vars1 = (pat_vars env [] args)
in (match (maybe_vars1) with
| Some (xs) -> begin
(let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (FStar_Absyn_Util.freevars_kind k2)
in (let uvs2 = (FStar_Absyn_Util.uvars_in_kind k2)
in (match ((((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && (not ((FStar_Util.set_mem u uvs2.FStar_Absyn_Syntax.uvars_k))))) with
| true -> begin
(let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (let _101_1056 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _101_1056)))
end
| false -> begin
(let _101_1061 = (let _101_1060 = (FStar_All.pipe_right xs FStar_Absyn_Util.args_of_non_null_binders)
in (let _101_1059 = (decompose_kind env k)
in (rel, u, _101_1060, xs, _101_1059)))
in (imitate_k _101_1061))
end))))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.FStar_Absyn_Syntax.n, k2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Kind_type, FStar_Absyn_Syntax.Kind_type)) | ((FStar_Absyn_Syntax.Kind_effect, FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _101_1062 = (solve_prob orig None [] wl)
in (FStar_All.pipe_left (solve env) _101_1062))
end
| (FStar_Absyn_Syntax.Kind_abbrev (_36_2048, k1), _36_2053) -> begin
(solve_k env (let _36_2055 = problem
in {lhs = k1; relation = _36_2055.relation; rhs = _36_2055.rhs; element = _36_2055.element; logical_guard = _36_2055.logical_guard; scope = _36_2055.scope; reason = _36_2055.reason; loc = _36_2055.loc; rank = _36_2055.rank}) wl)
end
| (_36_2058, FStar_Absyn_Syntax.Kind_abbrev (_36_2060, k2)) -> begin
(solve_k env (let _36_2065 = problem
in {lhs = _36_2065.lhs; relation = _36_2065.relation; rhs = k2; element = _36_2065.element; logical_guard = _36_2065.logical_guard; scope = _36_2065.scope; reason = _36_2065.reason; loc = _36_2065.loc; rank = _36_2065.rank}) wl)
end
| (FStar_Absyn_Syntax.Kind_arrow (bs1, k1'), FStar_Absyn_Syntax.Kind_arrow (bs2, k2')) -> begin
(let sub_prob = (fun scope env subst -> (let _101_1071 = (let _101_1070 = (FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _101_1070 problem.relation k2' None "Arrow-kind result"))
in (FStar_All.pipe_left (fun _101_1069 -> KProb (_101_1069)) _101_1071)))
in (solve_binders env bs1 bs2 orig wl sub_prob))
end
| (FStar_Absyn_Syntax.Kind_uvar (u1, args1), FStar_Absyn_Syntax.Kind_uvar (u2, args2)) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(giveup env "flex-flex: non patterns" (KProb (problem)))
end
| (Some (xs), Some (ys)) -> begin
(match (((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let _36_2108 = (new_kvar r zs)
in (match (_36_2108) with
| (u, _36_2107) -> begin
(let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end)
end)))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, args), _36_2117) -> begin
(flex_rigid problem.relation u args k2)
end
| (_36_2120, FStar_Absyn_Syntax.Kind_uvar (u, args)) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, FStar_Absyn_Syntax.Kind_unknown)) -> begin
(FStar_All.failwith "Impossible")
end
| _36_2147 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end)))
end)))
and solve_t = (fun env problem wl -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _36_2155 -> begin
(FStar_All.failwith "Impossible")
end)))
and solve_t' = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> (match (wl.defer_ok) with
| true -> begin
(let _36_2162 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1082 = (prob_to_string env orig)
in (FStar_Util.fprint2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _101_1082 msg))
end
| false -> begin
()
end)
in (solve env (defer msg orig wl)))
end
| false -> begin
(giveup env msg orig)
end))
in (let imitate_t = (fun orig env wl p -> (let _36_2179 = p
in (match (_36_2179) with
| ((u, k), ps, xs, (h, _36_2176, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_Tc_Env.get_range env)
in (let _36_2185 = (imitation_sub_probs orig env xs ps qs)
in (match (_36_2185) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _101_1094 = (let _101_1093 = (h gs_xs)
in (xs, _101_1093))
in (FStar_Absyn_Syntax.mk_Typ_lam' _101_1094 None r))
in (let _36_2187 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1099 = (FStar_Absyn_Print.typ_to_string im)
in (let _101_1098 = (FStar_Absyn_Print.tag_of_typ im)
in (let _101_1097 = (let _101_1095 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _101_1095 (FStar_String.concat ", ")))
in (let _101_1096 = (FStar_Tc_Normalize.formula_norm_to_string env formula)
in (FStar_Util.fprint4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _101_1099 _101_1098 _101_1097 _101_1096)))))
end
| false -> begin
()
end)
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun orig env wl i p -> (let _36_2203 = p
in (match (_36_2203) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let pi = (FStar_List.nth ps i)
in (let rec gs = (fun k -> (let _36_2210 = (FStar_Absyn_Util.kind_formals k)
in (match (_36_2210) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _36_2239 = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let k_a = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _36_2223 = (new_tvar r xs k_a)
in (match (_36_2223) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_Tc_Normalize.eta_expand env gi_xs)
in (let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app (gi, ps) (Some (k_a)) r)
in (let subst = (match ((FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
subst
end
| false -> begin
(FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, gi_xs)))::subst
end)
in (let _101_1119 = (FStar_Absyn_Syntax.targ gi_xs)
in (let _101_1118 = (FStar_Absyn_Syntax.targ gi_ps)
in (_101_1119, _101_1118, subst))))))
end)))
end
| FStar_Util.Inr (x) -> begin
(let t_x = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _36_2232 = (new_evar r xs t_x)
in (match (_36_2232) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app (gi, ps) (Some (t_x)) r)
in (let subst = (match ((FStar_Absyn_Syntax.is_null_binder hd)) with
| true -> begin
subst
end
| false -> begin
(FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, gi_xs)))::subst
end)
in (let _101_1121 = (FStar_Absyn_Syntax.varg gi_xs)
in (let _101_1120 = (FStar_Absyn_Syntax.varg gi_ps)
in (_101_1121, _101_1120, subst))))))
end)))
end)
in (match (_36_2239) with
| (gi_xs, gi_ps, subst) -> begin
(let _36_2242 = (aux subst tl)
in (match (_36_2242) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _101_1123 = (let _101_1122 = (FStar_List.nth xs i)
in (FStar_All.pipe_left Prims.fst _101_1122))
in ((Prims.fst pi), _101_1123))) with
| (FStar_Util.Inl (pi), FStar_Util.Inl (xi)) -> begin
(match ((let _101_1124 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _101_1124))) with
| true -> begin
None
end
| false -> begin
(let _36_2251 = (gs xi.FStar_Absyn_Syntax.sort)
in (match (_36_2251) with
| (g_xs, _36_2250) -> begin
(let xi = (FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _101_1126 = (let _101_1125 = (FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (FStar_Absyn_Syntax.ktype)) r)
in (xs, _101_1125))
in (FStar_Absyn_Syntax.mk_Typ_lam _101_1126 None r))
in (let sub = (let _101_1132 = (let _101_1131 = (FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (FStar_Absyn_Syntax.ktype)) r)
in (let _101_1130 = (let _101_1129 = (FStar_List.map (fun _36_2259 -> (match (_36_2259) with
| (_36_2255, _36_2257, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _101_1129))
in (mk_problem (p_scope orig) orig _101_1131 (p_rel orig) _101_1130 None "projection")))
in (FStar_All.pipe_left (fun _101_1127 -> TProb (_101_1127)) _101_1132))
in (let _36_2261 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1134 = (FStar_Absyn_Print.typ_to_string proj)
in (let _101_1133 = (prob_to_string env sub)
in (FStar_Util.fprint2 "Projecting %s\n\tsubprob=%s\n" _101_1134 _101_1133)))
end
| false -> begin
()
end)
in (let wl = (let _101_1136 = (let _101_1135 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_101_1135))
in (solve_prob orig _101_1136 ((UT ((u, proj)))::[]) wl))
in (let _101_1138 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _101_1137 -> Some (_101_1137)) _101_1138)))))))
end))
end)
end
| _36_2265 -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _36_2277 = lhs
in (match (_36_2277) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _101_1165 = (FStar_Absyn_Util.kind_formals k)
in (FStar_All.pipe_right _101_1165 Prims.fst))
in (let xs = (FStar_Absyn_Util.name_binders xs)
in (let _101_1170 = (decompose_typ env t2)
in ((uv, k), ps, xs, _101_1170)))))
in (let rec imitate_or_project = (fun n st i -> (match ((i >= n)) with
| true -> begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end
| false -> begin
(match ((i = (- (1)))) with
| true -> begin
(match ((imitate_t orig env wl st)) with
| Failed (_36_2287) -> begin
(imitate_or_project n st (i + 1))
end
| sol -> begin
sol
end)
end
| false -> begin
(match ((project_t orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(imitate_or_project n st (i + 1))
end
| Some (sol) -> begin
sol
end)
end)
end))
in (let check_head = (fun fvs1 t2 -> (let _36_2303 = (FStar_Absyn_Util.head_and_args t2)
in (match (_36_2303) with
| (hd, _36_2302) -> begin
(match (hd.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _36_2314 -> begin
(let fvs_hd = (FStar_Absyn_Util.freevars_typ hd)
in (match ((FStar_Absyn_Util.fvs_included fvs_hd fvs1)) with
| true -> begin
true
end
| false -> begin
(let _36_2316 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1181 = (FStar_Absyn_Print.freevars_to_string fvs_hd)
in (FStar_Util.fprint1 "Free variables are %s" _101_1181))
end
| false -> begin
()
end)
in false)
end))
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _101_1185 = (let _101_1184 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _101_1184 Prims.fst))
in (FStar_All.pipe_right _101_1185 FStar_Absyn_Util.freevars_typ))
in (match ((FStar_Util.set_is_empty fvs_hd.FStar_Absyn_Syntax.ftvs)) with
| true -> begin
(- (1))
end
| false -> begin
0
end)))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (FStar_Absyn_Util.freevars_typ t1)
in (let fvs2 = (FStar_Absyn_Util.freevars_typ t2)
in (let _36_2329 = (occurs_check env wl (uv, k) t2)
in (match (_36_2329) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(let _101_1187 = (let _101_1186 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _101_1186))
in (giveup_or_defer orig _101_1187))
end
| false -> begin
(match ((FStar_Absyn_Util.fvs_included fvs2 fvs1)) with
| true -> begin
(match (((FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ))) with
| true -> begin
(let _101_1188 = (subterms args_lhs)
in (imitate_t orig env wl _101_1188))
end
| false -> begin
(let _36_2330 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1191 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1190 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _101_1189 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.fprint3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _101_1191 _101_1190 _101_1189))))
end
| false -> begin
()
end)
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _36_2334 -> begin
(let _101_1193 = (let _101_1192 = (sn_binders env vars)
in (_101_1192, t2))
in (FStar_Absyn_Syntax.mk_Typ_lam _101_1193 None t1.FStar_Absyn_Syntax.pos))
end)
in (let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end)
end
| false -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end
| false -> begin
(match ((check_head fvs1 t2)) with
| true -> begin
(let _36_2337 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1196 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1195 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _101_1194 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.fprint3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _101_1196 _101_1195 _101_1194))))
end
| false -> begin
()
end)
in (let _101_1197 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _101_1197 (- (1)))))
end
| false -> begin
(giveup env "free-variable check failed on a non-redex" orig)
end)
end)
end)
end)
end))))))
end
| None -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "not a pattern" orig wl))
end
| false -> begin
(match ((let _101_1198 = (FStar_Absyn_Util.freevars_typ t1)
in (check_head _101_1198 t2))) with
| true -> begin
(let im_ok = (imitate_ok t2)
in (let _36_2341 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1199 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.fprint2 "Not a pattern (%s) ... %s\n" _101_1199 (match ((im_ok < 0)) with
| true -> begin
"imitating"
end
| false -> begin
"projecting"
end)))
end
| false -> begin
()
end)
in (let _101_1200 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _101_1200 im_ok))))
end
| false -> begin
(giveup env "head-symbol is free" orig)
end)
end)
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> (match ((wl.defer_ok && ((p_rel orig) <> EQ))) with
| true -> begin
(solve env (defer "flex-flex deferred" orig wl))
end
| false -> begin
(let force_quasi_pattern = (fun xs_opt _36_2353 -> (match (_36_2353) with
| (t, u, k, args) -> begin
(let rec aux = (fun binders ys args -> (match (args) with
| [] -> begin
(let ys = (FStar_List.rev ys)
in (let binders = (FStar_List.rev binders)
in (let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _36_2365 = (new_tvar t.FStar_Absyn_Syntax.pos ys kk)
in (match (_36_2365) with
| (t', _36_2364) -> begin
(let _36_2371 = (destruct_flex_t t')
in (match (_36_2371) with
| (u1_ys, u1, k1, _36_2370) -> begin
(let sol = (let _101_1218 = (let _101_1217 = (FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((u, k), _101_1217))
in UT (_101_1218))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun hd -> (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let _101_1222 = (let _101_1221 = (FStar_Tc_Recheck.recompute_kind a)
in (FStar_All.pipe_right _101_1221 (FStar_Absyn_Util.gen_bvar_p a.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _101_1222 FStar_Absyn_Syntax.t_binder))
end
| FStar_Util.Inr (x) -> begin
(let _101_1224 = (let _101_1223 = (FStar_Tc_Recheck.recompute_typ x)
in (FStar_All.pipe_right _101_1223 (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _101_1224 FStar_Absyn_Syntax.v_binder))
end))
in (let _36_2390 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _101_1225 = (new_binder hd)
in (_101_1225, ys))
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
(y, (y)::ys)
end
| Some (xs) -> begin
(match ((FStar_All.pipe_right xs (FStar_Util.for_some (FStar_Absyn_Util.eq_binder y)))) with
| true -> begin
(y, (y)::ys)
end
| false -> begin
(let _101_1226 = (new_binder hd)
in (_101_1226, ys))
end)
end)
end)
in (match (_36_2390) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun wl _36_2396 _36_2400 k r -> (match ((_36_2396, _36_2400)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
(match (((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(let _101_1237 = (solve_prob orig None [] wl)
in (solve env _101_1237))
end
| false -> begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _36_2409 = (new_tvar r zs k)
in (match (_36_2409) with
| (u_zs, _36_2408) -> begin
(let sub1 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _36_2413 = (occurs_check env wl (u1, k1) sub1)
in (match (_36_2413) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end
| false -> begin
(let sol1 = UT (((u1, k1), sub1))
in (match ((FStar_Unionfind.equivalent u1 u2)) with
| true -> begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end
| false -> begin
(let sub2 = (FStar_Absyn_Syntax.mk_Typ_lam' (ys, u_zs) (Some (k2)) r)
in (let _36_2419 = (occurs_check env wl (u2, k2) sub2)
in (match (_36_2419) with
| (occurs_ok, msg) -> begin
(match ((not (occurs_ok))) with
| true -> begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end
| false -> begin
(let sol2 = UT (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end)
end)))
end))
end)
end)))
end)))))
end)
end))
in (let solve_one_pat = (fun _36_2427 _36_2432 -> (match ((_36_2427, _36_2432)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _36_2433 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1243 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1242 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.fprint2 "Trying flex-flex one pattern (%s) with %s\n" _101_1243 _101_1242)))
end
| false -> begin
()
end)
in (match ((FStar_Unionfind.equivalent u1 u2)) with
| true -> begin
(let sub_probs = (FStar_List.map2 (fun a b -> (let a = (FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Prims.fst a), (Prims.fst b))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _101_1247 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _101_1247 (fun _101_1246 -> TProb (_101_1246))))
end
| (FStar_Util.Inr (t1), FStar_Util.Inr (t2)) -> begin
(let _101_1249 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _101_1249 (fun _101_1248 -> EProb (_101_1248))))
end
| _36_2449 -> begin
(FStar_All.failwith "Impossible")
end))) xs args2)
in (let guard = (let _101_1251 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _101_1251))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end
| false -> begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Absyn_Util.freevars_typ t2)
in (let _36_2459 = (occurs_check env wl (u1, k1) t2)
in (match (_36_2459) with
| (occurs_ok, _36_2458) -> begin
(let lhs_vars = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (match ((occurs_ok && (FStar_Absyn_Util.fvs_included rhs_vars lhs_vars))) with
| true -> begin
(let sol = (let _101_1253 = (let _101_1252 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.FStar_Absyn_Syntax.pos)
in ((u1, k1), _101_1252))
in UT (_101_1253))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end
| false -> begin
(match ((occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok))) with
| true -> begin
(let _36_2470 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_36_2470) with
| (sol, (_36_2465, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _36_2472 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _101_1254 = (uvi_to_string env sol)
in (FStar_Util.fprint1 "flex-flex quasi pattern (2): %s\n" _101_1254))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _36_2477 -> begin
(giveup env "impossible" orig)
end)))
end))
end
| false -> begin
(giveup_or_defer orig "flex-flex constraint")
end)
end))
end))))
end))
end))
in (let _36_2482 = lhs
in (match (_36_2482) with
| (t1, u1, k1, args1) -> begin
(let _36_2487 = rhs
in (match (_36_2487) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _101_1255 = (FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _101_1255 t2.FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _36_2505 -> begin
(match (wl.defer_ok) with
| true -> begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end
| false -> begin
(let _36_2509 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_36_2509) with
| (sol, _36_2508) -> begin
(let wl = (extend_solution sol wl)
in (let _36_2511 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern")))) with
| true -> begin
(let _101_1256 = (uvi_to_string env sol)
in (FStar_Util.fprint1 "flex-flex quasi pattern (1): %s\n" _101_1256))
end
| false -> begin
()
end)
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _36_2516 -> begin
(giveup env "impossible" orig)
end)))
end))
end)
end))))
end))
end)))))
end))
in (let orig = TProb (problem)
in (match ((FStar_Util.physical_equality problem.lhs problem.rhs)) with
| true -> begin
(let _101_1257 = (solve_prob orig None [] wl)
in (solve env _101_1257))
end
| false -> begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in (match ((FStar_Util.physical_equality t1 t2)) with
| true -> begin
(let _101_1258 = (solve_prob orig None [] wl)
in (solve env _101_1258))
end
| false -> begin
(let _36_2520 = (match ((FStar_Tc_Env.debug env (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1261 = (prob_to_string env orig)
in (let _101_1260 = (let _101_1259 = (FStar_List.map (uvi_to_string wl.tcenv) wl.subst)
in (FStar_All.pipe_right _101_1259 (FStar_String.concat "; ")))
in (FStar_Util.fprint2 "Attempting %s\n\tSubst is %s\n" _101_1261 _101_1260)))
end
| false -> begin
()
end)
in (let r = (FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun _36_2525 _36_2528 -> (match ((_36_2525, _36_2528)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _36_2535 = (FStar_Util.first_N n bs)
in (match (_36_2535) with
| (bs, rest) -> begin
(let _101_1291 = (mk_cod rest)
in (bs, _101_1291))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in (match ((l1 = l2)) with
| true -> begin
(let _101_1295 = (let _101_1292 = (mk_cod1 [])
in (bs1, _101_1292))
in (let _101_1294 = (let _101_1293 = (mk_cod2 [])
in (bs2, _101_1293))
in (_101_1295, _101_1294)))
end
| false -> begin
(match ((l1 > l2)) with
| true -> begin
(let _101_1298 = (curry l2 bs1 mk_cod1)
in (let _101_1297 = (let _101_1296 = (mk_cod2 [])
in (bs2, _101_1296))
in (_101_1298, _101_1297)))
end
| false -> begin
(let _101_1301 = (let _101_1299 = (mk_cod1 [])
in (bs1, _101_1299))
in (let _101_1300 = (curry l1 bs2 mk_cod2)
in (_101_1301, _101_1300)))
end)
end))))
end))
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(match ((FStar_Absyn_Util.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)) with
| true -> begin
(let _101_1302 = (solve_prob orig None [] wl)
in (solve env _101_1302))
end
| false -> begin
(let _101_1306 = (let _101_1305 = (let _101_1304 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _101_1303 -> Some (_101_1303)) _101_1304))
in (solve_prob orig _101_1305 [] wl))
in (solve env _101_1306))
end)
end
| (FStar_Absyn_Syntax.Typ_fun (bs1, c1), FStar_Absyn_Syntax.Typ_fun (bs2, c2)) -> begin
(let mk_c = (fun c _36_31 -> (match (_36_31) with
| [] -> begin
c
end
| bs -> begin
(let _101_1311 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Total _101_1311))
end))
in (let _36_2566 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_36_2566) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Absyn_Util.subst_comp subst c1)
in (let rel = (match ((FStar_ST.read FStar_Options.use_eq_at_higher_order)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (let _36_2572 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ")))) with
| true -> begin
(let _101_1318 = (let _101_1317 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_right _101_1317 FStar_Range.string_of_range))
in (FStar_Util.fprint2 "(%s) Using relation %s at higher order\n" _101_1318 (rel_to_string rel)))
end
| false -> begin
()
end)
in (let _101_1320 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _101_1319 -> CProb (_101_1319)) _101_1320)))))))
end)))
end
| (FStar_Absyn_Syntax.Typ_lam (bs1, t1'), FStar_Absyn_Syntax.Typ_lam (bs2, t2')) -> begin
(let mk_t = (fun t _36_32 -> (match (_36_32) with
| [] -> begin
t
end
| bs -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end))
in (let _36_2594 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_36_2594) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let t1' = (FStar_Absyn_Util.subst_typ subst t1')
in (let _101_1331 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (FStar_All.pipe_left (fun _101_1330 -> TProb (_101_1330)) _101_1331)))))
end)))
end
| (FStar_Absyn_Syntax.Typ_refine (_36_2600), FStar_Absyn_Syntax.Typ_refine (_36_2603)) -> begin
(let _36_2608 = (as_refinement env wl t1)
in (match (_36_2608) with
| (x1, phi1) -> begin
(let _36_2611 = (as_refinement env wl t2)
in (match (_36_2611) with
| (x2, phi2) -> begin
(let base_prob = (let _101_1333 = (mk_problem (p_scope orig) orig x1.FStar_Absyn_Syntax.sort problem.relation x2.FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (FStar_All.pipe_left (fun _101_1332 -> TProb (_101_1332)) _101_1333))
in (let x1_for_x2 = (let _101_1335 = (FStar_Absyn_Syntax.v_binder x1)
in (let _101_1334 = (FStar_Absyn_Syntax.v_binder x2)
in (FStar_Absyn_Util.mk_subst_one_binder _101_1335 _101_1334)))
in (let phi2 = (FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun imp phi1 phi2 -> (let _101_1352 = (imp phi1 phi2)
in (FStar_All.pipe_right _101_1352 (guard_on_element problem x1))))
in (let fallback = (fun _36_2620 -> (match (()) with
| () -> begin
(let impl = (match ((problem.relation = EQ)) with
| true -> begin
(mk_imp FStar_Absyn_Util.mk_iff phi1 phi2)
end
| false -> begin
(mk_imp FStar_Absyn_Util.mk_imp phi1 phi2)
end)
in (let guard = (let _101_1355 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _101_1355 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in (match ((problem.relation = EQ)) with
| true -> begin
(let ref_prob = (let _101_1357 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _101_1356 -> TProb (_101_1356)) _101_1357))
in (match ((solve env (let _36_2625 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; subst = _36_2625.subst; ctr = _36_2625.ctr; slack_vars = _36_2625.slack_vars; defer_ok = false; smt_ok = _36_2625.smt_ok; tcenv = _36_2625.tcenv}))) with
| Failed (_36_2628) -> begin
(fallback ())
end
| Success (subst, _36_2632) -> begin
(let guard = (let _101_1360 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _101_1359 = (let _101_1358 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _101_1358 (guard_on_element problem x1)))
in (FStar_Absyn_Util.mk_conj _101_1360 _101_1359)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _36_2637 = wl
in {attempting = _36_2637.attempting; wl_deferred = _36_2637.wl_deferred; subst = subst; ctr = (wl.ctr + 1); slack_vars = _36_2637.slack_vars; defer_ok = _36_2637.defer_ok; smt_ok = _36_2637.smt_ok; tcenv = _36_2637.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end
| false -> begin
(fallback ())
end))))))
end))
end))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _101_1362 = (destruct_flex_t t1)
in (let _101_1361 = (destruct_flex_t t2)
in (flex_flex orig _101_1362 _101_1361)))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) when (problem.relation = EQ) -> begin
(let _101_1363 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _101_1363 t2 wl))
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end
| false -> begin
(let new_rel = (match ((FStar_ST.read FStar_Options.no_slack)) with
| true -> begin
EQ
end
| false -> begin
problem.relation
end)
in (match ((let _101_1364 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _101_1364))) with
| true -> begin
(let _101_1367 = (FStar_All.pipe_left (fun _101_1365 -> TProb (_101_1365)) (let _36_2796 = problem
in {lhs = _36_2796.lhs; relation = new_rel; rhs = _36_2796.rhs; element = _36_2796.element; logical_guard = _36_2796.logical_guard; scope = _36_2796.scope; reason = _36_2796.reason; loc = _36_2796.loc; rank = _36_2796.rank}))
in (let _101_1366 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _101_1367 _101_1366 t2 wl)))
end
| false -> begin
(let _36_2800 = (base_and_refinement env wl t2)
in (match (_36_2800) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _101_1370 = (FStar_All.pipe_left (fun _101_1368 -> TProb (_101_1368)) (let _36_2802 = problem
in {lhs = _36_2802.lhs; relation = new_rel; rhs = _36_2802.rhs; element = _36_2802.element; logical_guard = _36_2802.logical_guard; scope = _36_2802.scope; reason = _36_2802.reason; loc = _36_2802.loc; rank = _36_2802.rank}))
in (let _101_1369 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _101_1370 _101_1369 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _36_2808 = y
in {FStar_Absyn_Syntax.v = _36_2808.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t1; FStar_Absyn_Syntax.p = _36_2808.FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _101_1372 = (mk_problem problem.scope orig t1 new_rel y.FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _101_1371 -> TProb (_101_1371)) _101_1372))
in (let guard = (let _101_1373 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _101_1373 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end))
end)
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end
| false -> begin
(let _36_2843 = (base_and_refinement env wl t1)
in (match (_36_2843) with
| (t_base, _36_2842) -> begin
(solve_t env (let _36_2844 = problem
in {lhs = t_base; relation = EQ; rhs = _36_2844.rhs; element = _36_2844.element; logical_guard = _36_2844.logical_guard; scope = _36_2844.scope; reason = _36_2844.reason; loc = _36_2844.loc; rank = _36_2844.rank}) wl)
end))
end)
end
| (FStar_Absyn_Syntax.Typ_refine (_36_2847), _36_2850) -> begin
(let t2 = (let _101_1374 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _101_1374))
in (solve_t env (let _36_2853 = problem
in {lhs = _36_2853.lhs; relation = _36_2853.relation; rhs = t2; element = _36_2853.element; logical_guard = _36_2853.logical_guard; scope = _36_2853.scope; reason = _36_2853.reason; loc = _36_2853.loc; rank = _36_2853.rank}) wl))
end
| (_36_2856, FStar_Absyn_Syntax.Typ_refine (_36_2858)) -> begin
(let t1 = (let _101_1375 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _101_1375))
in (solve_t env (let _36_2862 = problem
in {lhs = t1; relation = _36_2862.relation; rhs = _36_2862.rhs; element = _36_2862.element; logical_guard = _36_2862.logical_guard; scope = _36_2862.scope; reason = _36_2862.reason; loc = _36_2862.loc; rank = _36_2862.rank}) wl))
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) | ((FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, FStar_Absyn_Syntax.Typ_const (_))) | ((_, FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _36_2902 = (head_matches_delta env wl t1 t2)
in (match (_36_2902) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _36_2905) -> begin
(let head1 = (let _101_1376 = (FStar_Absyn_Util.head_and_args t1)
in (FStar_All.pipe_right _101_1376 Prims.fst))
in (let head2 = (let _101_1377 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _101_1377 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_36_2912) -> begin
true
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Tc_Env.is_projector env tc.FStar_Absyn_Syntax.v)
end
| _36_2917 -> begin
false
end))
in (match ((((may_equate head1) || (may_equate head2)) && wl.smt_ok)) with
| true -> begin
(let _101_1383 = (let _101_1382 = (let _101_1381 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _101_1380 -> Some (_101_1380)) _101_1381))
in (solve_prob orig _101_1382 [] wl))
in (solve env _101_1383))
end
| false -> begin
(giveup env "head mismatch" orig)
end))))
end
| (_36_2919, Some (t1, t2)) -> begin
(solve_t env (let _36_2925 = problem
in {lhs = t1; relation = _36_2925.relation; rhs = t2; element = _36_2925.element; logical_guard = _36_2925.logical_guard; scope = _36_2925.scope; reason = _36_2925.reason; loc = _36_2925.loc; rank = _36_2925.rank}) wl)
end
| (_36_2928, None) -> begin
(let _36_2931 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1385 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1384 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.fprint2 "Head matches: %s and %s\n" _101_1385 _101_1384)))
end
| false -> begin
()
end)
in (let _36_2935 = (FStar_Absyn_Util.head_and_args t1)
in (match (_36_2935) with
| (head, args) -> begin
(let _36_2938 = (FStar_Absyn_Util.head_and_args t2)
in (match (_36_2938) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in (match ((nargs <> (FStar_List.length args'))) with
| true -> begin
(let _101_1390 = (let _101_1389 = (FStar_Absyn_Print.typ_to_string head)
in (let _101_1388 = (FStar_Absyn_Print.args_to_string args)
in (let _101_1387 = (FStar_Absyn_Print.typ_to_string head')
in (let _101_1386 = (FStar_Absyn_Print.args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _101_1389 _101_1388 _101_1387 _101_1386)))))
in (giveup env _101_1390 orig))
end
| false -> begin
(match (((nargs = 0) || (eq_args args args'))) with
| true -> begin
(let _101_1391 = (solve_prob orig None [] wl)
in (solve env _101_1391))
end
| false -> begin
(let _36_2942 = (base_and_refinement env wl t1)
in (match (_36_2942) with
| (base1, refinement1) -> begin
(let _36_2945 = (base_and_refinement env wl t2)
in (match (_36_2945) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _36_2949 = (match (((head_matches head head) <> FullMatch)) with
| true -> begin
(let _101_1394 = (let _101_1393 = (FStar_Absyn_Print.typ_to_string head)
in (let _101_1392 = (FStar_Absyn_Print.typ_to_string head')
in (FStar_Util.format2 "Assertion failed: expected full match of %s and %s\n" _101_1393 _101_1392)))
in (FStar_All.failwith _101_1394))
end
| false -> begin
()
end)
in (let subprobs = (FStar_List.map2 (fun a a' -> (match (((Prims.fst a), (Prims.fst a'))) with
| (FStar_Util.Inl (t), FStar_Util.Inl (t')) -> begin
(let _101_1398 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (FStar_All.pipe_left (fun _101_1397 -> TProb (_101_1397)) _101_1398))
end
| (FStar_Util.Inr (v), FStar_Util.Inr (v')) -> begin
(let _101_1400 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (FStar_All.pipe_left (fun _101_1399 -> EProb (_101_1399)) _101_1400))
end
| _36_2964 -> begin
(FStar_All.failwith "Impossible")
end)) args args')
in (let formula = (let _101_1402 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Absyn_Util.mk_conj_l _101_1402))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _36_2970 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _36_2973 = problem
in {lhs = lhs; relation = _36_2973.relation; rhs = rhs; element = _36_2973.element; logical_guard = _36_2973.logical_guard; scope = _36_2973.scope; reason = _36_2973.reason; loc = _36_2973.loc; rank = _36_2973.rank}) wl)))
end)
end))
end))
end)
end))
end))
end)))
end)
end))
end
| ((FStar_Absyn_Syntax.Typ_ascribed (_), _)) | ((FStar_Absyn_Syntax.Typ_meta (_), _)) | ((FStar_Absyn_Syntax.Typ_delayed (_), _)) | ((_, FStar_Absyn_Syntax.Typ_ascribed (_))) | ((_, FStar_Absyn_Syntax.Typ_meta (_))) | ((_, FStar_Absyn_Syntax.Typ_delayed (_))) -> begin
(FStar_All.failwith "Impossible")
end
| _36_3012 -> begin
(giveup env "head mismatch" orig)
end))))
end)))
end))))))))
and solve_c = (fun env problem wl -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _36_3029 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ")))) with
| true -> begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end
| false -> begin
()
end)
in (let sub_probs = (FStar_List.map2 (fun arg1 arg2 -> (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _101_1417 = (sub_prob t1 EQ t2 "effect arg")
in (FStar_All.pipe_left (fun _101_1416 -> TProb (_101_1416)) _101_1417))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _101_1419 = (sub_prob e1 EQ e2 "effect arg")
in (FStar_All.pipe_left (fun _101_1418 -> EProb (_101_1418)) _101_1419))
end
| _36_3044 -> begin
(FStar_All.failwith "impossible")
end)) c1_comp.FStar_Absyn_Syntax.effect_args c2_comp.FStar_Absyn_Syntax.effect_args)
in (let guard = (let _101_1421 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _101_1421))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in (match ((FStar_Util.physical_equality c1 c2)) with
| true -> begin
(let _101_1422 = (solve_prob orig None [] wl)
in (solve env _101_1422))
end
| false -> begin
(let _36_3049 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1424 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _101_1423 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.fprint3 "solve_c %s %s %s\n" _101_1424 (rel_to_string problem.relation) _101_1423)))
end
| false -> begin
()
end)
in (let r = (FStar_Tc_Env.get_range env)
in (let _36_3054 = (c1, c2)
in (match (_36_3054) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Absyn_Syntax.n, c2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Total (t1), FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (FStar_Absyn_Syntax.Total (_36_3061), FStar_Absyn_Syntax.Comp (_36_3064)) -> begin
(let _101_1426 = (let _36_3067 = problem
in (let _101_1425 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _101_1425; relation = _36_3067.relation; rhs = _36_3067.rhs; element = _36_3067.element; logical_guard = _36_3067.logical_guard; scope = _36_3067.scope; reason = _36_3067.reason; loc = _36_3067.loc; rank = _36_3067.rank}))
in (solve_c env _101_1426 wl))
end
| (FStar_Absyn_Syntax.Comp (_36_3070), FStar_Absyn_Syntax.Total (_36_3073)) -> begin
(let _101_1428 = (let _36_3076 = problem
in (let _101_1427 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _36_3076.lhs; relation = _36_3076.relation; rhs = _101_1427; element = _36_3076.element; logical_guard = _36_3076.logical_guard; scope = _36_3076.scope; reason = _36_3076.reason; loc = _36_3076.loc; rank = _36_3076.rank}))
in (solve_c env _101_1428 wl))
end
| (FStar_Absyn_Syntax.Comp (_36_3079), FStar_Absyn_Syntax.Comp (_36_3082)) -> begin
(match ((((FStar_Absyn_Util.is_ml_comp c1) && (FStar_Absyn_Util.is_ml_comp c2)) || ((FStar_Absyn_Util.is_total_comp c1) && ((FStar_Absyn_Util.is_total_comp c2) || (FStar_Absyn_Util.is_ml_comp c2))))) with
| true -> begin
(solve_t env (problem_using_guard orig (FStar_Absyn_Util.comp_result c1) problem.relation (FStar_Absyn_Util.comp_result c2) None "result type") wl)
end
| false -> begin
(let c1_comp = (FStar_Absyn_Util.comp_to_comp_typ c1)
in (let c2_comp = (FStar_Absyn_Util.comp_to_comp_typ c2)
in (match (((problem.relation = EQ) && (FStar_Absyn_Syntax.lid_equals c1_comp.FStar_Absyn_Syntax.effect_name c2_comp.FStar_Absyn_Syntax.effect_name))) with
| true -> begin
(solve_eq c1_comp c2_comp)
end
| false -> begin
(let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _36_3089 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(FStar_Util.fprint2 "solve_c for %s and %s\n" c1.FStar_Absyn_Syntax.effect_name.FStar_Absyn_Syntax.str c2.FStar_Absyn_Syntax.effect_name.FStar_Absyn_Syntax.str)
end
| false -> begin
()
end)
in (match ((FStar_Tc_Env.monad_leq env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _101_1431 = (let _101_1430 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _101_1429 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _101_1430 _101_1429)))
in (giveup env _101_1431 orig))
end
| Some (edge) -> begin
(match ((problem.relation = EQ)) with
| true -> begin
(let _36_3109 = (match (c1.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp1), _36_3102)::(FStar_Util.Inl (wlp1), _36_3097)::[] -> begin
(wp1, wlp1)
end
| _36_3106 -> begin
(let _101_1434 = (let _101_1433 = (let _101_1432 = (FStar_Absyn_Syntax.range_of_lid c1.FStar_Absyn_Syntax.effect_name)
in (FStar_Range.string_of_range _101_1432))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _101_1433))
in (FStar_All.failwith _101_1434))
end)
in (match (_36_3109) with
| (wp, wlp) -> begin
(let c1 = (let _101_1440 = (let _101_1439 = (let _101_1435 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _101_1435))
in (let _101_1438 = (let _101_1437 = (let _101_1436 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _101_1436))
in (_101_1437)::[])
in (_101_1439)::_101_1438))
in {FStar_Absyn_Syntax.effect_name = c2.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _101_1440; FStar_Absyn_Syntax.flags = c1.FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end
| false -> begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _36_33 -> (match (_36_33) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.MLEFFECT) | (FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _36_3116 -> begin
false
end))))
in (let _36_3139 = (match ((c1.FStar_Absyn_Syntax.effect_args, c2.FStar_Absyn_Syntax.effect_args)) with
| ((FStar_Util.Inl (wp1), _36_3123)::_36_3119, (FStar_Util.Inl (wp2), _36_3131)::_36_3127) -> begin
(wp1, wp2)
end
| _36_3136 -> begin
(let _101_1444 = (let _101_1443 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _101_1442 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _101_1443 _101_1442)))
in (FStar_All.failwith _101_1444))
end)
in (match (_36_3139) with
| (wpc1, wpc2) -> begin
(match ((FStar_Util.physical_equality wpc1 wpc2)) with
| true -> begin
(solve_t env (problem_using_guard orig c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ None "result type") wl)
end
| false -> begin
(let c2_decl = (FStar_Tc_Env.get_effect_decl env c2.FStar_Absyn_Syntax.effect_name)
in (let g = (match (is_null_wp_2) with
| true -> begin
(let _36_3141 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(FStar_Util.print_string "Using trivial wp ... \n")
end
| false -> begin
()
end)
in (let _101_1450 = (let _101_1449 = (let _101_1448 = (FStar_Absyn_Syntax.targ c1.FStar_Absyn_Syntax.result_typ)
in (let _101_1447 = (let _101_1446 = (let _101_1445 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _101_1445))
in (_101_1446)::[])
in (_101_1448)::_101_1447))
in (c2_decl.FStar_Absyn_Syntax.trivial, _101_1449))
in (FStar_Absyn_Syntax.mk_Typ_app _101_1450 (Some (FStar_Absyn_Syntax.ktype)) r)))
end
| false -> begin
(let wp2_imp_wp1 = (let _101_1462 = (let _101_1461 = (let _101_1460 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _101_1459 = (let _101_1458 = (FStar_Absyn_Syntax.targ wpc2)
in (let _101_1457 = (let _101_1456 = (let _101_1452 = (let _101_1451 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.imp_lid _101_1451))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _101_1452))
in (let _101_1455 = (let _101_1454 = (let _101_1453 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _101_1453))
in (_101_1454)::[])
in (_101_1456)::_101_1455))
in (_101_1458)::_101_1457))
in (_101_1460)::_101_1459))
in (c2_decl.FStar_Absyn_Syntax.wp_binop, _101_1461))
in (FStar_Absyn_Syntax.mk_Typ_app _101_1462 None r))
in (let _101_1467 = (let _101_1466 = (let _101_1465 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _101_1464 = (let _101_1463 = (FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_101_1463)::[])
in (_101_1465)::_101_1464))
in (c2_decl.FStar_Absyn_Syntax.wp_as_type, _101_1466))
in (FStar_Absyn_Syntax.mk_Typ_app _101_1467 (Some (FStar_Absyn_Syntax.ktype)) r)))
end)
in (let base_prob = (let _101_1469 = (sub_prob c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _101_1468 -> TProb (_101_1468)) _101_1469))
in (let wl = (let _101_1473 = (let _101_1472 = (let _101_1471 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _101_1471 g))
in (FStar_All.pipe_left (fun _101_1470 -> Some (_101_1470)) _101_1472))
in (solve_prob orig _101_1473 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end)
end)))
end)
end))))
end)))
end)
end)
end))))
end)))))))
and solve_e = (fun env problem wl -> (match ((compress_prob wl (EProb (problem)))) with
| EProb (p) -> begin
(solve_e' env p wl)
end
| _36_3153 -> begin
(FStar_All.failwith "Impossible")
end))
and solve_e' = (fun env problem wl -> (let problem = (let _36_3157 = problem
in {lhs = _36_3157.lhs; relation = EQ; rhs = _36_3157.rhs; element = _36_3157.element; logical_guard = _36_3157.logical_guard; scope = _36_3157.scope; reason = _36_3157.reason; loc = _36_3157.loc; rank = _36_3157.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun lhs rhs reason -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _36_3169 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1483 = (prob_to_string env orig)
in (FStar_Util.fprint1 "Attempting:\n%s\n" _101_1483))
end
| false -> begin
()
end)
in (let flex_rigid = (fun _36_3176 e2 -> (match (_36_3176) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun xs args2 -> (let _36_3203 = (let _101_1499 = (FStar_All.pipe_right args2 (FStar_List.map (fun _36_34 -> (match (_36_34) with
| (FStar_Util.Inl (t), imp) -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _36_3190 = (new_tvar t.FStar_Absyn_Syntax.pos xs kk)
in (match (_36_3190) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Typ_app (gi, args1) (Some (kk)) t.FStar_Absyn_Syntax.pos)
in (let _101_1495 = (let _101_1494 = (sub_prob gi_pi t "type index")
in (FStar_All.pipe_left (fun _101_1493 -> TProb (_101_1493)) _101_1494))
in ((FStar_Util.Inl (gi_xi), imp), _101_1495)))
end)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let tt = (FStar_Tc_Recheck.recompute_typ v)
in (let _36_3199 = (new_evar v.FStar_Absyn_Syntax.pos xs tt)
in (match (_36_3199) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Exp_app (gi, args1) (Some (tt)) v.FStar_Absyn_Syntax.pos)
in (let _101_1498 = (let _101_1497 = (sub_prob gi_pi v "expression index")
in (FStar_All.pipe_left (fun _101_1496 -> EProb (_101_1496)) _101_1497))
in ((FStar_Util.Inr (gi_xi), imp), _101_1498)))
end)))
end))))
in (FStar_All.pipe_right _101_1499 FStar_List.unzip))
in (match (_36_3203) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _101_1501 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) gi_pi)
in (FStar_Absyn_Util.mk_conj_l _101_1501))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun head2 args2 -> (let giveup = (fun reason -> (let _101_1508 = (FStar_Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _101_1508 orig)))
in (match ((let _101_1509 = (FStar_Absyn_Util.compress_exp head2)
in _101_1509.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _36_3220 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_36_3220) with
| (all_xs, tres) -> begin
(match (((FStar_List.length all_xs) <> (FStar_List.length args1))) with
| true -> begin
(let _101_1512 = (let _101_1511 = (FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _101_1510 = (FStar_Absyn_Print.args_to_string args2)
in (FStar_Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _101_1511 _101_1510)))
in (giveup _101_1512))
end
| false -> begin
(let rec aux = (fun xs args -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(FStar_All.failwith "impossible")
end
| ((FStar_Util.Inl (_36_3237), _36_3240)::xs, (FStar_Util.Inl (_36_3245), _36_3248)::args) -> begin
(aux xs args)
end
| ((FStar_Util.Inr (xi), _36_3256)::xs, (FStar_Util.Inr (arg), _36_3263)::args) -> begin
(match ((let _101_1517 = (FStar_Absyn_Util.compress_exp arg)
in _101_1517.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (z) -> begin
(match ((FStar_Absyn_Util.bvar_eq y z)) with
| true -> begin
(let _36_3272 = (sub_problems all_xs args2)
in (match (_36_3272) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _101_1521 = (let _101_1520 = (let _101_1519 = (let _101_1518 = (FStar_Absyn_Util.bvar_to_exp xi)
in (_101_1518, gi_xi))
in (FStar_Absyn_Syntax.mk_Exp_app' _101_1519 None e1.FStar_Absyn_Syntax.pos))
in (all_xs, _101_1520))
in (FStar_Absyn_Syntax.mk_Exp_abs _101_1521 None e1.FStar_Absyn_Syntax.pos))
in (let _36_3274 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1525 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _101_1524 = (FStar_Absyn_Print.exp_to_string sol)
in (let _101_1523 = (let _101_1522 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _101_1522 (FStar_String.concat "\n")))
in (FStar_Util.fprint3 "Projected: %s -> %s\nSubprobs=\n%s\n" _101_1525 _101_1524 _101_1523))))
end
| false -> begin
()
end)
in (let _101_1527 = (let _101_1526 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _101_1526))
in (solve env _101_1527))))
end))
end
| false -> begin
(aux xs args)
end)
end
| _36_3277 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _101_1530 = (let _101_1529 = (FStar_Absyn_Print.binder_to_string x)
in (let _101_1528 = (FStar_Absyn_Print.arg_to_string arg)
in (FStar_Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _101_1529 _101_1528)))
in (giveup _101_1530))
end))
in (aux (FStar_List.rev all_xs) (FStar_List.rev args1)))
end)
end))
end
| _36_3286 -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun _36_3288 -> (match (()) with
| () -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end
| false -> begin
(let _36_3289 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1534 = (FStar_Absyn_Print.exp_to_string e1)
in (let _101_1533 = (FStar_Absyn_Print.exp_to_string e2)
in (FStar_Util.fprint2 "Imitating expressions: %s =?= %s\n" _101_1534 _101_1533)))
end
| false -> begin
()
end)
in (let _36_3293 = (FStar_Absyn_Util.head_and_args_e e2)
in (match (_36_3293) with
| (head2, args2) -> begin
(let fvhead = (FStar_Absyn_Util.freevars_exp head2)
in (let _36_3298 = (occurs_check_e env (u1, t1) head2)
in (match (_36_3298) with
| (occurs_ok, _36_3297) -> begin
(match (((FStar_Absyn_Util.fvs_included fvhead FStar_Absyn_Syntax.no_fvs) && occurs_ok)) with
| true -> begin
(let _36_3306 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_36_3306) with
| (xs, tres) -> begin
(let _36_3310 = (sub_problems xs args2)
in (match (_36_3310) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _36_3314 -> begin
(let _101_1536 = (let _101_1535 = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (xs, _101_1535))
in (FStar_Absyn_Syntax.mk_Exp_abs _101_1536 None e1.FStar_Absyn_Syntax.pos))
end))
in (let _36_3316 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1540 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _101_1539 = (FStar_Absyn_Print.exp_to_string sol)
in (let _101_1538 = (let _101_1537 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _101_1537 (FStar_String.concat "\n")))
in (FStar_Util.fprint3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _101_1540 _101_1539 _101_1538))))
end
| false -> begin
()
end)
in (let _101_1542 = (let _101_1541 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _101_1541))
in (solve env _101_1542))))
end))
end))
end
| false -> begin
(match (occurs_ok) with
| true -> begin
(project_e head2 args2)
end
| false -> begin
(giveup env "flex-rigid: occurs check failed" orig)
end)
end)
end)))
end)))
end)
end))
in (match (maybe_vars1) with
| (None) | (Some ([])) -> begin
(imitate_or_project_e ())
end
| Some (xs) -> begin
(let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (FStar_Absyn_Util.freevars_exp e2)
in (let _36_3328 = (occurs_check_e env (u1, t1) e2)
in (match (_36_3328) with
| (occurs_ok, _36_3327) -> begin
(match ((((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && occurs_ok)) with
| true -> begin
(let sol = (FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.FStar_Absyn_Syntax.pos)
in (let _101_1543 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _101_1543)))
end
| false -> begin
(imitate_or_project_e ())
end)
end))))
end)))))
end))
in (let flex_flex = (fun _36_3335 _36_3340 -> (match ((_36_3335, _36_3340)) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(match (wl.defer_ok) with
| true -> begin
(solve env (defer "flex-flex: not a pattern" orig wl))
end
| false -> begin
(giveup env "flex-flex expressions not patterns" orig)
end)
end
| (Some (xs), Some (ys)) -> begin
(match (((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys))) with
| true -> begin
(solve env wl)
end
| false -> begin
(let zs = (intersect_vars xs ys)
in (let tt = (FStar_Tc_Recheck.recompute_typ e2)
in (let _36_3361 = (let _101_1548 = (FStar_Tc_Env.get_range env)
in (new_evar _101_1548 zs tt))
in (match (_36_3361) with
| (u, _36_3360) -> begin
(let sub1 = (match (xs) with
| [] -> begin
u
end
| _36_3364 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.FStar_Absyn_Syntax.pos)
end)
in (let sub2 = (match (ys) with
| [] -> begin
u
end
| _36_3368 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.FStar_Absyn_Syntax.pos)
end)
in (let _101_1549 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _101_1549))))
end))))
end)
end)))
end))
in (let smt_fallback = (fun e1 e2 -> (match (wl.smt_ok) with
| true -> begin
(let _36_3373 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1554 = (prob_to_string env orig)
in (FStar_Util.fprint1 "Using SMT to solve:\n%s\n" _101_1554))
end
| false -> begin
()
end)
in (let _36_3378 = (let _101_1556 = (FStar_Tc_Env.get_range env)
in (let _101_1555 = (FStar_Tc_Env.binders env)
in (new_tvar _101_1556 _101_1555 FStar_Absyn_Syntax.ktype)))
in (match (_36_3378) with
| (t, _36_3377) -> begin
(let _101_1560 = (let _101_1559 = (let _101_1558 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _101_1557 -> Some (_101_1557)) _101_1558))
in (solve_prob orig _101_1559 [] wl))
in (solve env _101_1560))
end)))
end
| false -> begin
(giveup env "no SMT solution permitted" orig)
end))
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_ascribed (e1, _36_3381, _36_3383), _36_3387) -> begin
(solve_e env (let _36_3389 = problem
in {lhs = e1; relation = _36_3389.relation; rhs = _36_3389.rhs; element = _36_3389.element; logical_guard = _36_3389.logical_guard; scope = _36_3389.scope; reason = _36_3389.reason; loc = _36_3389.loc; rank = _36_3389.rank}) wl)
end
| (_36_3392, FStar_Absyn_Syntax.Exp_ascribed (e2, _36_3395, _36_3397)) -> begin
(solve_e env (let _36_3401 = problem
in {lhs = _36_3401.lhs; relation = _36_3401.relation; rhs = e2; element = _36_3401.element; logical_guard = _36_3401.logical_guard; scope = _36_3401.scope; reason = _36_3401.reason; loc = _36_3401.loc; rank = _36_3401.rank}) wl)
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _101_1562 = (destruct_flex_e e1)
in (let _101_1561 = (destruct_flex_e e2)
in (flex_flex _101_1562 _101_1561)))
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(let _101_1563 = (destruct_flex_e e1)
in (flex_rigid _101_1563 e2))
end
| ((_, FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _101_1564 = (destruct_flex_e e2)
in (flex_rigid _101_1564 e1))
end
| (FStar_Absyn_Syntax.Exp_bvar (x1), FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
(match ((FStar_Absyn_Util.bvd_eq x1.FStar_Absyn_Syntax.v x1'.FStar_Absyn_Syntax.v)) with
| true -> begin
(let _101_1565 = (solve_prob orig None [] wl)
in (solve env _101_1565))
end
| false -> begin
(let _101_1571 = (let _101_1570 = (let _101_1569 = (let _101_1568 = (FStar_Tc_Recheck.recompute_typ e1)
in (let _101_1567 = (FStar_Tc_Recheck.recompute_typ e2)
in (FStar_Absyn_Util.mk_eq _101_1568 _101_1567 e1 e2)))
in (FStar_All.pipe_left (fun _101_1566 -> Some (_101_1566)) _101_1569))
in (solve_prob orig _101_1570 [] wl))
in (solve env _101_1571))
end)
end
| (FStar_Absyn_Syntax.Exp_fvar (fv1, _36_3540), FStar_Absyn_Syntax.Exp_fvar (fv1', _36_3545)) -> begin
(match ((FStar_Absyn_Syntax.lid_equals fv1.FStar_Absyn_Syntax.v fv1'.FStar_Absyn_Syntax.v)) with
| true -> begin
(let _101_1572 = (solve_prob orig None [] wl)
in (solve env _101_1572))
end
| false -> begin
(giveup env "free-variables unequal" orig)
end)
end
| (FStar_Absyn_Syntax.Exp_constant (s1), FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun s1 s2 -> (match ((s1, s2)) with
| (FStar_Absyn_Syntax.Const_bytearray (b1, _36_3559), FStar_Absyn_Syntax.Const_bytearray (b2, _36_3564)) -> begin
(b1 = b2)
end
| (FStar_Absyn_Syntax.Const_string (b1, _36_3570), FStar_Absyn_Syntax.Const_string (b2, _36_3575)) -> begin
(b1 = b2)
end
| _36_3580 -> begin
(s1 = s2)
end))
in (match ((const_eq s1 s1')) with
| true -> begin
(let _101_1577 = (solve_prob orig None [] wl)
in (solve env _101_1577))
end
| false -> begin
(giveup env "constants unequal" orig)
end))
end
| (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_36_3590); FStar_Absyn_Syntax.tk = _36_3588; FStar_Absyn_Syntax.pos = _36_3586; FStar_Absyn_Syntax.fvs = _36_3584; FStar_Absyn_Syntax.uvs = _36_3582}, _36_3594), _36_3598) -> begin
(let _101_1579 = (let _36_3600 = problem
in (let _101_1578 = (whnf_e env e1)
in {lhs = _101_1578; relation = _36_3600.relation; rhs = _36_3600.rhs; element = _36_3600.element; logical_guard = _36_3600.logical_guard; scope = _36_3600.scope; reason = _36_3600.reason; loc = _36_3600.loc; rank = _36_3600.rank}))
in (solve_e env _101_1579 wl))
end
| (_36_3603, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_36_3613); FStar_Absyn_Syntax.tk = _36_3611; FStar_Absyn_Syntax.pos = _36_3609; FStar_Absyn_Syntax.fvs = _36_3607; FStar_Absyn_Syntax.uvs = _36_3605}, _36_3617)) -> begin
(let _101_1581 = (let _36_3621 = problem
in (let _101_1580 = (whnf_e env e2)
in {lhs = _36_3621.lhs; relation = _36_3621.relation; rhs = _101_1580; element = _36_3621.element; logical_guard = _36_3621.logical_guard; scope = _36_3621.scope; reason = _36_3621.reason; loc = _36_3621.loc; rank = _36_3621.rank}))
in (solve_e env _101_1581 wl))
end
| (FStar_Absyn_Syntax.Exp_app (head1, args1), FStar_Absyn_Syntax.Exp_app (head2, args2)) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun sub_probs wl args1 args2 -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _101_1591 = (let _101_1590 = (FStar_List.map p_guard sub_probs)
in (FStar_All.pipe_right _101_1590 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Util.mk_conj_l _101_1591))
in (let g = (simplify_formula env guard)
in (let g = (FStar_Absyn_Util.compress_typ g)
in (match (g.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
(let _101_1592 = (solve_prob orig None wl.subst (let _36_3646 = orig_wl
in {attempting = _36_3646.attempting; wl_deferred = _36_3646.wl_deferred; subst = []; ctr = _36_3646.ctr; slack_vars = _36_3646.slack_vars; defer_ok = _36_3646.defer_ok; smt_ok = _36_3646.smt_ok; tcenv = _36_3646.tcenv}))
in (solve env _101_1592))
end
| _36_3649 -> begin
(let _36_3653 = (let _101_1594 = (FStar_Tc_Env.get_range env)
in (let _101_1593 = (FStar_Tc_Env.binders env)
in (new_tvar _101_1594 _101_1593 FStar_Absyn_Syntax.ktype)))
in (match (_36_3653) with
| (t, _36_3652) -> begin
(let guard = (let _101_1595 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_Absyn_Util.mk_disj g _101_1595))
in (let _101_1596 = (solve_prob orig (Some (guard)) wl.subst (let _36_3655 = orig_wl
in {attempting = _36_3655.attempting; wl_deferred = _36_3655.wl_deferred; subst = []; ctr = _36_3655.ctr; slack_vars = _36_3655.slack_vars; defer_ok = _36_3655.defer_ok; smt_ok = _36_3655.smt_ok; tcenv = _36_3655.tcenv}))
in (solve env _101_1596)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _101_1598 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (FStar_All.pipe_left (fun _101_1597 -> TProb (_101_1597)) _101_1598))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _101_1600 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (FStar_All.pipe_left (fun _101_1599 -> EProb (_101_1599)) _101_1600))
end
| _36_3675 -> begin
(FStar_All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _36_3677 = wl
in {attempting = (prob)::[]; wl_deferred = []; subst = _36_3677.subst; ctr = _36_3677.ctr; slack_vars = _36_3677.slack_vars; defer_ok = false; smt_ok = false; tcenv = _36_3677.tcenv}))) with
| Failed (_36_3680) -> begin
(smt_fallback e1 e2)
end
| Success (subst, _36_3684) -> begin
(solve_args ((prob)::sub_probs) (let _36_3687 = wl
in {attempting = _36_3687.attempting; wl_deferred = _36_3687.wl_deferred; subst = subst; ctr = _36_3687.ctr; slack_vars = _36_3687.slack_vars; defer_ok = _36_3687.defer_ok; smt_ok = _36_3687.smt_ok; tcenv = _36_3687.tcenv}) rest1 rest2)
end))
end
| _36_3690 -> begin
(FStar_All.failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun head1 head2 -> (match ((let _101_1608 = (let _101_1605 = (FStar_Absyn_Util.compress_exp head1)
in _101_1605.FStar_Absyn_Syntax.n)
in (let _101_1607 = (let _101_1606 = (FStar_Absyn_Util.compress_exp head2)
in _101_1606.FStar_Absyn_Syntax.n)
in (_101_1608, _101_1607)))) with
| (FStar_Absyn_Syntax.Exp_bvar (x), FStar_Absyn_Syntax.Exp_bvar (y)) when ((FStar_Absyn_Util.bvar_eq x y) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _36_3701), FStar_Absyn_Syntax.Exp_fvar (g, _36_3706)) when (((FStar_Absyn_Util.fvar_eq f g) && (not ((FStar_Absyn_Util.is_interpreted f.FStar_Absyn_Syntax.v)))) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_ascribed (e, _36_3712, _36_3714), _36_3718) -> begin
(match_head_and_args e head2)
end
| (_36_3721, FStar_Absyn_Syntax.Exp_ascribed (e, _36_3724, _36_3726)) -> begin
(match_head_and_args head1 e)
end
| (FStar_Absyn_Syntax.Exp_abs (_36_3731), _36_3734) -> begin
(let _101_1610 = (let _36_3736 = problem
in (let _101_1609 = (whnf_e env e1)
in {lhs = _101_1609; relation = _36_3736.relation; rhs = _36_3736.rhs; element = _36_3736.element; logical_guard = _36_3736.logical_guard; scope = _36_3736.scope; reason = _36_3736.reason; loc = _36_3736.loc; rank = _36_3736.rank}))
in (solve_e env _101_1610 wl))
end
| (_36_3739, FStar_Absyn_Syntax.Exp_abs (_36_3741)) -> begin
(let _101_1612 = (let _36_3744 = problem
in (let _101_1611 = (whnf_e env e2)
in {lhs = _36_3744.lhs; relation = _36_3744.relation; rhs = _101_1611; element = _36_3744.element; logical_guard = _36_3744.logical_guard; scope = _36_3744.scope; reason = _36_3744.reason; loc = _36_3744.loc; rank = _36_3744.rank}))
in (solve_e env _101_1612 wl))
end
| _36_3747 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _36_3749 -> begin
(let _36_3753 = (let _101_1614 = (FStar_Tc_Env.get_range env)
in (let _101_1613 = (FStar_Tc_Env.binders env)
in (new_tvar _101_1614 _101_1613 FStar_Absyn_Syntax.ktype)))
in (match (_36_3753) with
| (t, _36_3752) -> begin
(let guard = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _36_3755 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1615 = (FStar_Absyn_Print.typ_to_string guard)
in (FStar_Util.fprint1 "Emitting guard %s\n" _101_1615))
end
| false -> begin
()
end)
in (let _101_1619 = (let _101_1618 = (let _101_1617 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _101_1616 -> Some (_101_1616)) _101_1617))
in (solve_prob orig _101_1618 [] wl))
in (solve env _101_1619))))
end))
end)))))))))))

type guard_formula =
| Trivial
| NonTrivial of FStar_Absyn_Syntax.formula

let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial -> begin
true
end
| _ -> begin
false
end))

let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

let ___NonTrivial____0 = (fun projectee -> (match (projectee) with
| NonTrivial (_36_3759) -> begin
_36_3759
end))

type implicits =
((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list

type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

let is_Mkguard_t = (Obj.magic (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t")))

let guard_to_string = (fun env g -> (let form = (match (g.guard_f) with
| Trivial -> begin
"trivial"
end
| NonTrivial (f) -> begin
(match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(FStar_Tc_Normalize.formula_norm_to_string env f)
end
| false -> begin
"non-trivial"
end)
end)
in (let carry = (let _101_1650 = (FStar_List.map (fun _36_3773 -> (match (_36_3773) with
| (_36_3771, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (FStar_All.pipe_right _101_1650 (FStar_String.concat ",\n")))
in (FStar_Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun g -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_form = (fun g -> g.guard_f)

let is_trivial = (fun g -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _36_3779} -> begin
true
end
| _36_3786 -> begin
false
end))

let trivial_guard = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}

let abstract_guard = (fun x g -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _36_3802 -> begin
(FStar_All.failwith "impossible")
end)
in (let _101_1667 = (let _36_3804 = g
in (let _101_1666 = (let _101_1665 = (let _101_1664 = (let _101_1663 = (let _101_1662 = (FStar_Absyn_Syntax.v_binder x)
in (_101_1662)::[])
in (_101_1663, f))
in (FStar_Absyn_Syntax.mk_Typ_lam _101_1664 None f.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (fun _101_1661 -> NonTrivial (_101_1661)) _101_1665))
in {guard_f = _101_1666; deferred = _36_3804.deferred; implicits = _36_3804.implicits}))
in Some (_101_1667)))
end))

let apply_guard = (fun g e -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _36_3811 = g
in (let _101_1679 = (let _101_1678 = (let _101_1677 = (let _101_1676 = (let _101_1675 = (let _101_1674 = (FStar_Absyn_Syntax.varg e)
in (_101_1674)::[])
in (f, _101_1675))
in (FStar_Absyn_Syntax.mk_Typ_app _101_1676))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn f.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _101_1677))
in NonTrivial (_101_1678))
in {guard_f = _101_1679; deferred = _36_3811.deferred; implicits = _36_3811.implicits}))
end))

let trivial = (fun t -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_36_3816) -> begin
(FStar_All.failwith "impossible")
end))

let conj_guard_f = (fun g1 g2 -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _101_1686 = (FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_101_1686))
end))

let check_trivial = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Absyn_Syntax.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _36_3834 -> begin
NonTrivial (t)
end))

let imp_guard_f = (fun g1 g2 -> (match ((g1, g2)) with
| (Trivial, g) -> begin
g
end
| (g, Trivial) -> begin
Trivial
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let imp = (FStar_Absyn_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

let binop_guard = (fun f g1 g2 -> (let _101_1709 = (f g1.guard_f g2.guard_f)
in {guard_f = _101_1709; deferred = {carry = (FStar_List.append g1.deferred.carry g2.deferred.carry); slack = (FStar_List.append g1.deferred.slack g2.deferred.slack)}; implicits = (FStar_List.append g1.implicits g2.implicits)}))

let conj_guard = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun binders g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _36_3861 = g
in (let _101_1724 = (let _101_1723 = (FStar_Absyn_Util.close_forall binders f)
in (FStar_All.pipe_right _101_1723 (fun _101_1722 -> NonTrivial (_101_1722))))
in {guard_f = _101_1724; deferred = _36_3861.deferred; implicits = _36_3861.implicits}))
end))

let mk_guard = (fun g ps slack locs -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _101_1736 = (FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _101_1735 = (FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _101_1736 (rel_to_string rel) _101_1735)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun env t1 rel t2 -> (let x = (let _101_1745 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.gen_bvar_p _101_1745 t1))
in (let env = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let p = (let _101_1749 = (let _101_1747 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left (fun _101_1746 -> Some (_101_1746)) _101_1747))
in (let _101_1748 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _101_1749 _101_1748)))
in (TProb (p), x)))))

let new_k_problem = (fun env lhs rel rhs elt loc -> (let reason = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _101_1757 = (FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _101_1756 = (FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _101_1757 (rel_to_string rel) _101_1756)))
end
| false -> begin
"TOP"
end)
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let simplify_guard = (fun env g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _36_3895 = (match ((FStar_Tc_Env.debug env FStar_Options.High)) with
| true -> begin
(let _101_1762 = (FStar_Absyn_Print.typ_to_string f)
in (FStar_Util.fprint1 "Simplifying guard %s\n" _101_1762))
end
| false -> begin
()
end)
in (let f = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Absyn_Syntax.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _36_3901 -> begin
NonTrivial (f)
end)
in (let _36_3903 = g
in {guard_f = f; deferred = _36_3903.deferred; implicits = _36_3903.implicits}))))
end))

let solve_and_commit = (fun env probs err -> (let probs = (match ((FStar_ST.read FStar_Options.eager_inference)) with
| true -> begin
(let _36_3908 = probs
in {attempting = _36_3908.attempting; wl_deferred = _36_3908.wl_deferred; subst = _36_3908.subst; ctr = _36_3908.ctr; slack_vars = _36_3908.slack_vars; defer_ok = false; smt_ok = _36_3908.smt_ok; tcenv = _36_3908.tcenv})
end
| false -> begin
probs
end)
in (let sol = (solve env probs)
in (match (sol) with
| Success (s, deferred) -> begin
(let _36_3916 = (commit env s)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _36_3922 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel")))) with
| true -> begin
(let _101_1774 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _101_1774))
end
| false -> begin
()
end)
in (err (d, s)))
end))))

let with_guard = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _101_1786 = (let _101_1785 = (let _101_1784 = (let _101_1783 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _101_1783 (fun _101_1782 -> NonTrivial (_101_1782))))
in {guard_f = _101_1784; deferred = d; implicits = []})
in (simplify_guard env _101_1785))
in (FStar_All.pipe_left (fun _101_1781 -> Some (_101_1781)) _101_1786))
end))

let try_keq = (fun env k1 k2 -> (let _36_3933 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1794 = (FStar_Absyn_Print.kind_to_string k1)
in (let _101_1793 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.fprint2 "try_keq of %s and %s\n" _101_1794 _101_1793)))
end
| false -> begin
()
end)
in (let prob = (let _101_1799 = (let _101_1798 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _101_1797 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _101_1796 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _101_1798 EQ _101_1797 None _101_1796))))
in (FStar_All.pipe_left (fun _101_1795 -> KProb (_101_1795)) _101_1799))
in (let _101_1801 = (solve_and_commit env (singleton env prob) (fun _36_3936 -> None))
in (FStar_All.pipe_left (with_guard env prob) _101_1801)))))

let keq = (fun env t k1 k2 -> (match ((try_keq env k1 k2)) with
| None -> begin
(let r = (match (t) with
| None -> begin
(FStar_Tc_Env.get_range env)
end
| Some (t) -> begin
t.FStar_Absyn_Syntax.pos
end)
in (match (t) with
| None -> begin
(let _101_1812 = (let _101_1811 = (let _101_1810 = (FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_101_1810, r))
in FStar_Absyn_Syntax.Error (_101_1811))
in (Prims.raise _101_1812))
end
| Some (t) -> begin
(let _101_1815 = (let _101_1814 = (let _101_1813 = (FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_101_1813, r))
in FStar_Absyn_Syntax.Error (_101_1814))
in (Prims.raise _101_1815))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun env k1 k2 -> (let _36_3955 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1825 = (let _101_1822 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _101_1822))
in (let _101_1824 = (FStar_Absyn_Print.kind_to_string k1)
in (let _101_1823 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.fprint3 "(%s) subkind of %s and %s\n" _101_1825 _101_1824 _101_1823))))
end
| false -> begin
()
end)
in (let prob = (let _101_1830 = (let _101_1829 = (whnf_k env k1)
in (let _101_1828 = (whnf_k env k2)
in (let _101_1827 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _101_1829 SUB _101_1828 None _101_1827))))
in (FStar_All.pipe_left (fun _101_1826 -> KProb (_101_1826)) _101_1830))
in (let res = (let _101_1837 = (let _101_1836 = (solve_and_commit env (singleton env prob) (fun _36_3958 -> (let _101_1835 = (let _101_1834 = (let _101_1833 = (FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _101_1832 = (FStar_Tc_Env.get_range env)
in (_101_1833, _101_1832)))
in FStar_Absyn_Syntax.Error (_101_1834))
in (Prims.raise _101_1835))))
in (FStar_All.pipe_left (with_guard env prob) _101_1836))
in (FStar_Util.must _101_1837))
in res))))

let try_teq = (fun env t1 t2 -> (let _36_3964 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1845 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1844 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.fprint2 "try_teq of %s and %s\n" _101_1845 _101_1844)))
end
| false -> begin
()
end)
in (let prob = (let _101_1848 = (let _101_1847 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _101_1847))
in (FStar_All.pipe_left (fun _101_1846 -> TProb (_101_1846)) _101_1848))
in (let g = (let _101_1850 = (solve_and_commit env (singleton env prob) (fun _36_3967 -> None))
in (FStar_All.pipe_left (with_guard env prob) _101_1850))
in g))))

let teq = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _101_1860 = (let _101_1859 = (let _101_1858 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _101_1857 = (FStar_Tc_Env.get_range env)
in (_101_1858, _101_1857)))
in FStar_Absyn_Syntax.Error (_101_1859))
in (Prims.raise _101_1860))
end
| Some (g) -> begin
(let _36_3976 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1863 = (FStar_Absyn_Print.typ_to_string t1)
in (let _101_1862 = (FStar_Absyn_Print.typ_to_string t2)
in (let _101_1861 = (guard_to_string env g)
in (FStar_Util.fprint3 "teq of %s and %s succeeded with guard %s\n" _101_1863 _101_1862 _101_1861))))
end
| false -> begin
()
end)
in g)
end))

let try_subtype = (fun env t1 t2 -> (let _36_3981 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1871 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _101_1870 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.fprint2 "try_subtype of %s and %s\n" _101_1871 _101_1870)))
end
| false -> begin
()
end)
in (let _36_3985 = (new_t_prob env t1 SUB t2)
in (match (_36_3985) with
| (prob, x) -> begin
(let g = (let _101_1873 = (solve_and_commit env (singleton env prob) (fun _36_3986 -> None))
in (FStar_All.pipe_left (with_guard env prob) _101_1873))
in (let _36_3989 = (match (((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g))) with
| true -> begin
(let _101_1877 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _101_1876 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _101_1875 = (let _101_1874 = (FStar_Util.must g)
in (guard_to_string env _101_1874))
in (FStar_Util.fprint3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _101_1877 _101_1876 _101_1875))))
end
| false -> begin
()
end)
in (abstract_guard x g)))
end))))

let subtype_fail = (fun env t1 t2 -> (let _101_1884 = (let _101_1883 = (let _101_1882 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _101_1881 = (FStar_Tc_Env.get_range env)
in (_101_1882, _101_1881)))
in FStar_Absyn_Syntax.Error (_101_1883))
in (Prims.raise _101_1884)))

let subtype = (fun env t1 t2 -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun env c1 c2 -> (let _36_4003 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1898 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _101_1897 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.fprint2 "sub_comp of %s and %s\n" _101_1898 _101_1897)))
end
| false -> begin
()
end)
in (let rel = (match (env.FStar_Tc_Env.use_eq) with
| true -> begin
EQ
end
| false -> begin
SUB
end)
in (let prob = (let _101_1901 = (let _101_1900 = (FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _101_1900 "sub_comp"))
in (FStar_All.pipe_left (fun _101_1899 -> CProb (_101_1899)) _101_1901))
in (let _101_1903 = (solve_and_commit env (singleton env prob) (fun _36_4007 -> None))
in (FStar_All.pipe_left (with_guard env prob) _101_1903))))))

let solve_deferred_constraints = (fun env g -> (let fail = (fun _36_4014 -> (match (_36_4014) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _36_4019 = (match (((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && ((FStar_List.length g.deferred.carry) <> 0))) with
| true -> begin
(let _101_1916 = (let _101_1915 = (FStar_All.pipe_right g.deferred.carry (FStar_List.map (fun _36_4018 -> (match (_36_4018) with
| (msg, x) -> begin
(let _101_1914 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc x))
in (let _101_1913 = (prob_to_string env x)
in (let _101_1912 = (let _101_1911 = (FStar_All.pipe_right (p_guard x) Prims.fst)
in (FStar_Tc_Normalize.formula_norm_to_string env _101_1911))
in (FStar_Util.format4 "(At %s) %s\n%s\nguard is %s\n" _101_1914 msg _101_1913 _101_1912))))
end))))
in (FStar_All.pipe_right _101_1915 (FStar_String.concat "\n")))
in (FStar_All.pipe_left (FStar_Util.fprint1 "Trying to solve carried problems: begin\n%s\nend\n") _101_1916))
end
| false -> begin
()
end)
in (let gopt = (let _101_1917 = (wl_of_guard env g.deferred)
in (solve_and_commit env _101_1917 fail))
in (match (gopt) with
| Some ({carry = _36_4024; slack = slack}) -> begin
(let _36_4027 = (fix_slack_vars slack)
in (let _36_4029 = g
in {guard_f = _36_4029.guard_f; deferred = no_deferred; implicits = _36_4029.implicits}))
end
| _36_4032 -> begin
(FStar_All.failwith "impossible")
end)))))

let try_discharge_guard = (fun env g -> (let g = (solve_deferred_constraints env g)
in (match ((not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Absyn_Syntax.str)))) with
| true -> begin
()
end
| false -> begin
(match (g.guard_f) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let vc = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(let _36_4043 = (match ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel")))) with
| true -> begin
(let _101_1924 = (FStar_Tc_Env.get_range env)
in (let _101_1923 = (let _101_1922 = (FStar_Absyn_Print.formula_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _101_1922))
in (FStar_Tc_Errors.diag _101_1924 _101_1923)))
end
| false -> begin
()
end)
in (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env vc))
end))
end)
end)))

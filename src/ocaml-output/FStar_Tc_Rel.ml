
open Prims
let new_kvar = (fun r binders -> (let u = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (let _102_7 = (let _102_6 = (let _102_5 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _102_5))
in (FStar_Absyn_Syntax.mk_Kind_uvar _102_6 r))
in (_102_7, u))))

let new_tvar = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Absyn_Syntax.is_null_binder x) Prims.op_Negation))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _49_47 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _102_15 = (FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_102_15, uv)))))
end))))

let new_evar = (fun r binders t -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Absyn_Syntax.is_null_binder x) Prims.op_Negation))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _49_60 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _102_24 = (let _102_23 = (FStar_Absyn_Syntax.mk_Total t)
in (binders, _102_23))
in (FStar_Absyn_Syntax.mk_Typ_fun _102_24 None r))
in (let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _49_66 -> begin
(let _102_25 = (FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_102_25, uv))
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

let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

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
| KProb (_49_83) -> begin
_49_83
end))

let ___TProb____0 = (fun projectee -> (match (projectee) with
| TProb (_49_86) -> begin
_49_86
end))

let ___EProb____0 = (fun projectee -> (match (projectee) with
| EProb (_49_89) -> begin
_49_89
end))

let ___CProb____0 = (fun projectee -> (match (projectee) with
| CProb (_49_92) -> begin
_49_92
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
| UK (_49_95) -> begin
_49_95
end))

let ___UT____0 = (fun projectee -> (match (projectee) with
| UT (_49_98) -> begin
_49_98
end))

let ___UE____0 = (fun projectee -> (match (projectee) with
| UE (_49_101) -> begin
_49_101
end))

type worklist =
{attempting : probs; wl_deferred : (Prims.int * Prims.string * prob) Prims.list; subst : uvi Prims.list; ctr : Prims.int; slack_vars : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_Tc_Env.env}

let is_Mkworklist = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

type deferred =
{carry : (Prims.string * prob) Prims.list; slack : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list}

let is_Mkdeferred = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdeferred"))))

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
| Success (_49_116) -> begin
_49_116
end))

let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_49_119) -> begin
_49_119
end))

let rel_to_string = (fun _49_1 -> (match (_49_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string = (fun env _49_2 -> (match (_49_2) with
| KProb (p) -> begin
(let _102_227 = (FStar_Absyn_Print.kind_to_string p.lhs)
in (let _102_226 = (FStar_Absyn_Print.kind_to_string p.rhs)
in (FStar_Util.format3 "\t%s\n\t\t%s\n\t%s" _102_227 (rel_to_string p.relation) _102_226)))
end
| TProb (p) -> begin
(let _102_240 = (let _102_239 = (FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _102_238 = (let _102_237 = (FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _102_236 = (let _102_235 = (let _102_234 = (FStar_All.pipe_right p.reason FStar_List.hd)
in (let _102_233 = (let _102_232 = (FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _102_231 = (let _102_230 = (FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _102_229 = (let _102_228 = (FStar_Tc_Normalize.formula_norm_to_string env (Prims.fst p.logical_guard))
in (_102_228)::[])
in (_102_230)::_102_229))
in (_102_232)::_102_231))
in (_102_234)::_102_233))
in ((rel_to_string p.relation))::_102_235)
in (_102_237)::_102_236))
in (_102_239)::_102_238))
in (FStar_Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _102_240))
end
| EProb (p) -> begin
(let _102_242 = (FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _102_241 = (FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _102_242 (rel_to_string p.relation) _102_241)))
end
| CProb (p) -> begin
(let _102_244 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _102_243 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _102_244 (rel_to_string p.relation) _102_243)))
end))

let uvi_to_string = (fun env uvi -> (let str = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _102_250 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _102_250 FStar_Util.string_of_int))
end)
in (match (uvi) with
| UK (u, _49_141) -> begin
(let _102_251 = (str u)
in (FStar_All.pipe_right _102_251 (FStar_Util.format1 "UK %s")))
end
| UT ((u, _49_146), t) -> begin
(let _102_254 = (str u)
in (FStar_All.pipe_right _102_254 (fun x -> (let _102_253 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "UT %s %s" x _102_253)))))
end
| UE ((u, _49_154), _49_157) -> begin
(let _102_255 = (str u)
in (FStar_All.pipe_right _102_255 (FStar_Util.format1 "UE %s")))
end)))

let invert_rel = (fun _49_3 -> (match (_49_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun p -> (let _49_165 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _49_165.element; logical_guard = _49_165.logical_guard; scope = _49_165.scope; reason = _49_165.reason; loc = _49_165.loc; rank = _49_165.rank}))

let maybe_invert = (fun p -> if (p.relation = SUBINV) then begin
(invert p)
end else begin
p
end)

let maybe_invert_p = (fun _49_4 -> (match (_49_4) with
| KProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _102_262 -> KProb (_102_262)))
end
| TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _102_263 -> TProb (_102_263)))
end
| EProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _102_264 -> EProb (_102_264)))
end
| CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _102_265 -> CProb (_102_265)))
end))

let vary_rel = (fun rel _49_5 -> (match (_49_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel = (fun _49_6 -> (match (_49_6) with
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

let p_reason = (fun _49_7 -> (match (_49_7) with
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

let p_loc = (fun _49_8 -> (match (_49_8) with
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

let p_context = (fun _49_9 -> (match (_49_9) with
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

let p_guard = (fun _49_10 -> (match (_49_10) with
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

let p_scope = (fun _49_11 -> (match (_49_11) with
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

let p_invert = (fun _49_12 -> (match (_49_12) with
| KProb (p) -> begin
(FStar_All.pipe_left (fun _102_284 -> KProb (_102_284)) (invert p))
end
| TProb (p) -> begin
(FStar_All.pipe_left (fun _102_285 -> TProb (_102_285)) (invert p))
end
| EProb (p) -> begin
(FStar_All.pipe_left (fun _102_286 -> EProb (_102_286)) (invert p))
end
| CProb (p) -> begin
(FStar_All.pipe_left (fun _102_287 -> CProb (_102_287)) (invert p))
end))

let is_top_level_prob = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _102_297 = (new_tvar (p_loc orig) scope FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _102_297; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun env lhs rel rhs elt loc reason -> (let _102_307 = (let _102_306 = (FStar_Tc_Env.get_range env)
in (let _102_305 = (FStar_Tc_Env.binders env)
in (new_tvar _102_306 _102_305 FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _102_307; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun orig lhs rel rhs elt reason -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun problem x phi -> (match (problem.element) with
| None -> begin
(FStar_Absyn_Util.close_forall (((FStar_Absyn_Syntax.v_binder x))::[]) phi)
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
in (let _49_284 = (p_guard prob)
in (match (_49_284) with
| (_49_282, uv) -> begin
(let _49_292 = (match ((let _102_327 = (FStar_Absyn_Util.compress_typ uv)
in _102_327.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uvar, k) -> begin
(let phi = (FStar_Absyn_Util.close_for_kind phi k)
in (FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _49_291 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (match (uvis) with
| [] -> begin
wl
end
| _49_296 -> begin
(let _49_297 = if (FStar_All.pipe_left (FStar_Tc_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _102_329 = (let _102_328 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _102_328 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Extending solution: %s\n" _102_329))
end else begin
()
end
in (let _49_299 = wl
in {attempting = _49_299.attempting; wl_deferred = _49_299.wl_deferred; subst = (FStar_List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _49_299.slack_vars; defer_ok = _49_299.defer_ok; smt_ok = _49_299.smt_ok; tcenv = _49_299.tcenv}))
end))
end))))

let extend_solution = (fun sol wl -> (let _49_303 = wl
in {attempting = _49_303.attempting; wl_deferred = _49_303.wl_deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _49_303.slack_vars; defer_ok = _49_303.defer_ok; smt_ok = _49_303.smt_ok; tcenv = _49_303.tcenv}))

let solve_prob = (fun prob logical_guard uvis wl -> (solve_prob' false prob logical_guard uvis wl))

let explain = (fun env d s -> (let _102_350 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _102_349 = (prob_to_string env d)
in (let _102_348 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _102_350 _102_349 _102_348 s)))))

let empty_worklist = (fun env -> {attempting = []; wl_deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton = (fun env prob -> (let _49_315 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _49_315.wl_deferred; subst = _49_315.subst; ctr = _49_315.ctr; slack_vars = _49_315.slack_vars; defer_ok = _49_315.defer_ok; smt_ok = _49_315.smt_ok; tcenv = _49_315.tcenv}))

let wl_of_guard = (fun env g -> (let _49_319 = (empty_worklist env)
in (let _102_361 = (FStar_List.map Prims.snd g.carry)
in {attempting = _102_361; wl_deferred = _49_319.wl_deferred; subst = _49_319.subst; ctr = _49_319.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _49_319.smt_ok; tcenv = _49_319.tcenv})))

let defer = (fun reason prob wl -> (let _49_324 = wl
in {attempting = _49_324.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; subst = _49_324.subst; ctr = _49_324.ctr; slack_vars = _49_324.slack_vars; defer_ok = _49_324.defer_ok; smt_ok = _49_324.smt_ok; tcenv = _49_324.tcenv}))

let attempt = (fun probs wl -> (let _49_328 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _49_328.wl_deferred; subst = _49_328.subst; ctr = _49_328.ctr; slack_vars = _49_328.slack_vars; defer_ok = _49_328.defer_ok; smt_ok = _49_328.smt_ok; tcenv = _49_328.tcenv}))

let add_slack_mul = (fun slack wl -> (let _49_332 = wl
in {attempting = _49_332.attempting; wl_deferred = _49_332.wl_deferred; subst = _49_332.subst; ctr = _49_332.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _49_332.defer_ok; smt_ok = _49_332.smt_ok; tcenv = _49_332.tcenv}))

let add_slack_add = (fun slack wl -> (let _49_336 = wl
in {attempting = _49_336.attempting; wl_deferred = _49_336.wl_deferred; subst = _49_336.subst; ctr = _49_336.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _49_336.defer_ok; smt_ok = _49_336.smt_ok; tcenv = _49_336.tcenv}))

let giveup = (fun env reason prob -> (let _49_341 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_386 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _102_386))
end else begin
()
end
in Failed ((prob, reason))))

let commit = (fun env uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _49_13 -> (match (_49_13) with
| UK (u, k) -> begin
(FStar_Absyn_Util.unchecked_unify u k)
end
| UT ((u, k), t) -> begin
(FStar_Absyn_Util.unchecked_unify u t)
end
| UE ((u, _49_358), e) -> begin
(FStar_Absyn_Util.unchecked_unify u e)
end)))))

let find_uvar_k = (fun uv s -> (FStar_Util.find_map s (fun _49_14 -> (match (_49_14) with
| UK (u, t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _49_371 -> begin
None
end))))

let find_uvar_t = (fun uv s -> (FStar_Util.find_map s (fun _49_15 -> (match (_49_15) with
| UT ((u, _49_377), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _49_383 -> begin
None
end))))

let find_uvar_e = (fun uv s -> (FStar_Util.find_map s (fun _49_16 -> (match (_49_16) with
| UE ((u, _49_389), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _49_395 -> begin
None
end))))

let simplify_formula = (fun env f -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _102_417 = (let _102_416 = (norm_targ env t)
in (FStar_All.pipe_left (fun _102_415 -> FStar_Util.Inl (_102_415)) _102_416))
in (_102_417, (Prims.snd a)))
end
| FStar_Util.Inr (v) -> begin
(let _102_420 = (let _102_419 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env v)
in (FStar_All.pipe_left (fun _102_418 -> FStar_Util.Inr (_102_418)) _102_419))
in (_102_420, (Prims.snd a)))
end))

let whnf = (fun env t -> (let _102_425 = (FStar_Tc_Normalize.whnf env t)
in (FStar_All.pipe_right _102_425 FStar_Absyn_Util.compress_typ)))

let sn = (fun env t -> (let _102_430 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env t)
in (FStar_All.pipe_right _102_430 FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _49_17 -> (match (_49_17) with
| (FStar_Util.Inl (a), imp) -> begin
(let _102_436 = (let _102_435 = (let _49_417 = a
in (let _102_434 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _49_417.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _102_434; FStar_Absyn_Syntax.p = _49_417.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_102_435))
in (_102_436, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _102_439 = (let _102_438 = (let _49_423 = x
in (let _102_437 = (norm_targ env x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _49_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _102_437; FStar_Absyn_Syntax.p = _49_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_102_438))
in (_102_439, imp))
end)))))

let whnf_k = (fun env k -> (let _102_444 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env k)
in (FStar_All.pipe_right _102_444 FStar_Absyn_Util.compress_kind)))

let whnf_e = (fun env e -> (let _102_449 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env e)
in (FStar_All.pipe_right _102_449 FStar_Absyn_Util.compress_exp)))

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
(let k = (let _102_456 = (FStar_Absyn_Util.subst_of_list formals actuals)
in (FStar_Absyn_Util.subst_kind _102_456 body))
in (compress_k env wl k))
end
| _49_446 -> begin
if ((FStar_List.length actuals) = 0) then begin
(compress_k env wl k')
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end)
end
| _49_448 -> begin
k
end)))

let rec compress = (fun env wl t -> (let t = (let _102_463 = (FStar_Absyn_Util.unmeta_typ t)
in (whnf env _102_463))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _49_455) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _49_471); FStar_Absyn_Syntax.tk = _49_468; FStar_Absyn_Syntax.pos = _49_466; FStar_Absyn_Syntax.fvs = _49_464; FStar_Absyn_Syntax.uvs = _49_462}, args) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _49_482 -> begin
t
end)
end
| _49_484 -> begin
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
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _49_506); FStar_Absyn_Syntax.tk = _49_503; FStar_Absyn_Syntax.pos = _49_501; FStar_Absyn_Syntax.fvs = _49_499; FStar_Absyn_Syntax.uvs = _49_497}, args) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.FStar_Absyn_Syntax.pos))
end)
end
| _49_518 -> begin
e
end)))

let normalize_refinement = (fun steps env wl t0 -> (let _102_478 = (compress env wl t0)
in (FStar_Tc_Normalize.normalize_refinement steps env _102_478)))

let base_and_refinement = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
if norm then begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, phi); FStar_Absyn_Syntax.tk = _49_540; FStar_Absyn_Syntax.pos = _49_538; FStar_Absyn_Syntax.fvs = _49_536; FStar_Absyn_Syntax.uvs = _49_534} -> begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _102_491 = (let _102_490 = (FStar_Absyn_Print.typ_to_string tt)
in (let _102_489 = (FStar_Absyn_Print.tag_of_typ tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _102_490 _102_489)))
in (FStar_All.failwith _102_491))
end)
end
end
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _49_555 = (let _102_492 = (normalize_refinement [] env wl t1)
in (aux true _102_492))
in (match (_49_555) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _49_558 -> begin
(t2', refinement)
end)
end))
end
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (FStar_Absyn_Syntax.Typ_ascribed (_)) | (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_meta (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _102_495 = (let _102_494 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_493 = (FStar_Absyn_Print.tag_of_typ t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _102_494 _102_493)))
in (FStar_All.failwith _102_495))
end))
in (let _102_496 = (compress env wl t1)
in (aux false _102_496))))

let unrefine = (fun env t -> (let _102_501 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _102_501 Prims.fst)))

let trivial_refinement = (fun t -> (let _102_503 = (FStar_Absyn_Util.gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in (_102_503, FStar_Absyn_Util.t_true)))

let as_refinement = (fun env wl t -> (let _49_589 = (base_and_refinement env wl t)
in (match (_49_589) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun _49_597 -> (match (_49_597) with
| (t_base, refopt) -> begin
(let _49_605 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_49_605) with
| (y, phi) -> begin
(FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun env wl uk t -> (let uvs = (FStar_Absyn_Util.uvars_in_typ t)
in (let _102_523 = (FStar_All.pipe_right uvs.FStar_Absyn_Syntax.uvars_t FStar_Util.set_elements)
in (FStar_All.pipe_right _102_523 (FStar_Util.for_some (fun _49_616 -> (match (_49_616) with
| (uvt, _49_615) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(FStar_Unionfind.equivalent uvt (Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_49_629, t); FStar_Absyn_Syntax.tk = _49_627; FStar_Absyn_Syntax.pos = _49_625; FStar_Absyn_Syntax.fvs = _49_623; FStar_Absyn_Syntax.uvs = _49_621} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))

let occurs_check = (fun env wl uk t -> (let occurs_ok = (not ((occurs env wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _102_536 = (let _102_535 = (FStar_Absyn_Print.uvar_t_to_string uk)
in (let _102_534 = (FStar_Absyn_Print.typ_to_string t)
in (let _102_533 = (let _102_532 = (FStar_All.pipe_right wl.subst (FStar_List.map (uvi_to_string env)))
in (FStar_All.pipe_right _102_532 (FStar_String.concat ", ")))
in (FStar_Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _102_535 _102_534 _102_533))))
in Some (_102_536))
end
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun env wl uk fvs t -> (let fvs_t = (FStar_Absyn_Util.freevars_typ t)
in (let _49_650 = (occurs_check env wl uk t)
in (match (_49_650) with
| (occurs_ok, msg) -> begin
(let _102_547 = (FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _102_547, (msg, fvs, fvs_t)))
end))))

let occurs_check_e = (fun env ut e -> (let uvs = (FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((FStar_Util.set_mem ut uvs.FStar_Absyn_Syntax.uvars_e)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _102_559 = (let _102_558 = (FStar_Absyn_Print.uvar_e_to_string ut)
in (let _102_557 = (let _102_555 = (let _102_554 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _102_554 (FStar_List.map FStar_Absyn_Print.uvar_e_to_string)))
in (FStar_All.pipe_right _102_555 (FStar_String.concat ", ")))
in (let _102_556 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _102_558 _102_557 _102_556))))
in Some (_102_559))
end
in (occurs_ok, msg)))))

let intersect_vars = (fun v1 v2 -> (let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _102_566 = (let _102_565 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _102_564 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _102_565; FStar_Absyn_Syntax.fxvs = _102_564}))
in (FStar_Absyn_Syntax.binders_of_freevars _102_566)))))

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun ax1 ax2 -> (match (((Prims.fst ax1), (Prims.fst ax2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Util.bvar_eq x y)
end
| _49_676 -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((FStar_All.pipe_left Prims.fst hd)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _49_688; FStar_Absyn_Syntax.pos = _49_686; FStar_Absyn_Syntax.fvs = _49_684; FStar_Absyn_Syntax.uvs = _49_682}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _49_18 -> (match (_49_18) with
| (FStar_Util.Inl (b), _49_697) -> begin
(FStar_Absyn_Syntax.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)
end
| _49_700 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inl (a), (Prims.snd hd)))
end
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (x); FStar_Absyn_Syntax.tk = _49_708; FStar_Absyn_Syntax.pos = _49_706; FStar_Absyn_Syntax.fvs = _49_704; FStar_Absyn_Syntax.uvs = _49_702}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _49_19 -> (match (_49_19) with
| (FStar_Util.Inr (y), _49_717) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _49_720 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inr (x), (Prims.snd hd)))
end
end
| _49_722 -> begin
None
end)))

let rec pat_vars = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _49_731 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_582 = (FStar_Absyn_Print.arg_to_string hd)
in (FStar_Util.print1 "Not a pattern: %s\n" _102_582))
end else begin
()
end
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
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, k); FStar_Absyn_Syntax.tk = _49_747; FStar_Absyn_Syntax.pos = _49_745; FStar_Absyn_Syntax.fvs = _49_743; FStar_Absyn_Syntax.uvs = _49_741}, args) -> begin
(t, uv, k, args)
end
| _49_757 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, k) -> begin
(e, uv, k, [])
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, k); FStar_Absyn_Syntax.tk = _49_770; FStar_Absyn_Syntax.pos = _49_768; FStar_Absyn_Syntax.fvs = _49_766; FStar_Absyn_Syntax.uvs = _49_764}, args) -> begin
(e, uv, k, args)
end
| _49_780 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun env t -> (let _49_787 = (destruct_flex_t t)
in (match (_49_787) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _49_791 -> begin
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

let head_match = (fun _49_20 -> (match (_49_20) with
| MisMatch -> begin
MisMatch
end
| _49_795 -> begin
HeadMatch
end))

let rec head_matches = (fun t1 t2 -> (match ((let _102_599 = (let _102_596 = (FStar_Absyn_Util.unmeta_typ t1)
in _102_596.FStar_Absyn_Syntax.n)
in (let _102_598 = (let _102_597 = (FStar_Absyn_Util.unmeta_typ t2)
in _102_597.FStar_Absyn_Syntax.n)
in (_102_599, _102_598)))) with
| (FStar_Absyn_Syntax.Typ_btvar (x), FStar_Absyn_Syntax.Typ_btvar (y)) -> begin
if (FStar_Absyn_Util.bvar_eq x y) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
if (FStar_Absyn_Util.fvar_eq f g) then begin
FullMatch
end else begin
MisMatch
end
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), FStar_Absyn_Syntax.Typ_const (_))) | ((FStar_Absyn_Syntax.Typ_const (_), FStar_Absyn_Syntax.Typ_btvar (_))) -> begin
MisMatch
end
| (FStar_Absyn_Syntax.Typ_refine (x, _49_824), FStar_Absyn_Syntax.Typ_refine (y, _49_829)) -> begin
(let _102_600 = (head_matches x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _102_600 head_match))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _49_835), _49_839) -> begin
(let _102_601 = (head_matches x.FStar_Absyn_Syntax.sort t2)
in (FStar_All.pipe_right _102_601 head_match))
end
| (_49_842, FStar_Absyn_Syntax.Typ_refine (x, _49_845)) -> begin
(let _102_602 = (head_matches t1 x.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _102_602 head_match))
end
| (FStar_Absyn_Syntax.Typ_fun (_49_850), FStar_Absyn_Syntax.Typ_fun (_49_853)) -> begin
HeadMatch
end
| (FStar_Absyn_Syntax.Typ_app (head, _49_858), FStar_Absyn_Syntax.Typ_app (head', _49_863)) -> begin
(head_matches head head')
end
| (FStar_Absyn_Syntax.Typ_app (head, _49_869), _49_873) -> begin
(head_matches head t2)
end
| (_49_876, FStar_Absyn_Syntax.Typ_app (head, _49_879)) -> begin
(head_matches t1 head)
end
| (FStar_Absyn_Syntax.Typ_uvar (uv, _49_885), FStar_Absyn_Syntax.Typ_uvar (uv', _49_890)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (_49_895, FStar_Absyn_Syntax.Typ_lam (_49_897)) -> begin
HeadMatch
end
| _49_901 -> begin
MisMatch
end))

let head_matches_delta = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun _49_912 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 2) then begin
(fail ())
end else begin
if (d = 1) then begin
(let t1' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t1)
in (let t2' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t2)
in (aux 2 t1' t2')))
end else begin
(let t1 = (normalize_refinement [] env wl t1)
in (let t2 = (normalize_refinement [] env wl t2)
in (aux (d + 1) t1 t2)))
end
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux 0 t1 t2)))))

let decompose_binder = (fun bs v_ktec rebuild_base -> (let fail = (fun _49_928 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let rebuild = (fun ktecs -> (let rec aux = (fun new_bs bs ktecs -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (FStar_List.rev new_bs) ktec)
end
| ((FStar_Util.Inl (a), imp)::rest, FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((FStar_Util.Inl ((let _49_950 = a
in {FStar_Absyn_Syntax.v = _49_950.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _49_950.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((FStar_Util.Inr (x), imp)::rest, FStar_Absyn_Syntax.T (t, _49_961)::rest') -> begin
(aux (((FStar_Util.Inr ((let _49_966 = x
in {FStar_Absyn_Syntax.v = _49_966.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _49_966.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _49_969 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun _49_973 _49_21 -> (match (_49_973) with
| (binders, b_ktecs) -> begin
(match (_49_21) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, v_ktec))::b_ktecs))
end
| hd::rest -> begin
(let bopt = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
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
in (let _102_656 = (mk_b_ktecs ([], []) bs)
in (rebuild, _102_656))))))

let rec decompose_kind = (fun env k -> (let fail = (fun _49_992 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let k0 = k
in (let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun _49_22 -> (match (_49_22) with
| [] -> begin
k
end
| _49_1000 -> begin
(fail ())
end))
in (rebuild, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(decompose_binder bs (FStar_Absyn_Syntax.K (k)) (fun bs _49_23 -> (match (_49_23) with
| FStar_Absyn_Syntax.K (k) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.FStar_Absyn_Syntax.pos)
end
| _49_1011 -> begin
(fail ())
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_49_1013, k) -> begin
(decompose_kind env k)
end
| _49_1018 -> begin
(FStar_All.failwith "Impossible")
end)))))

let rec decompose_typ = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((FStar_Util.Inl (_49_1033), imp), FStar_Absyn_Syntax.T (t, _49_1039)) -> begin
(FStar_Util.Inl (t), imp)
end
| ((FStar_Util.Inr (_49_1044), imp), FStar_Absyn_Syntax.E (e)) -> begin
(FStar_Util.Inr (e), imp)
end
| _49_1052 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (FStar_All.pipe_right args (FStar_List.map (fun _49_24 -> (match (_49_24) with
| (FStar_Util.Inl (t), _49_1058) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _49_1063) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _49_1078 = (decompose_binder bs (FStar_Absyn_Syntax.C (c)) (fun bs _49_25 -> (match (_49_25) with
| FStar_Absyn_Syntax.C (c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end
| _49_1075 -> begin
(FStar_All.failwith "Bad reconstruction")
end)))
in (match (_49_1078) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _49_1080 -> begin
(let rebuild = (fun _49_26 -> (match (_49_26) with
| [] -> begin
t
end
| _49_1084 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

let un_T = (fun _49_27 -> (match (_49_27) with
| FStar_Absyn_Syntax.T (x, _49_1090) -> begin
x
end
| _49_1094 -> begin
(FStar_All.failwith "impossible")
end))

let arg_of_ktec = (fun _49_28 -> (match (_49_28) with
| FStar_Absyn_Syntax.T (t, _49_1098) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Absyn_Syntax.E (e) -> begin
(FStar_Absyn_Syntax.varg e)
end
| _49_1104 -> begin
(FStar_All.failwith "Impossible")
end))

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_49_1117, variance, FStar_Absyn_Syntax.K (ki)) -> begin
(let _49_1124 = (new_kvar r scope)
in (match (_49_1124) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _102_739 = (let _102_738 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (FStar_All.pipe_left (fun _102_737 -> KProb (_102_737)) _102_738))
in (FStar_Absyn_Syntax.K (gi_xs), _102_739)))
end))
end
| (_49_1127, variance, FStar_Absyn_Syntax.T (ti, kopt)) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _49_1140 = (new_tvar r scope k)
in (match (_49_1140) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _102_742 = (let _102_741 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _102_740 -> TProb (_102_740)) _102_741))
in (FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _102_742)))
end)))
end
| (_49_1143, variance, FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (FStar_Tc_Recheck.recompute_typ ei)
in (let _49_1151 = (new_evar r scope t)
in (match (_49_1151) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _102_745 = (let _102_744 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (FStar_All.pipe_left (fun _102_743 -> EProb (_102_743)) _102_744))
in (FStar_Absyn_Syntax.E (gi_xs), _102_745)))
end)))
end
| (_49_1154, _49_1156, FStar_Absyn_Syntax.C (_49_1158)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _49_1234 = (match (q) with
| (bopt, variance, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Total (ti); FStar_Absyn_Syntax.tk = _49_1178; FStar_Absyn_Syntax.pos = _49_1176; FStar_Absyn_Syntax.fvs = _49_1174; FStar_Absyn_Syntax.uvs = _49_1172})) -> begin
(match ((sub_prob scope args (bopt, variance, FStar_Absyn_Syntax.T ((ti, Some (FStar_Absyn_Syntax.ktype)))))) with
| (FStar_Absyn_Syntax.T (gi_xs, _49_1186), prob) -> begin
(let _102_754 = (let _102_753 = (FStar_Absyn_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _102_752 -> FStar_Absyn_Syntax.C (_102_752)) _102_753))
in (_102_754, (prob)::[]))
end
| _49_1192 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_49_1194, _49_1196, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (c); FStar_Absyn_Syntax.tk = _49_1204; FStar_Absyn_Syntax.pos = _49_1202; FStar_Absyn_Syntax.fvs = _49_1200; FStar_Absyn_Syntax.uvs = _49_1198})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map (fun _49_29 -> (match (_49_29) with
| (FStar_Util.Inl (t), _49_1214) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _49_1219) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, FStar_Absyn_Syntax.T ((c.FStar_Absyn_Syntax.result_typ, Some (FStar_Absyn_Syntax.ktype)))))::components
in (let _49_1225 = (let _102_756 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _102_756 FStar_List.unzip))
in (match (_49_1225) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _102_761 = (let _102_760 = (let _102_757 = (FStar_List.hd ktecs)
in (FStar_All.pipe_right _102_757 un_T))
in (let _102_759 = (let _102_758 = (FStar_List.tl ktecs)
in (FStar_All.pipe_right _102_758 (FStar_List.map arg_of_ktec)))
in {FStar_Absyn_Syntax.effect_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _102_760; FStar_Absyn_Syntax.effect_args = _102_759; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _102_761))
in (FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _49_1228 -> begin
(let _49_1231 = (sub_prob scope args q)
in (match (_49_1231) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_49_1234) with
| (ktec, probs) -> begin
(let _49_1247 = (match (q) with
| (Some (b), _49_1238, _49_1240) -> begin
(let _102_763 = (let _102_762 = (FStar_Absyn_Util.arg_of_non_null_binder b)
in (_102_762)::args)
in (Some (b), (b)::scope, _102_763))
end
| _49_1243 -> begin
(None, scope, args)
end)
in (match (_49_1247) with
| (bopt, scope, args) -> begin
(let _49_1251 = (aux scope args qs)
in (match (_49_1251) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _102_766 = (let _102_765 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_102_765)
in (FStar_Absyn_Util.mk_conj_l _102_766))
end
| Some (b) -> begin
(let _102_770 = (let _102_769 = (FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _102_768 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_102_769)::_102_768))
in (FStar_Absyn_Util.mk_conj_l _102_770))
end)
in ((FStar_List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); upper : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); flag : Prims.bool FStar_ST.ref}

let is_Mkslack = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkslack"))))

let fix_slack_uv = (fun _49_1264 mul -> (match (_49_1264) with
| (uv, k) -> begin
(let inst = if mul then begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_true k)
end else begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_false k)
end
in (FStar_Absyn_Util.unchecked_unify uv inst))
end))

let fix_slack_vars = (fun slack -> (FStar_All.pipe_right slack (FStar_List.iter (fun _49_1270 -> (match (_49_1270) with
| (mul, s) -> begin
(match ((let _102_788 = (FStar_Absyn_Util.compress_typ s)
in _102_788.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(fix_slack_uv (uv, k) mul)
end
| _49_1276 -> begin
()
end)
end)))))

let fix_slack = (fun slack -> (let _49_1284 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.lower))
in (match (_49_1284) with
| (_49_1279, ul, kl, _49_1283) -> begin
(let _49_1291 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.upper))
in (match (_49_1291) with
| (_49_1286, uh, kh, _49_1290) -> begin
(let _49_1292 = (fix_slack_uv (ul, kl) false)
in (let _49_1294 = (fix_slack_uv (uh, kh) true)
in (let _49_1296 = (FStar_ST.op_Colon_Equals slack.flag true)
in (FStar_Absyn_Util.mk_conj (Prims.fst slack.lower) (Prims.fst slack.upper)))))
end))
end)))

let new_slack_var = (fun env slack -> (let xs = (let _102_796 = (let _102_795 = (destruct_flex_pattern env (Prims.snd slack.lower))
in (FStar_All.pipe_right _102_795 Prims.snd))
in (FStar_All.pipe_right _102_796 FStar_Util.must))
in (let _102_797 = (new_tvar (Prims.fst slack.lower).FStar_Absyn_Syntax.pos xs FStar_Absyn_Syntax.ktype)
in (_102_797, xs))))

let new_slack_formula = (fun p env wl xs low high -> (let _49_1309 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_49_1309) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _49_1313 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_49_1313) with
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
in (let _102_807 = (let _102_806 = (let _102_805 = (let _102_804 = (FStar_Util.mk_ref false)
in (low, high, _102_804))
in FStar_Absyn_Syntax.Meta_slack_formula (_102_805))
in (FStar_Absyn_Syntax.mk_Typ_meta _102_806))
in (_102_807, wl)))))
end)))
end)))

let destruct_slack = (fun env wl phi -> (let rec destruct = (fun conn_lid mk_conn phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _49_1337; FStar_Absyn_Syntax.pos = _49_1335; FStar_Absyn_Syntax.fvs = _49_1333; FStar_Absyn_Syntax.uvs = _49_1331}, (FStar_Util.Inl (lhs), _49_1349)::(FStar_Util.Inl (rhs), _49_1344)::[]) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
Some ((lhs, rhs))
end
| _49_1375 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some (rest, uvar) -> begin
(let _102_831 = (let _102_830 = (mk_conn lhs rest)
in (_102_830, uvar))
in Some (_102_831))
end)
end))
end
| _49_1382 -> begin
None
end))
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (phi1, phi2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _102_832 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_102_832))
end else begin
(let low = (let _102_833 = (compress env wl phi1)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.or_lid FStar_Absyn_Util.mk_disj) _102_833))
in (let hi = (let _102_834 = (compress env wl phi2)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.and_lid FStar_Absyn_Util.mk_disj) _102_834))
in (match ((low, hi)) with
| (None, None) -> begin
(let _49_1395 = (FStar_ST.op_Colon_Equals flag true)
in (let _102_835 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_102_835)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(FStar_All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
FStar_Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end
end
| _49_1413 -> begin
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
| (FStar_Absyn_Syntax.Typ_uvar (u1, _49_1430), FStar_Absyn_Syntax.Typ_uvar (u2, _49_1435)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Absyn_Syntax.Typ_app (h1, args1), FStar_Absyn_Syntax.Typ_app (h2, args2)) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _49_1449 -> begin
false
end))))
and eq_exp = (fun e1 e2 -> (let e1 = (FStar_Absyn_Util.compress_exp e1)
in (let e2 = (FStar_Absyn_Util.compress_exp e2)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (a), FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _49_1461), FStar_Absyn_Syntax.Exp_fvar (g, _49_1466)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Exp_constant (c), FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (FStar_Absyn_Syntax.Exp_app (h1, args1), FStar_Absyn_Syntax.Exp_app (h2, args2)) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _49_1485 -> begin
false
end))))
and eq_args = (fun a1 a2 -> if ((FStar_List.length a1) = (FStar_List.length a2)) then begin
(FStar_List.forall2 (fun a1 a2 -> (match ((a1, a2)) with
| ((FStar_Util.Inl (t), _49_1493), (FStar_Util.Inl (s), _49_1498)) -> begin
(eq_typ t s)
end
| ((FStar_Util.Inr (e), _49_1504), (FStar_Util.Inr (f), _49_1509)) -> begin
(eq_exp e f)
end
| _49_1513 -> begin
false
end)) a1 a2)
end else begin
false
end)

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
(let _102_865 = (let _49_1518 = p
in (let _102_863 = (compress_k wl.tcenv wl p.lhs)
in (let _102_862 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _102_863; relation = _49_1518.relation; rhs = _102_862; element = _49_1518.element; logical_guard = _49_1518.logical_guard; scope = _49_1518.scope; reason = _49_1518.reason; loc = _49_1518.loc; rank = _49_1518.rank})))
in (FStar_All.pipe_right _102_865 (fun _102_864 -> KProb (_102_864))))
end
| TProb (p) -> begin
(let _102_869 = (let _49_1522 = p
in (let _102_867 = (compress wl.tcenv wl p.lhs)
in (let _102_866 = (compress wl.tcenv wl p.rhs)
in {lhs = _102_867; relation = _49_1522.relation; rhs = _102_866; element = _49_1522.element; logical_guard = _49_1522.logical_guard; scope = _49_1522.scope; reason = _49_1522.reason; loc = _49_1522.loc; rank = _49_1522.rank})))
in (FStar_All.pipe_right _102_869 (fun _102_868 -> TProb (_102_868))))
end
| EProb (p) -> begin
(let _102_873 = (let _49_1526 = p
in (let _102_871 = (compress_e wl.tcenv wl p.lhs)
in (let _102_870 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _102_871; relation = _49_1526.relation; rhs = _102_870; element = _49_1526.element; logical_guard = _49_1526.logical_guard; scope = _49_1526.scope; reason = _49_1526.reason; loc = _49_1526.loc; rank = _49_1526.rank})))
in (FStar_All.pipe_right _102_873 (fun _102_872 -> EProb (_102_872))))
end
| CProb (_49_1529) -> begin
p
end))

let rank = (fun wl prob -> (let prob = (let _102_878 = (compress_prob wl prob)
in (FStar_All.pipe_right _102_878 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.FStar_Absyn_Syntax.n, kp.rhs.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_uvar (_49_1537), FStar_Absyn_Syntax.Kind_uvar (_49_1540)) -> begin
flex_flex
end
| (FStar_Absyn_Syntax.Kind_uvar (_49_1544), _49_1547) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
flex_rigid
end
end
| (_49_1550, FStar_Absyn_Syntax.Kind_uvar (_49_1552)) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
rigid_flex
end
end
| (_49_1556, _49_1558) -> begin
rigid_rigid
end)
in (let _102_880 = (FStar_All.pipe_right (let _49_1561 = kp
in {lhs = _49_1561.lhs; relation = _49_1561.relation; rhs = _49_1561.rhs; element = _49_1561.element; logical_guard = _49_1561.logical_guard; scope = _49_1561.scope; reason = _49_1561.reason; loc = _49_1561.loc; rank = Some (rank)}) (fun _102_879 -> KProb (_102_879)))
in (rank, _102_880)))
end
| TProb (tp) -> begin
(let _49_1568 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_49_1568) with
| (lh, _49_1567) -> begin
(let _49_1572 = (FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_49_1572) with
| (rh, _49_1571) -> begin
(let _49_1628 = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_49_1574), FStar_Absyn_Syntax.Typ_uvar (_49_1577)) -> begin
(flex_flex, tp)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Absyn_Syntax.Typ_uvar (_49_1593), _49_1596) -> begin
(let _49_1600 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_49_1600) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _49_1603 -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _102_882 = (let _49_1605 = tp
in (let _102_881 = (force_refinement (b, ref_opt))
in {lhs = _49_1605.lhs; relation = _49_1605.relation; rhs = _102_881; element = _49_1605.element; logical_guard = _49_1605.logical_guard; scope = _49_1605.scope; reason = _49_1605.reason; loc = _49_1605.loc; rank = _49_1605.rank}))
in (rank, _102_882)))
end)
end))
end
| (_49_1608, FStar_Absyn_Syntax.Typ_uvar (_49_1610)) -> begin
(let _49_1615 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_49_1615) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _49_1618 -> begin
(let _102_884 = (let _49_1619 = tp
in (let _102_883 = (force_refinement (b, ref_opt))
in {lhs = _102_883; relation = _49_1619.relation; rhs = _49_1619.rhs; element = _49_1619.element; logical_guard = _49_1619.logical_guard; scope = _49_1619.scope; reason = _49_1619.reason; loc = _49_1619.loc; rank = _49_1619.rank}))
in (refine_flex, _102_884))
end)
end))
end
| (_49_1622, _49_1624) -> begin
(rigid_rigid, tp)
end)
in (match (_49_1628) with
| (rank, tp) -> begin
(let _102_886 = (FStar_All.pipe_right (let _49_1629 = tp
in {lhs = _49_1629.lhs; relation = _49_1629.relation; rhs = _49_1629.rhs; element = _49_1629.element; logical_guard = _49_1629.logical_guard; scope = _49_1629.scope; reason = _49_1629.reason; loc = _49_1629.loc; rank = Some (rank)}) (fun _102_885 -> TProb (_102_885)))
in (rank, _102_886))
end))
end))
end))
end
| EProb (ep) -> begin
(let _49_1636 = (FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_49_1636) with
| (lh, _49_1635) -> begin
(let _49_1640 = (FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_49_1640) with
| (rh, _49_1639) -> begin
(let rank = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_uvar (_49_1642), FStar_Absyn_Syntax.Exp_uvar (_49_1645)) -> begin
flex_flex
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_49_1661, _49_1663) -> begin
rigid_rigid
end)
in (let _102_888 = (FStar_All.pipe_right (let _49_1666 = ep
in {lhs = _49_1666.lhs; relation = _49_1666.relation; rhs = _49_1666.rhs; element = _49_1666.element; logical_guard = _49_1666.logical_guard; scope = _49_1666.scope; reason = _49_1666.reason; loc = _49_1666.loc; rank = Some (rank)}) (fun _102_887 -> EProb (_102_887)))
in (rank, _102_888)))
end))
end))
end
| CProb (cp) -> begin
(let _102_890 = (FStar_All.pipe_right (let _49_1670 = cp
in {lhs = _49_1670.lhs; relation = _49_1670.relation; rhs = _49_1670.rhs; element = _49_1670.element; logical_guard = _49_1670.logical_guard; scope = _49_1670.scope; reason = _49_1670.reason; loc = _49_1670.loc; rank = Some (rigid_rigid)}) (fun _102_889 -> CProb (_102_889)))
in (rigid_rigid, _102_890))
end)))

let next_prob = (fun wl -> (let rec aux = (fun _49_1677 probs -> (match (_49_1677) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _49_1685 = (rank wl hd)
in (match (_49_1685) with
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

let rec solve_flex_rigid_join = (fun env tp wl -> (let _49_1696 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_940 = (prob_to_string env (TProb (tp)))
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _102_940))
end else begin
()
end
in (let _49_1700 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_49_1700) with
| (u, args) -> begin
(let _49_1706 = (0, 1, 2, 3, 4)
in (match (_49_1706) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun t1 t2 -> (let _49_1715 = (FStar_Absyn_Util.head_and_args t1)
in (match (_49_1715) with
| (h1, args1) -> begin
(let _49_1719 = (FStar_Absyn_Util.head_and_args t2)
in (match (_49_1719) with
| (h2, _49_1718) -> begin
(match ((h1.FStar_Absyn_Syntax.n, h2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (tc1), FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
if (FStar_Ident.lid_equals tc1.FStar_Absyn_Syntax.v tc2.FStar_Absyn_Syntax.v) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _102_952 = (let _102_951 = (let _102_950 = (new_problem env t1 EQ t2 None t1.FStar_Absyn_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _102_949 -> TProb (_102_949)) _102_950))
in (_102_951)::[])
in Some (_102_952))
end
end else begin
None
end
end
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (FStar_Absyn_Util.bvar_eq a b) then begin
Some ([])
end else begin
None
end
end
| _49_1731 -> begin
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
(let phi2 = (let _102_957 = (FStar_Absyn_Util.mk_subst_one_binder (FStar_Absyn_Syntax.v_binder x) (FStar_Absyn_Syntax.v_binder y))
in (FStar_Absyn_Util.subst_typ _102_957 phi2))
in (let _102_961 = (let _102_960 = (let _102_959 = (let _102_958 = (FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _102_958))
in (FStar_Absyn_Syntax.mk_Typ_refine _102_959 (Some (FStar_Absyn_Syntax.ktype)) t1.FStar_Absyn_Syntax.pos))
in (_102_960, m))
in Some (_102_961)))
end))
end
| (_49_1750, FStar_Absyn_Syntax.Typ_refine (y, _49_1753)) -> begin
(let m = (base_types_match t1 y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _49_1763), _49_1767) -> begin
(let m = (base_types_match x.FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _49_1774 -> begin
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
| FStar_Absyn_Syntax.Typ_uvar (uv, _49_1782) -> begin
(let _49_1807 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _49_30 -> (match (_49_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _49_1793 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_49_1793) with
| (u', _49_1792) -> begin
(match ((let _102_963 = (compress env wl u')
in _102_963.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv', _49_1796) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _49_1800 -> begin
false
end)
end))
end
| _49_1802 -> begin
false
end)
end
| _49_1804 -> begin
false
end))))
in (match (_49_1807) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _49_1811 tps -> (match (_49_1811) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _102_968 = (compress env wl hd.rhs)
in (conjoin bound _102_968))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _49_1824 -> begin
None
end)
end))
in (match ((let _102_970 = (let _102_969 = (compress env wl tp.rhs)
in (_102_969, []))
in (make_upper_bound _102_970 upper_bounds))) with
| None -> begin
(let _49_1826 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (let _49_1833 = wl
in {attempting = sub_probs; wl_deferred = _49_1833.wl_deferred; subst = _49_1833.subst; ctr = _49_1833.ctr; slack_vars = _49_1833.slack_vars; defer_ok = _49_1833.defer_ok; smt_ok = _49_1833.smt_ok; tcenv = _49_1833.tcenv}))) with
| Success (subst, _49_1837) -> begin
(let wl = (let _49_1840 = wl
in {attempting = rest; wl_deferred = _49_1840.wl_deferred; subst = []; ctr = _49_1840.ctr; slack_vars = _49_1840.slack_vars; defer_ok = _49_1840.defer_ok; smt_ok = _49_1840.smt_ok; tcenv = _49_1840.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _49_1846 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _49_1849 -> begin
None
end))
end))
end))
end
| _49_1851 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve = (fun env probs -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _49_1859 = probs
in {attempting = tl; wl_deferred = _49_1859.wl_deferred; subst = _49_1859.subst; ctr = _49_1859.ctr; slack_vars = _49_1859.slack_vars; defer_ok = _49_1859.defer_ok; smt_ok = _49_1859.smt_ok; tcenv = _49_1859.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
if ((((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) && (not ((FStar_ST.read FStar_Options.no_slack)))) then begin
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
end
| EProb (ep) -> begin
(solve_e' env (maybe_invert ep) probs)
end
| CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end))
end
| (None, _49_1875, _49_1877) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _49_1881 -> begin
(let _49_1890 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _49_1887 -> (match (_49_1887) with
| (c, _49_1884, _49_1886) -> begin
(c < probs.ctr)
end))))
in (match (_49_1890) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _102_979 = (let _102_978 = (let _102_977 = (FStar_List.map (fun _49_1896 -> (match (_49_1896) with
| (_49_1893, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in {carry = _102_977; slack = probs.slack_vars})
in (probs.subst, _102_978))
in Success (_102_979))
end
| _49_1898 -> begin
(let _102_982 = (let _49_1899 = probs
in (let _102_981 = (FStar_All.pipe_right attempt (FStar_List.map (fun _49_1906 -> (match (_49_1906) with
| (_49_1902, _49_1904, y) -> begin
y
end))))
in {attempting = _102_981; wl_deferred = rest; subst = _49_1899.subst; ctr = _49_1899.ctr; slack_vars = _49_1899.slack_vars; defer_ok = _49_1899.defer_ok; smt_ok = _49_1899.smt_ok; tcenv = _49_1899.tcenv}))
in (solve env _102_982))
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
(let subst = (let _102_1008 = (FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (FStar_List.append _102_1008 subst))
in (let env = (let _102_1009 = (FStar_Tc_Env.binding_of_binder hd2)
in (FStar_Tc_Env.push_local_binding env _102_1009))
in (let prob = (match (((Prims.fst hd1), (Prims.fst hd2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _102_1013 = (let _102_1012 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _102_1011 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _102_1012 _102_1011 b.FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (FStar_All.pipe_left (fun _102_1010 -> KProb (_102_1010)) _102_1013))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _102_1017 = (let _102_1016 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _102_1015 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _102_1016 _102_1015 y.FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (FStar_All.pipe_left (fun _102_1014 -> TProb (_102_1014)) _102_1017))
end
| _49_1982 -> begin
(FStar_All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| FStar_Util.Inr (msg) -> begin
FStar_Util.Inr (msg)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _102_1019 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _102_1018 = (FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (FStar_Absyn_Util.mk_conj _102_1019 _102_1018)))
in FStar_Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _49_1992 -> begin
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
| _49_2007 -> begin
(FStar_All.failwith "impossible")
end))
and solve_k' = (fun env problem wl -> (let orig = KProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _102_1026 = (solve_prob orig None [] wl)
in (solve env _102_1026))
end else begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in if (FStar_Util.physical_equality k1 k2) then begin
(let _102_1027 = (solve_prob orig None [] wl)
in (solve env _102_1027))
end else begin
(let r = (FStar_Tc_Env.get_range env)
in (let imitate_k = (fun _49_2023 -> (match (_49_2023) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let _49_2028 = (imitation_sub_probs orig env xs ps qs)
in (match (_49_2028) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _102_1043 = (let _102_1042 = (h gs_xs)
in (xs, _102_1042))
in (FStar_Absyn_Syntax.mk_Kind_lam _102_1043 r))
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
in if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && (not ((FStar_Util.set_mem u uvs2.FStar_Absyn_Syntax.uvars_k)))) then begin
(let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (let _102_1052 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _102_1052)))
end else begin
(let _102_1057 = (let _102_1056 = (FStar_All.pipe_right xs FStar_Absyn_Util.args_of_non_null_binders)
in (let _102_1055 = (decompose_kind env k)
in (rel, u, _102_1056, xs, _102_1055)))
in (imitate_k _102_1057))
end)))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.FStar_Absyn_Syntax.n, k2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Kind_type, FStar_Absyn_Syntax.Kind_type)) | ((FStar_Absyn_Syntax.Kind_effect, FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _102_1058 = (solve_prob orig None [] wl)
in (FStar_All.pipe_left (solve env) _102_1058))
end
| (FStar_Absyn_Syntax.Kind_abbrev (_49_2051, k1), _49_2056) -> begin
(solve_k env (let _49_2058 = problem
in {lhs = k1; relation = _49_2058.relation; rhs = _49_2058.rhs; element = _49_2058.element; logical_guard = _49_2058.logical_guard; scope = _49_2058.scope; reason = _49_2058.reason; loc = _49_2058.loc; rank = _49_2058.rank}) wl)
end
| (_49_2061, FStar_Absyn_Syntax.Kind_abbrev (_49_2063, k2)) -> begin
(solve_k env (let _49_2068 = problem
in {lhs = _49_2068.lhs; relation = _49_2068.relation; rhs = k2; element = _49_2068.element; logical_guard = _49_2068.logical_guard; scope = _49_2068.scope; reason = _49_2068.reason; loc = _49_2068.loc; rank = _49_2068.rank}) wl)
end
| (FStar_Absyn_Syntax.Kind_arrow (bs1, k1'), FStar_Absyn_Syntax.Kind_arrow (bs2, k2')) -> begin
(let sub_prob = (fun scope env subst -> (let _102_1067 = (let _102_1066 = (FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _102_1066 problem.relation k2' None "Arrow-kind result"))
in (FStar_All.pipe_left (fun _102_1065 -> KProb (_102_1065)) _102_1067)))
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
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(let zs = (intersect_vars xs ys)
in (let _49_2111 = (new_kvar r zs)
in (match (_49_2111) with
| (u, _49_2110) -> begin
(let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end
end)))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, args), _49_2120) -> begin
(flex_rigid problem.relation u args k2)
end
| (_49_2123, FStar_Absyn_Syntax.Kind_uvar (u, args)) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, FStar_Absyn_Syntax.Kind_unknown)) -> begin
(FStar_All.failwith "Impossible")
end
| _49_2150 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end))
end))
and solve_t = (fun env problem wl -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _49_2158 -> begin
(FStar_All.failwith "Impossible")
end)))
and solve_t' = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> if wl.defer_ok then begin
(let _49_2165 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1078 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _102_1078 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
in (let imitate_t = (fun orig env wl p -> (let _49_2182 = p
in (match (_49_2182) with
| ((u, k), ps, xs, (h, _49_2179, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_Tc_Env.get_range env)
in (let _49_2188 = (imitation_sub_probs orig env xs ps qs)
in (match (_49_2188) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _102_1090 = (let _102_1089 = (h gs_xs)
in (xs, _102_1089))
in (FStar_Absyn_Syntax.mk_Typ_lam' _102_1090 None r))
in (let _49_2190 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1095 = (FStar_Absyn_Print.typ_to_string im)
in (let _102_1094 = (FStar_Absyn_Print.tag_of_typ im)
in (let _102_1093 = (let _102_1091 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _102_1091 (FStar_String.concat ", ")))
in (let _102_1092 = (FStar_Tc_Normalize.formula_norm_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _102_1095 _102_1094 _102_1093 _102_1092)))))
end else begin
()
end
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun orig env wl i p -> (let _49_2206 = p
in (match (_49_2206) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let pi = (FStar_List.nth ps i)
in (let rec gs = (fun k -> (let _49_2213 = (FStar_Absyn_Util.kind_formals k)
in (match (_49_2213) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _49_2242 = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let k_a = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _49_2226 = (new_tvar r xs k_a)
in (match (_49_2226) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_Tc_Normalize.eta_expand env gi_xs)
in (let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app (gi, ps) (Some (k_a)) r)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in ((FStar_Absyn_Syntax.targ gi_xs), (FStar_Absyn_Syntax.targ gi_ps), subst))))
end)))
end
| FStar_Util.Inr (x) -> begin
(let t_x = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _49_2235 = (new_evar r xs t_x)
in (match (_49_2235) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app (gi, ps) (Some (t_x)) r)
in (let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in ((FStar_Absyn_Syntax.varg gi_xs), (FStar_Absyn_Syntax.varg gi_ps), subst))))
end)))
end)
in (match (_49_2242) with
| (gi_xs, gi_ps, subst) -> begin
(let _49_2245 = (aux subst tl)
in (match (_49_2245) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _102_1115 = (let _102_1114 = (FStar_List.nth xs i)
in (FStar_All.pipe_left Prims.fst _102_1114))
in ((Prims.fst pi), _102_1115))) with
| (FStar_Util.Inl (pi), FStar_Util.Inl (xi)) -> begin
if (let _102_1116 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _102_1116)) then begin
None
end else begin
(let _49_2254 = (gs xi.FStar_Absyn_Syntax.sort)
in (match (_49_2254) with
| (g_xs, _49_2253) -> begin
(let xi = (FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _102_1118 = (let _102_1117 = (FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (FStar_Absyn_Syntax.ktype)) r)
in (xs, _102_1117))
in (FStar_Absyn_Syntax.mk_Typ_lam _102_1118 None r))
in (let sub = (let _102_1124 = (let _102_1123 = (FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (FStar_Absyn_Syntax.ktype)) r)
in (let _102_1122 = (let _102_1121 = (FStar_List.map (fun _49_2262 -> (match (_49_2262) with
| (_49_2258, _49_2260, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _102_1121))
in (mk_problem (p_scope orig) orig _102_1123 (p_rel orig) _102_1122 None "projection")))
in (FStar_All.pipe_left (fun _102_1119 -> TProb (_102_1119)) _102_1124))
in (let _49_2264 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1126 = (FStar_Absyn_Print.typ_to_string proj)
in (let _102_1125 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _102_1126 _102_1125)))
end else begin
()
end
in (let wl = (let _102_1128 = (let _102_1127 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_102_1127))
in (solve_prob orig _102_1128 ((UT ((u, proj)))::[]) wl))
in (let _102_1130 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _102_1129 -> Some (_102_1129)) _102_1130)))))))
end))
end
end
| _49_2268 -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _49_2280 = lhs
in (match (_49_2280) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _102_1157 = (FStar_Absyn_Util.kind_formals k)
in (FStar_All.pipe_right _102_1157 Prims.fst))
in (let xs = (FStar_Absyn_Util.name_binders xs)
in (let _102_1162 = (decompose_typ env t2)
in ((uv, k), ps, xs, _102_1162)))))
in (let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
if (i = (- (1))) then begin
(match ((imitate_t orig env wl st)) with
| Failed (_49_2290) -> begin
(imitate_or_project n st (i + 1))
end
| sol -> begin
sol
end)
end else begin
(match ((project_t orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(imitate_or_project n st (i + 1))
end
| Some (sol) -> begin
sol
end)
end
end)
in (let check_head = (fun fvs1 t2 -> (let _49_2306 = (FStar_Absyn_Util.head_and_args t2)
in (match (_49_2306) with
| (hd, _49_2305) -> begin
(match (hd.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _49_2317 -> begin
(let fvs_hd = (FStar_Absyn_Util.freevars_typ hd)
in if (FStar_Absyn_Util.fvs_included fvs_hd fvs1) then begin
true
end else begin
(let _49_2319 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1173 = (FStar_Absyn_Print.freevars_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _102_1173))
end else begin
()
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _102_1177 = (let _102_1176 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _102_1176 Prims.fst))
in (FStar_All.pipe_right _102_1177 FStar_Absyn_Util.freevars_typ))
in if (FStar_Util.set_is_empty fvs_hd.FStar_Absyn_Syntax.ftvs) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (FStar_Absyn_Util.freevars_typ t1)
in (let fvs2 = (FStar_Absyn_Util.freevars_typ t2)
in (let _49_2332 = (occurs_check env wl (uv, k) t2)
in (match (_49_2332) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _102_1179 = (let _102_1178 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _102_1178))
in (giveup_or_defer orig _102_1179))
end else begin
if (FStar_Absyn_Util.fvs_included fvs2 fvs1) then begin
if ((FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ)) then begin
(let _102_1180 = (subterms args_lhs)
in (imitate_t orig env wl _102_1180))
end else begin
(let _49_2333 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1183 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1182 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _102_1181 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _102_1183 _102_1182 _102_1181))))
end else begin
()
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _49_2337 -> begin
(let _102_1185 = (let _102_1184 = (sn_binders env vars)
in (_102_1184, t2))
in (FStar_Absyn_Syntax.mk_Typ_lam _102_1185 None t1.FStar_Absyn_Syntax.pos))
end)
in (let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _49_2340 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1188 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1187 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _102_1186 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _102_1188 _102_1187 _102_1186))))
end else begin
()
end
in (let _102_1189 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _102_1189 (- (1)))))
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
if (let _102_1190 = (FStar_Absyn_Util.freevars_typ t1)
in (check_head _102_1190 t2)) then begin
(let im_ok = (imitate_ok t2)
in (let _49_2344 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1191 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _102_1191 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _102_1192 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _102_1192 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun xs_opt _49_2356 -> (match (_49_2356) with
| (t, u, k, args) -> begin
(let rec aux = (fun binders ys args -> (match (args) with
| [] -> begin
(let ys = (FStar_List.rev ys)
in (let binders = (FStar_List.rev binders)
in (let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _49_2368 = (new_tvar t.FStar_Absyn_Syntax.pos ys kk)
in (match (_49_2368) with
| (t', _49_2367) -> begin
(let _49_2374 = (destruct_flex_t t')
in (match (_49_2374) with
| (u1_ys, u1, k1, _49_2373) -> begin
(let sol = (let _102_1210 = (let _102_1209 = (FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((u, k), _102_1209))
in UT (_102_1210))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun hd -> (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let _102_1214 = (let _102_1213 = (FStar_Tc_Recheck.recompute_kind a)
in (FStar_All.pipe_right _102_1213 (FStar_Absyn_Util.gen_bvar_p a.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _102_1214 FStar_Absyn_Syntax.t_binder))
end
| FStar_Util.Inr (x) -> begin
(let _102_1216 = (let _102_1215 = (FStar_Tc_Recheck.recompute_typ x)
in (FStar_All.pipe_right _102_1215 (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _102_1216 FStar_Absyn_Syntax.v_binder))
end))
in (let _49_2393 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _102_1217 = (new_binder hd)
in (_102_1217, ys))
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
(y, (y)::ys)
end
| Some (xs) -> begin
if (FStar_All.pipe_right xs (FStar_Util.for_some (FStar_Absyn_Util.eq_binder y))) then begin
(y, (y)::ys)
end else begin
(let _102_1218 = (new_binder hd)
in (_102_1218, ys))
end
end)
end)
in (match (_49_2393) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun wl _49_2399 _49_2403 k r -> (match ((_49_2399, _49_2403)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _102_1229 = (solve_prob orig None [] wl)
in (solve env _102_1229))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _49_2412 = (new_tvar r zs k)
in (match (_49_2412) with
| (u_zs, _49_2411) -> begin
(let sub1 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _49_2416 = (occurs_check env wl (u1, k1) sub1)
in (match (_49_2416) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(let sol1 = UT (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(let sub2 = (FStar_Absyn_Syntax.mk_Typ_lam' (ys, u_zs) (Some (k2)) r)
in (let _49_2422 = (occurs_check env wl (u2, k2) sub2)
in (match (_49_2422) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(let sol2 = UT (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end)))))
end
end))
in (let solve_one_pat = (fun _49_2430 _49_2435 -> (match ((_49_2430, _49_2435)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _49_2436 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1235 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1234 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _102_1235 _102_1234)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let sub_probs = (FStar_List.map2 (fun a b -> (let a = (FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Prims.fst a), (Prims.fst b))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _102_1239 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _102_1239 (fun _102_1238 -> TProb (_102_1238))))
end
| (FStar_Util.Inr (t1), FStar_Util.Inr (t2)) -> begin
(let _102_1241 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _102_1241 (fun _102_1240 -> EProb (_102_1240))))
end
| _49_2452 -> begin
(FStar_All.failwith "Impossible")
end))) xs args2)
in (let guard = (let _102_1243 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _102_1243))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Absyn_Util.freevars_typ t2)
in (let _49_2462 = (occurs_check env wl (u1, k1) t2)
in (match (_49_2462) with
| (occurs_ok, _49_2461) -> begin
(let lhs_vars = (FStar_Absyn_Syntax.freevars_of_binders xs)
in if (occurs_ok && (FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)) then begin
(let sol = (let _102_1245 = (let _102_1244 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.FStar_Absyn_Syntax.pos)
in ((u1, k1), _102_1244))
in UT (_102_1245))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(let _49_2473 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_49_2473) with
| (sol, (_49_2468, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _49_2475 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _102_1246 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _102_1246))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _49_2480 -> begin
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
in (let _49_2485 = lhs
in (match (_49_2485) with
| (t1, u1, k1, args1) -> begin
(let _49_2490 = rhs
in (match (_49_2490) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _102_1247 = (FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _102_1247 t2.FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _49_2508 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _49_2512 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_49_2512) with
| (sol, _49_2511) -> begin
(let wl = (extend_solution sol wl)
in (let _49_2514 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _102_1248 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _102_1248))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _49_2519 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (let orig = TProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _102_1249 = (solve_prob orig None [] wl)
in (solve env _102_1249))
end else begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _102_1250 = (solve_prob orig None [] wl)
in (solve env _102_1250))
end else begin
(let _49_2523 = if (FStar_Tc_Env.debug env (FStar_Options.Other ("Rel"))) then begin
(let _102_1253 = (prob_to_string env orig)
in (let _102_1252 = (let _102_1251 = (FStar_List.map (uvi_to_string wl.tcenv) wl.subst)
in (FStar_All.pipe_right _102_1251 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Attempting %s\n\tSubst is %s\n" _102_1253 _102_1252)))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun _49_2528 _49_2531 -> (match ((_49_2528, _49_2531)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _49_2538 = (FStar_Util.first_N n bs)
in (match (_49_2538) with
| (bs, rest) -> begin
(let _102_1283 = (mk_cod rest)
in (bs, _102_1283))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _102_1287 = (let _102_1284 = (mk_cod1 [])
in (bs1, _102_1284))
in (let _102_1286 = (let _102_1285 = (mk_cod2 [])
in (bs2, _102_1285))
in (_102_1287, _102_1286)))
end else begin
if (l1 > l2) then begin
(let _102_1290 = (curry l2 bs1 mk_cod1)
in (let _102_1289 = (let _102_1288 = (mk_cod2 [])
in (bs2, _102_1288))
in (_102_1290, _102_1289)))
end else begin
(let _102_1293 = (let _102_1291 = (mk_cod1 [])
in (bs1, _102_1291))
in (let _102_1292 = (curry l1 bs2 mk_cod2)
in (_102_1293, _102_1292)))
end
end)))
end))
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (FStar_Absyn_Util.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
(let _102_1294 = (solve_prob orig None [] wl)
in (solve env _102_1294))
end else begin
(let _102_1298 = (let _102_1297 = (let _102_1296 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _102_1295 -> Some (_102_1295)) _102_1296))
in (solve_prob orig _102_1297 [] wl))
in (solve env _102_1298))
end
end
| (FStar_Absyn_Syntax.Typ_fun (bs1, c1), FStar_Absyn_Syntax.Typ_fun (bs2, c2)) -> begin
(let mk_c = (fun c _49_31 -> (match (_49_31) with
| [] -> begin
c
end
| bs -> begin
(let _102_1303 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Total _102_1303))
end))
in (let _49_2569 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_49_2569) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Absyn_Util.subst_comp subst c1)
in (let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
EQ
end else begin
problem.relation
end
in (let _49_2575 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(let _102_1310 = (let _102_1309 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_right _102_1309 FStar_Range.string_of_range))
in (FStar_Util.print2 "(%s) Using relation %s at higher order\n" _102_1310 (rel_to_string rel)))
end else begin
()
end
in (let _102_1312 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _102_1311 -> CProb (_102_1311)) _102_1312)))))))
end)))
end
| (FStar_Absyn_Syntax.Typ_lam (bs1, t1'), FStar_Absyn_Syntax.Typ_lam (bs2, t2')) -> begin
(let mk_t = (fun t _49_32 -> (match (_49_32) with
| [] -> begin
t
end
| bs -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end))
in (let _49_2597 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_49_2597) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let t1' = (FStar_Absyn_Util.subst_typ subst t1')
in (let _102_1323 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (FStar_All.pipe_left (fun _102_1322 -> TProb (_102_1322)) _102_1323)))))
end)))
end
| (FStar_Absyn_Syntax.Typ_refine (_49_2603), FStar_Absyn_Syntax.Typ_refine (_49_2606)) -> begin
(let _49_2611 = (as_refinement env wl t1)
in (match (_49_2611) with
| (x1, phi1) -> begin
(let _49_2614 = (as_refinement env wl t2)
in (match (_49_2614) with
| (x2, phi2) -> begin
(let base_prob = (let _102_1325 = (mk_problem (p_scope orig) orig x1.FStar_Absyn_Syntax.sort problem.relation x2.FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (FStar_All.pipe_left (fun _102_1324 -> TProb (_102_1324)) _102_1325))
in (let x1_for_x2 = (FStar_Absyn_Util.mk_subst_one_binder (FStar_Absyn_Syntax.v_binder x1) (FStar_Absyn_Syntax.v_binder x2))
in (let phi2 = (FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun imp phi1 phi2 -> (let _102_1342 = (imp phi1 phi2)
in (FStar_All.pipe_right _102_1342 (guard_on_element problem x1))))
in (let fallback = (fun _49_2623 -> (match (()) with
| () -> begin
(let impl = if (problem.relation = EQ) then begin
(mk_imp FStar_Absyn_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Absyn_Util.mk_imp phi1 phi2)
end
in (let guard = (let _102_1345 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _102_1345 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.relation = EQ) then begin
(let ref_prob = (let _102_1347 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _102_1346 -> TProb (_102_1346)) _102_1347))
in (match ((solve env (let _49_2628 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; subst = _49_2628.subst; ctr = _49_2628.ctr; slack_vars = _49_2628.slack_vars; defer_ok = false; smt_ok = _49_2628.smt_ok; tcenv = _49_2628.tcenv}))) with
| Failed (_49_2631) -> begin
(fallback ())
end
| Success (subst, _49_2635) -> begin
(let guard = (let _102_1350 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _102_1349 = (let _102_1348 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _102_1348 (guard_on_element problem x1)))
in (FStar_Absyn_Util.mk_conj _102_1350 _102_1349)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _49_2640 = wl
in {attempting = _49_2640.attempting; wl_deferred = _49_2640.wl_deferred; subst = subst; ctr = (wl.ctr + 1); slack_vars = _49_2640.slack_vars; defer_ok = _49_2640.defer_ok; smt_ok = _49_2640.smt_ok; tcenv = _49_2640.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end)))))
end))
end))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _102_1352 = (destruct_flex_t t1)
in (let _102_1351 = (destruct_flex_t t2)
in (flex_flex orig _102_1352 _102_1351)))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) when (problem.relation = EQ) -> begin
(let _102_1353 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _102_1353 t2 wl))
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
EQ
end else begin
problem.relation
end
in if (let _102_1354 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _102_1354)) then begin
(let _102_1357 = (FStar_All.pipe_left (fun _102_1355 -> TProb (_102_1355)) (let _49_2799 = problem
in {lhs = _49_2799.lhs; relation = new_rel; rhs = _49_2799.rhs; element = _49_2799.element; logical_guard = _49_2799.logical_guard; scope = _49_2799.scope; reason = _49_2799.reason; loc = _49_2799.loc; rank = _49_2799.rank}))
in (let _102_1356 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _102_1357 _102_1356 t2 wl)))
end else begin
(let _49_2803 = (base_and_refinement env wl t2)
in (match (_49_2803) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _102_1360 = (FStar_All.pipe_left (fun _102_1358 -> TProb (_102_1358)) (let _49_2805 = problem
in {lhs = _49_2805.lhs; relation = new_rel; rhs = _49_2805.rhs; element = _49_2805.element; logical_guard = _49_2805.logical_guard; scope = _49_2805.scope; reason = _49_2805.reason; loc = _49_2805.loc; rank = _49_2805.rank}))
in (let _102_1359 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _102_1360 _102_1359 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _49_2811 = y
in {FStar_Absyn_Syntax.v = _49_2811.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t1; FStar_Absyn_Syntax.p = _49_2811.FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _102_1362 = (mk_problem problem.scope orig t1 new_rel y.FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _102_1361 -> TProb (_102_1361)) _102_1362))
in (let guard = (let _102_1363 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _102_1363 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end)
end
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
if wl.defer_ok then begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end else begin
(let _49_2846 = (base_and_refinement env wl t1)
in (match (_49_2846) with
| (t_base, _49_2845) -> begin
(solve_t env (let _49_2847 = problem
in {lhs = t_base; relation = EQ; rhs = _49_2847.rhs; element = _49_2847.element; logical_guard = _49_2847.logical_guard; scope = _49_2847.scope; reason = _49_2847.reason; loc = _49_2847.loc; rank = _49_2847.rank}) wl)
end))
end
end
| (FStar_Absyn_Syntax.Typ_refine (_49_2850), _49_2853) -> begin
(let t2 = (let _102_1364 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _102_1364))
in (solve_t env (let _49_2856 = problem
in {lhs = _49_2856.lhs; relation = _49_2856.relation; rhs = t2; element = _49_2856.element; logical_guard = _49_2856.logical_guard; scope = _49_2856.scope; reason = _49_2856.reason; loc = _49_2856.loc; rank = _49_2856.rank}) wl))
end
| (_49_2859, FStar_Absyn_Syntax.Typ_refine (_49_2861)) -> begin
(let t1 = (let _102_1365 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _102_1365))
in (solve_t env (let _49_2865 = problem
in {lhs = t1; relation = _49_2865.relation; rhs = _49_2865.rhs; element = _49_2865.element; logical_guard = _49_2865.logical_guard; scope = _49_2865.scope; reason = _49_2865.reason; loc = _49_2865.loc; rank = _49_2865.rank}) wl))
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) | ((FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, FStar_Absyn_Syntax.Typ_const (_))) | ((_, FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _49_2905 = (head_matches_delta env wl t1 t2)
in (match (_49_2905) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _49_2908) -> begin
(let head1 = (let _102_1366 = (FStar_Absyn_Util.head_and_args t1)
in (FStar_All.pipe_right _102_1366 Prims.fst))
in (let head2 = (let _102_1367 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _102_1367 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_49_2915) -> begin
true
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Tc_Env.is_projector env tc.FStar_Absyn_Syntax.v)
end
| _49_2920 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _102_1373 = (let _102_1372 = (let _102_1371 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _102_1370 -> Some (_102_1370)) _102_1371))
in (solve_prob orig _102_1372 [] wl))
in (solve env _102_1373))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_49_2922, Some (t1, t2)) -> begin
(solve_t env (let _49_2928 = problem
in {lhs = t1; relation = _49_2928.relation; rhs = t2; element = _49_2928.element; logical_guard = _49_2928.logical_guard; scope = _49_2928.scope; reason = _49_2928.reason; loc = _49_2928.loc; rank = _49_2928.rank}) wl)
end
| (_49_2931, None) -> begin
(let _49_2934 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1375 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1374 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Head matches: %s and %s\n" _102_1375 _102_1374)))
end else begin
()
end
in (let _49_2938 = (FStar_Absyn_Util.head_and_args t1)
in (match (_49_2938) with
| (head, args) -> begin
(let _49_2941 = (FStar_Absyn_Util.head_and_args t2)
in (match (_49_2941) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _102_1380 = (let _102_1379 = (FStar_Absyn_Print.typ_to_string head)
in (let _102_1378 = (FStar_Absyn_Print.args_to_string args)
in (let _102_1377 = (FStar_Absyn_Print.typ_to_string head')
in (let _102_1376 = (FStar_Absyn_Print.args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _102_1379 _102_1378 _102_1377 _102_1376)))))
in (giveup env _102_1380 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(let _102_1381 = (solve_prob orig None [] wl)
in (solve env _102_1381))
end else begin
(let _49_2945 = (base_and_refinement env wl t1)
in (match (_49_2945) with
| (base1, refinement1) -> begin
(let _49_2948 = (base_and_refinement env wl t2)
in (match (_49_2948) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _49_2952 = if ((head_matches head head) <> FullMatch) then begin
(let _102_1384 = (let _102_1383 = (FStar_Absyn_Print.typ_to_string head)
in (let _102_1382 = (FStar_Absyn_Print.typ_to_string head')
in (FStar_Util.format2 "Assertion failed: expected full match of %s and %s\n" _102_1383 _102_1382)))
in (FStar_All.failwith _102_1384))
end else begin
()
end
in (let subprobs = (FStar_List.map2 (fun a a' -> (match (((Prims.fst a), (Prims.fst a'))) with
| (FStar_Util.Inl (t), FStar_Util.Inl (t')) -> begin
(let _102_1388 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (FStar_All.pipe_left (fun _102_1387 -> TProb (_102_1387)) _102_1388))
end
| (FStar_Util.Inr (v), FStar_Util.Inr (v')) -> begin
(let _102_1390 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (FStar_All.pipe_left (fun _102_1389 -> EProb (_102_1389)) _102_1390))
end
| _49_2967 -> begin
(FStar_All.failwith "Impossible")
end)) args args')
in (let formula = (let _102_1392 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Absyn_Util.mk_conj_l _102_1392))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _49_2973 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _49_2976 = problem
in {lhs = lhs; relation = _49_2976.relation; rhs = rhs; element = _49_2976.element; logical_guard = _49_2976.logical_guard; scope = _49_2976.scope; reason = _49_2976.reason; loc = _49_2976.loc; rank = _49_2976.rank}) wl)))
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
| ((FStar_Absyn_Syntax.Typ_ascribed (_), _)) | ((FStar_Absyn_Syntax.Typ_meta (_), _)) | ((FStar_Absyn_Syntax.Typ_delayed (_), _)) | ((_, FStar_Absyn_Syntax.Typ_ascribed (_))) | ((_, FStar_Absyn_Syntax.Typ_meta (_))) | ((_, FStar_Absyn_Syntax.Typ_delayed (_))) -> begin
(FStar_All.failwith "Impossible")
end
| _49_3015 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c = (fun env problem wl -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _49_3032 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (let sub_probs = (FStar_List.map2 (fun arg1 arg2 -> (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _102_1407 = (sub_prob t1 EQ t2 "effect arg")
in (FStar_All.pipe_left (fun _102_1406 -> TProb (_102_1406)) _102_1407))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _102_1409 = (sub_prob e1 EQ e2 "effect arg")
in (FStar_All.pipe_left (fun _102_1408 -> EProb (_102_1408)) _102_1409))
end
| _49_3047 -> begin
(FStar_All.failwith "impossible")
end)) c1_comp.FStar_Absyn_Syntax.effect_args c2_comp.FStar_Absyn_Syntax.effect_args)
in (let guard = (let _102_1411 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _102_1411))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _102_1412 = (solve_prob orig None [] wl)
in (solve env _102_1412))
end else begin
(let _49_3052 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1414 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _102_1413 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _102_1414 (rel_to_string problem.relation) _102_1413)))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let _49_3057 = (c1, c2)
in (match (_49_3057) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Absyn_Syntax.n, c2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Total (t1), FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (FStar_Absyn_Syntax.Total (_49_3064), FStar_Absyn_Syntax.Comp (_49_3067)) -> begin
(let _102_1416 = (let _49_3070 = problem
in (let _102_1415 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _102_1415; relation = _49_3070.relation; rhs = _49_3070.rhs; element = _49_3070.element; logical_guard = _49_3070.logical_guard; scope = _49_3070.scope; reason = _49_3070.reason; loc = _49_3070.loc; rank = _49_3070.rank}))
in (solve_c env _102_1416 wl))
end
| (FStar_Absyn_Syntax.Comp (_49_3073), FStar_Absyn_Syntax.Total (_49_3076)) -> begin
(let _102_1418 = (let _49_3079 = problem
in (let _102_1417 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _49_3079.lhs; relation = _49_3079.relation; rhs = _102_1417; element = _49_3079.element; logical_guard = _49_3079.logical_guard; scope = _49_3079.scope; reason = _49_3079.reason; loc = _49_3079.loc; rank = _49_3079.rank}))
in (solve_c env _102_1418 wl))
end
| (FStar_Absyn_Syntax.Comp (_49_3082), FStar_Absyn_Syntax.Comp (_49_3085)) -> begin
if (((FStar_Absyn_Util.is_ml_comp c1) && (FStar_Absyn_Util.is_ml_comp c2)) || ((FStar_Absyn_Util.is_total_comp c1) && ((FStar_Absyn_Util.is_total_comp c2) || (FStar_Absyn_Util.is_ml_comp c2)))) then begin
(solve_t env (problem_using_guard orig (FStar_Absyn_Util.comp_result c1) problem.relation (FStar_Absyn_Util.comp_result c2) None "result type") wl)
end else begin
(let c1_comp = (FStar_Absyn_Util.comp_to_comp_typ c1)
in (let c2_comp = (FStar_Absyn_Util.comp_to_comp_typ c2)
in if ((problem.relation = EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Absyn_Syntax.effect_name c2_comp.FStar_Absyn_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (let _49_3092 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Absyn_Syntax.effect_name.FStar_Ident.str c2.FStar_Absyn_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_Tc_Env.monad_leq env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _102_1421 = (let _102_1420 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _102_1419 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _102_1420 _102_1419)))
in (giveup env _102_1421 orig))
end
| Some (edge) -> begin
if (problem.relation = EQ) then begin
(let _49_3112 = (match (c1.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp1), _49_3105)::(FStar_Util.Inl (wlp1), _49_3100)::[] -> begin
(wp1, wlp1)
end
| _49_3109 -> begin
(let _102_1423 = (let _102_1422 = (FStar_Range.string_of_range (FStar_Absyn_Syntax.range_of_lid c1.FStar_Absyn_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _102_1422))
in (FStar_All.failwith _102_1423))
end)
in (match (_49_3112) with
| (wp, wlp) -> begin
(let c1 = (let _102_1429 = (let _102_1428 = (let _102_1424 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _102_1424))
in (let _102_1427 = (let _102_1426 = (let _102_1425 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _102_1425))
in (_102_1426)::[])
in (_102_1428)::_102_1427))
in {FStar_Absyn_Syntax.effect_name = c2.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _102_1429; FStar_Absyn_Syntax.flags = c1.FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _49_33 -> (match (_49_33) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.MLEFFECT) | (FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _49_3119 -> begin
false
end))))
in (let _49_3142 = (match ((c1.FStar_Absyn_Syntax.effect_args, c2.FStar_Absyn_Syntax.effect_args)) with
| ((FStar_Util.Inl (wp1), _49_3126)::_49_3122, (FStar_Util.Inl (wp2), _49_3134)::_49_3130) -> begin
(wp1, wp2)
end
| _49_3139 -> begin
(let _102_1433 = (let _102_1432 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _102_1431 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _102_1432 _102_1431)))
in (FStar_All.failwith _102_1433))
end)
in (match (_49_3142) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(solve_t env (problem_using_guard orig c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ None "result type") wl)
end else begin
(let c2_decl = (FStar_Tc_Env.get_effect_decl env c2.FStar_Absyn_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _49_3144 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _102_1438 = (let _102_1437 = (let _102_1436 = (let _102_1435 = (let _102_1434 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _102_1434))
in (_102_1435)::[])
in ((FStar_Absyn_Syntax.targ c1.FStar_Absyn_Syntax.result_typ))::_102_1436)
in (c2_decl.FStar_Absyn_Syntax.trivial, _102_1437))
in (FStar_Absyn_Syntax.mk_Typ_app _102_1438 (Some (FStar_Absyn_Syntax.ktype)) r)))
end else begin
(let wp2_imp_wp1 = (let _102_1448 = (let _102_1447 = (let _102_1446 = (let _102_1445 = (let _102_1444 = (let _102_1440 = (let _102_1439 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.imp_lid _102_1439))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _102_1440))
in (let _102_1443 = (let _102_1442 = (let _102_1441 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _102_1441))
in (_102_1442)::[])
in (_102_1444)::_102_1443))
in ((FStar_Absyn_Syntax.targ wpc2))::_102_1445)
in ((FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ))::_102_1446)
in (c2_decl.FStar_Absyn_Syntax.wp_binop, _102_1447))
in (FStar_Absyn_Syntax.mk_Typ_app _102_1448 None r))
in (FStar_Absyn_Syntax.mk_Typ_app (c2_decl.FStar_Absyn_Syntax.wp_as_type, ((FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ))::((FStar_Absyn_Syntax.targ wp2_imp_wp1))::[]) (Some (FStar_Absyn_Syntax.ktype)) r))
end
in (let base_prob = (let _102_1450 = (sub_prob c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _102_1449 -> TProb (_102_1449)) _102_1450))
in (let wl = (let _102_1454 = (let _102_1453 = (let _102_1452 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _102_1452 g))
in (FStar_All.pipe_left (fun _102_1451 -> Some (_102_1451)) _102_1453))
in (solve_prob orig _102_1454 [] wl))
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
and solve_e = (fun env problem wl -> (match ((compress_prob wl (EProb (problem)))) with
| EProb (p) -> begin
(solve_e' env p wl)
end
| _49_3156 -> begin
(FStar_All.failwith "Impossible")
end))
and solve_e' = (fun env problem wl -> (let problem = (let _49_3160 = problem
in {lhs = _49_3160.lhs; relation = EQ; rhs = _49_3160.rhs; element = _49_3160.element; logical_guard = _49_3160.logical_guard; scope = _49_3160.scope; reason = _49_3160.reason; loc = _49_3160.loc; rank = _49_3160.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun lhs rhs reason -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _49_3172 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1464 = (prob_to_string env orig)
in (FStar_Util.print1 "Attempting:\n%s\n" _102_1464))
end else begin
()
end
in (let flex_rigid = (fun _49_3179 e2 -> (match (_49_3179) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun xs args2 -> (let _49_3206 = (let _102_1480 = (FStar_All.pipe_right args2 (FStar_List.map (fun _49_34 -> (match (_49_34) with
| (FStar_Util.Inl (t), imp) -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _49_3193 = (new_tvar t.FStar_Absyn_Syntax.pos xs kk)
in (match (_49_3193) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args1) (Some (kk)) t.FStar_Absyn_Syntax.pos)
in (let _102_1476 = (let _102_1475 = (sub_prob gi_pi t "type index")
in (FStar_All.pipe_left (fun _102_1474 -> TProb (_102_1474)) _102_1475))
in ((FStar_Util.Inl (gi_xi), imp), _102_1476)))
end)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let tt = (FStar_Tc_Recheck.recompute_typ v)
in (let _49_3202 = (new_evar v.FStar_Absyn_Syntax.pos xs tt)
in (match (_49_3202) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args1) (Some (tt)) v.FStar_Absyn_Syntax.pos)
in (let _102_1479 = (let _102_1478 = (sub_prob gi_pi v "expression index")
in (FStar_All.pipe_left (fun _102_1477 -> EProb (_102_1477)) _102_1478))
in ((FStar_Util.Inr (gi_xi), imp), _102_1479)))
end)))
end))))
in (FStar_All.pipe_right _102_1480 FStar_List.unzip))
in (match (_49_3206) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _102_1482 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) gi_pi)
in (FStar_Absyn_Util.mk_conj_l _102_1482))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun head2 args2 -> (let giveup = (fun reason -> (let _102_1489 = (FStar_Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _102_1489 orig)))
in (match ((let _102_1490 = (FStar_Absyn_Util.compress_exp head2)
in _102_1490.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _49_3223 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_49_3223) with
| (all_xs, tres) -> begin
if ((FStar_List.length all_xs) <> (FStar_List.length args1)) then begin
(let _102_1493 = (let _102_1492 = (FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _102_1491 = (FStar_Absyn_Print.args_to_string args2)
in (FStar_Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _102_1492 _102_1491)))
in (giveup _102_1493))
end else begin
(let rec aux = (fun xs args -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(FStar_All.failwith "impossible")
end
| ((FStar_Util.Inl (_49_3240), _49_3243)::xs, (FStar_Util.Inl (_49_3248), _49_3251)::args) -> begin
(aux xs args)
end
| ((FStar_Util.Inr (xi), _49_3259)::xs, (FStar_Util.Inr (arg), _49_3266)::args) -> begin
(match ((let _102_1498 = (FStar_Absyn_Util.compress_exp arg)
in _102_1498.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (z) -> begin
if (FStar_Absyn_Util.bvar_eq y z) then begin
(let _49_3275 = (sub_problems all_xs args2)
in (match (_49_3275) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _102_1502 = (let _102_1501 = (let _102_1500 = (let _102_1499 = (FStar_Absyn_Util.bvar_to_exp xi)
in (_102_1499, gi_xi))
in (FStar_Absyn_Syntax.mk_Exp_app' _102_1500 None e1.FStar_Absyn_Syntax.pos))
in (all_xs, _102_1501))
in (FStar_Absyn_Syntax.mk_Exp_abs _102_1502 None e1.FStar_Absyn_Syntax.pos))
in (let _49_3277 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1506 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _102_1505 = (FStar_Absyn_Print.exp_to_string sol)
in (let _102_1504 = (let _102_1503 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _102_1503 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Projected: %s -> %s\nSubprobs=\n%s\n" _102_1506 _102_1505 _102_1504))))
end else begin
()
end
in (let _102_1508 = (let _102_1507 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _102_1507))
in (solve env _102_1508))))
end))
end else begin
(aux xs args)
end
end
| _49_3280 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _102_1511 = (let _102_1510 = (FStar_Absyn_Print.binder_to_string x)
in (let _102_1509 = (FStar_Absyn_Print.arg_to_string arg)
in (FStar_Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _102_1510 _102_1509)))
in (giveup _102_1511))
end))
in (aux (FStar_List.rev all_xs) (FStar_List.rev args1)))
end
end))
end
| _49_3289 -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun _49_3291 -> (match (()) with
| () -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end else begin
(let _49_3292 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1515 = (FStar_Absyn_Print.exp_to_string e1)
in (let _102_1514 = (FStar_Absyn_Print.exp_to_string e2)
in (FStar_Util.print2 "Imitating expressions: %s =?= %s\n" _102_1515 _102_1514)))
end else begin
()
end
in (let _49_3296 = (FStar_Absyn_Util.head_and_args_e e2)
in (match (_49_3296) with
| (head2, args2) -> begin
(let fvhead = (FStar_Absyn_Util.freevars_exp head2)
in (let _49_3301 = (occurs_check_e env (u1, t1) head2)
in (match (_49_3301) with
| (occurs_ok, _49_3300) -> begin
if ((FStar_Absyn_Util.fvs_included fvhead FStar_Absyn_Syntax.no_fvs) && occurs_ok) then begin
(let _49_3309 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_49_3309) with
| (xs, tres) -> begin
(let _49_3313 = (sub_problems xs args2)
in (match (_49_3313) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _49_3317 -> begin
(let _102_1517 = (let _102_1516 = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (xs, _102_1516))
in (FStar_Absyn_Syntax.mk_Exp_abs _102_1517 None e1.FStar_Absyn_Syntax.pos))
end))
in (let _49_3319 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1521 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _102_1520 = (FStar_Absyn_Print.exp_to_string sol)
in (let _102_1519 = (let _102_1518 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _102_1518 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _102_1521 _102_1520 _102_1519))))
end else begin
()
end
in (let _102_1523 = (let _102_1522 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _102_1522))
in (solve env _102_1523))))
end))
end))
end else begin
if occurs_ok then begin
(project_e head2 args2)
end else begin
(giveup env "flex-rigid: occurs check failed" orig)
end
end
end)))
end)))
end
end))
in (match (maybe_vars1) with
| (None) | (Some ([])) -> begin
(imitate_or_project_e ())
end
| Some (xs) -> begin
(let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (let fvs2 = (FStar_Absyn_Util.freevars_exp e2)
in (let _49_3331 = (occurs_check_e env (u1, t1) e2)
in (match (_49_3331) with
| (occurs_ok, _49_3330) -> begin
if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && occurs_ok) then begin
(let sol = (FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.FStar_Absyn_Syntax.pos)
in (let _102_1524 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _102_1524)))
end else begin
(imitate_or_project_e ())
end
end))))
end)))))
end))
in (let flex_flex = (fun _49_3338 _49_3343 -> (match ((_49_3338, _49_3343)) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-flex: not a pattern" orig wl))
end else begin
(giveup env "flex-flex expressions not patterns" orig)
end
end
| (Some (xs), Some (ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(let zs = (intersect_vars xs ys)
in (let tt = (FStar_Tc_Recheck.recompute_typ e2)
in (let _49_3364 = (let _102_1529 = (FStar_Tc_Env.get_range env)
in (new_evar _102_1529 zs tt))
in (match (_49_3364) with
| (u, _49_3363) -> begin
(let sub1 = (match (xs) with
| [] -> begin
u
end
| _49_3367 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.FStar_Absyn_Syntax.pos)
end)
in (let sub2 = (match (ys) with
| [] -> begin
u
end
| _49_3371 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.FStar_Absyn_Syntax.pos)
end)
in (let _102_1530 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _102_1530))))
end))))
end
end)))
end))
in (let smt_fallback = (fun e1 e2 -> if wl.smt_ok then begin
(let _49_3376 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1535 = (prob_to_string env orig)
in (FStar_Util.print1 "Using SMT to solve:\n%s\n" _102_1535))
end else begin
()
end
in (let _49_3381 = (let _102_1537 = (FStar_Tc_Env.get_range env)
in (let _102_1536 = (FStar_Tc_Env.binders env)
in (new_tvar _102_1537 _102_1536 FStar_Absyn_Syntax.ktype)))
in (match (_49_3381) with
| (t, _49_3380) -> begin
(let _102_1541 = (let _102_1540 = (let _102_1539 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _102_1538 -> Some (_102_1538)) _102_1539))
in (solve_prob orig _102_1540 [] wl))
in (solve env _102_1541))
end)))
end else begin
(giveup env "no SMT solution permitted" orig)
end)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_ascribed (e1, _49_3384, _49_3386), _49_3390) -> begin
(solve_e env (let _49_3392 = problem
in {lhs = e1; relation = _49_3392.relation; rhs = _49_3392.rhs; element = _49_3392.element; logical_guard = _49_3392.logical_guard; scope = _49_3392.scope; reason = _49_3392.reason; loc = _49_3392.loc; rank = _49_3392.rank}) wl)
end
| (_49_3395, FStar_Absyn_Syntax.Exp_ascribed (e2, _49_3398, _49_3400)) -> begin
(solve_e env (let _49_3404 = problem
in {lhs = _49_3404.lhs; relation = _49_3404.relation; rhs = e2; element = _49_3404.element; logical_guard = _49_3404.logical_guard; scope = _49_3404.scope; reason = _49_3404.reason; loc = _49_3404.loc; rank = _49_3404.rank}) wl)
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _102_1543 = (destruct_flex_e e1)
in (let _102_1542 = (destruct_flex_e e2)
in (flex_flex _102_1543 _102_1542)))
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(let _102_1544 = (destruct_flex_e e1)
in (flex_rigid _102_1544 e2))
end
| ((_, FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _102_1545 = (destruct_flex_e e2)
in (flex_rigid _102_1545 e1))
end
| (FStar_Absyn_Syntax.Exp_bvar (x1), FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
if (FStar_Absyn_Util.bvd_eq x1.FStar_Absyn_Syntax.v x1'.FStar_Absyn_Syntax.v) then begin
(let _102_1546 = (solve_prob orig None [] wl)
in (solve env _102_1546))
end else begin
(let _102_1552 = (let _102_1551 = (let _102_1550 = (let _102_1549 = (FStar_Tc_Recheck.recompute_typ e1)
in (let _102_1548 = (FStar_Tc_Recheck.recompute_typ e2)
in (FStar_Absyn_Util.mk_eq _102_1549 _102_1548 e1 e2)))
in (FStar_All.pipe_left (fun _102_1547 -> Some (_102_1547)) _102_1550))
in (solve_prob orig _102_1551 [] wl))
in (solve env _102_1552))
end
end
| (FStar_Absyn_Syntax.Exp_fvar (fv1, _49_3543), FStar_Absyn_Syntax.Exp_fvar (fv1', _49_3548)) -> begin
if (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv1'.FStar_Absyn_Syntax.v) then begin
(let _102_1553 = (solve_prob orig None [] wl)
in (solve env _102_1553))
end else begin
(giveup env "free-variables unequal" orig)
end
end
| (FStar_Absyn_Syntax.Exp_constant (s1), FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun s1 s2 -> (match ((s1, s2)) with
| (FStar_Const.Const_bytearray (b1, _49_3562), FStar_Const.Const_bytearray (b2, _49_3567)) -> begin
(b1 = b2)
end
| (FStar_Const.Const_string (b1, _49_3573), FStar_Const.Const_string (b2, _49_3578)) -> begin
(b1 = b2)
end
| _49_3583 -> begin
(s1 = s2)
end))
in if (const_eq s1 s1') then begin
(let _102_1558 = (solve_prob orig None [] wl)
in (solve env _102_1558))
end else begin
(giveup env "constants unequal" orig)
end)
end
| (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_49_3593); FStar_Absyn_Syntax.tk = _49_3591; FStar_Absyn_Syntax.pos = _49_3589; FStar_Absyn_Syntax.fvs = _49_3587; FStar_Absyn_Syntax.uvs = _49_3585}, _49_3597), _49_3601) -> begin
(let _102_1560 = (let _49_3603 = problem
in (let _102_1559 = (whnf_e env e1)
in {lhs = _102_1559; relation = _49_3603.relation; rhs = _49_3603.rhs; element = _49_3603.element; logical_guard = _49_3603.logical_guard; scope = _49_3603.scope; reason = _49_3603.reason; loc = _49_3603.loc; rank = _49_3603.rank}))
in (solve_e env _102_1560 wl))
end
| (_49_3606, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_49_3616); FStar_Absyn_Syntax.tk = _49_3614; FStar_Absyn_Syntax.pos = _49_3612; FStar_Absyn_Syntax.fvs = _49_3610; FStar_Absyn_Syntax.uvs = _49_3608}, _49_3620)) -> begin
(let _102_1562 = (let _49_3624 = problem
in (let _102_1561 = (whnf_e env e2)
in {lhs = _49_3624.lhs; relation = _49_3624.relation; rhs = _102_1561; element = _49_3624.element; logical_guard = _49_3624.logical_guard; scope = _49_3624.scope; reason = _49_3624.reason; loc = _49_3624.loc; rank = _49_3624.rank}))
in (solve_e env _102_1562 wl))
end
| (FStar_Absyn_Syntax.Exp_app (head1, args1), FStar_Absyn_Syntax.Exp_app (head2, args2)) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun sub_probs wl args1 args2 -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _102_1572 = (let _102_1571 = (FStar_List.map p_guard sub_probs)
in (FStar_All.pipe_right _102_1571 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Util.mk_conj_l _102_1572))
in (let g = (simplify_formula env guard)
in (let g = (FStar_Absyn_Util.compress_typ g)
in (match (g.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
(let _102_1573 = (solve_prob orig None wl.subst (let _49_3649 = orig_wl
in {attempting = _49_3649.attempting; wl_deferred = _49_3649.wl_deferred; subst = []; ctr = _49_3649.ctr; slack_vars = _49_3649.slack_vars; defer_ok = _49_3649.defer_ok; smt_ok = _49_3649.smt_ok; tcenv = _49_3649.tcenv}))
in (solve env _102_1573))
end
| _49_3652 -> begin
(let _49_3656 = (let _102_1575 = (FStar_Tc_Env.get_range env)
in (let _102_1574 = (FStar_Tc_Env.binders env)
in (new_tvar _102_1575 _102_1574 FStar_Absyn_Syntax.ktype)))
in (match (_49_3656) with
| (t, _49_3655) -> begin
(let guard = (let _102_1576 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_Absyn_Util.mk_disj g _102_1576))
in (let _102_1577 = (solve_prob orig (Some (guard)) wl.subst (let _49_3658 = orig_wl
in {attempting = _49_3658.attempting; wl_deferred = _49_3658.wl_deferred; subst = []; ctr = _49_3658.ctr; slack_vars = _49_3658.slack_vars; defer_ok = _49_3658.defer_ok; smt_ok = _49_3658.smt_ok; tcenv = _49_3658.tcenv}))
in (solve env _102_1577)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _102_1579 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (FStar_All.pipe_left (fun _102_1578 -> TProb (_102_1578)) _102_1579))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _102_1581 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (FStar_All.pipe_left (fun _102_1580 -> EProb (_102_1580)) _102_1581))
end
| _49_3678 -> begin
(FStar_All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _49_3680 = wl
in {attempting = (prob)::[]; wl_deferred = []; subst = _49_3680.subst; ctr = _49_3680.ctr; slack_vars = _49_3680.slack_vars; defer_ok = false; smt_ok = false; tcenv = _49_3680.tcenv}))) with
| Failed (_49_3683) -> begin
(smt_fallback e1 e2)
end
| Success (subst, _49_3687) -> begin
(solve_args ((prob)::sub_probs) (let _49_3690 = wl
in {attempting = _49_3690.attempting; wl_deferred = _49_3690.wl_deferred; subst = subst; ctr = _49_3690.ctr; slack_vars = _49_3690.slack_vars; defer_ok = _49_3690.defer_ok; smt_ok = _49_3690.smt_ok; tcenv = _49_3690.tcenv}) rest1 rest2)
end))
end
| _49_3693 -> begin
(FStar_All.failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun head1 head2 -> (match ((let _102_1589 = (let _102_1586 = (FStar_Absyn_Util.compress_exp head1)
in _102_1586.FStar_Absyn_Syntax.n)
in (let _102_1588 = (let _102_1587 = (FStar_Absyn_Util.compress_exp head2)
in _102_1587.FStar_Absyn_Syntax.n)
in (_102_1589, _102_1588)))) with
| (FStar_Absyn_Syntax.Exp_bvar (x), FStar_Absyn_Syntax.Exp_bvar (y)) when ((FStar_Absyn_Util.bvar_eq x y) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _49_3704), FStar_Absyn_Syntax.Exp_fvar (g, _49_3709)) when (((FStar_Absyn_Util.fvar_eq f g) && (not ((FStar_Absyn_Util.is_interpreted f.FStar_Absyn_Syntax.v)))) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_ascribed (e, _49_3715, _49_3717), _49_3721) -> begin
(match_head_and_args e head2)
end
| (_49_3724, FStar_Absyn_Syntax.Exp_ascribed (e, _49_3727, _49_3729)) -> begin
(match_head_and_args head1 e)
end
| (FStar_Absyn_Syntax.Exp_abs (_49_3734), _49_3737) -> begin
(let _102_1591 = (let _49_3739 = problem
in (let _102_1590 = (whnf_e env e1)
in {lhs = _102_1590; relation = _49_3739.relation; rhs = _49_3739.rhs; element = _49_3739.element; logical_guard = _49_3739.logical_guard; scope = _49_3739.scope; reason = _49_3739.reason; loc = _49_3739.loc; rank = _49_3739.rank}))
in (solve_e env _102_1591 wl))
end
| (_49_3742, FStar_Absyn_Syntax.Exp_abs (_49_3744)) -> begin
(let _102_1593 = (let _49_3747 = problem
in (let _102_1592 = (whnf_e env e2)
in {lhs = _49_3747.lhs; relation = _49_3747.relation; rhs = _102_1592; element = _49_3747.element; logical_guard = _49_3747.logical_guard; scope = _49_3747.scope; reason = _49_3747.reason; loc = _49_3747.loc; rank = _49_3747.rank}))
in (solve_e env _102_1593 wl))
end
| _49_3750 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _49_3752 -> begin
(let _49_3756 = (let _102_1595 = (FStar_Tc_Env.get_range env)
in (let _102_1594 = (FStar_Tc_Env.binders env)
in (new_tvar _102_1595 _102_1594 FStar_Absyn_Syntax.ktype)))
in (match (_49_3756) with
| (t, _49_3755) -> begin
(let guard = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _49_3758 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1596 = (FStar_Absyn_Print.typ_to_string guard)
in (FStar_Util.print1 "Emitting guard %s\n" _102_1596))
end else begin
()
end
in (let _102_1600 = (let _102_1599 = (let _102_1598 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _102_1597 -> Some (_102_1597)) _102_1598))
in (solve_prob orig _102_1599 [] wl))
in (solve env _102_1600))))
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
| NonTrivial (_49_3762) -> begin
_49_3762
end))

type implicits =
((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list

type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

let is_Mkguard_t = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

let guard_to_string = (fun env g -> (let form = (match (g.guard_f) with
| Trivial -> begin
"trivial"
end
| NonTrivial (f) -> begin
if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Tc_Normalize.formula_norm_to_string env f)
end else begin
"non-trivial"
end
end)
in (let carry = (let _102_1631 = (FStar_List.map (fun _49_3776 -> (match (_49_3776) with
| (_49_3774, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (FStar_All.pipe_right _102_1631 (FStar_String.concat ",\n")))
in (FStar_Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula = (fun g -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_form = (fun g -> g.guard_f)

let is_trivial = (fun g -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _49_3782} -> begin
true
end
| _49_3789 -> begin
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
| _49_3805 -> begin
(FStar_All.failwith "impossible")
end)
in (let _102_1645 = (let _49_3807 = g
in (let _102_1644 = (let _102_1643 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder x))::[], f) None f.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (fun _102_1642 -> NonTrivial (_102_1642)) _102_1643))
in {guard_f = _102_1644; deferred = _49_3807.deferred; implicits = _49_3807.implicits}))
in Some (_102_1645)))
end))

let apply_guard = (fun g e -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _49_3814 = g
in (let _102_1653 = (let _102_1652 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn f.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) (FStar_Absyn_Syntax.mk_Typ_app (f, ((FStar_Absyn_Syntax.varg e))::[])))
in NonTrivial (_102_1652))
in {guard_f = _102_1653; deferred = _49_3814.deferred; implicits = _49_3814.implicits}))
end))

let trivial = (fun t -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_49_3819) -> begin
(FStar_All.failwith "impossible")
end))

let conj_guard_f = (fun g1 g2 -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _102_1660 = (FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_102_1660))
end))

let check_trivial = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _49_3837 -> begin
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

let binop_guard = (fun f g1 g2 -> (let _102_1683 = (f g1.guard_f g2.guard_f)
in {guard_f = _102_1683; deferred = {carry = (FStar_List.append g1.deferred.carry g2.deferred.carry); slack = (FStar_List.append g1.deferred.slack g2.deferred.slack)}; implicits = (FStar_List.append g1.implicits g2.implicits)}))

let conj_guard = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

let imp_guard = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

let close_guard = (fun binders g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _49_3864 = g
in (let _102_1698 = (let _102_1697 = (FStar_Absyn_Util.close_forall binders f)
in (FStar_All.pipe_right _102_1697 (fun _102_1696 -> NonTrivial (_102_1696))))
in {guard_f = _102_1698; deferred = _49_3864.deferred; implicits = _49_3864.implicits}))
end))

let mk_guard = (fun g ps slack locs -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _102_1710 = (FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _102_1709 = (FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _102_1710 (rel_to_string rel) _102_1709)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob = (fun env t1 rel t2 -> (let x = (let _102_1719 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.gen_bvar_p _102_1719 t1))
in (let env = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let p = (let _102_1723 = (let _102_1721 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left (fun _102_1720 -> Some (_102_1720)) _102_1721))
in (let _102_1722 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _102_1723 _102_1722)))
in (TProb (p), x)))))

let new_k_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _102_1731 = (FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _102_1730 = (FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _102_1731 (rel_to_string rel) _102_1730)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let simplify_guard = (fun env g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _49_3898 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _102_1736 = (FStar_Absyn_Print.typ_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _102_1736))
end else begin
()
end
in (let f = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _49_3904 -> begin
NonTrivial (f)
end)
in (let _49_3906 = g
in {guard_f = f; deferred = _49_3906.deferred; implicits = _49_3906.implicits}))))
end))

let solve_and_commit = (fun env probs err -> (let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(let _49_3911 = probs
in {attempting = _49_3911.attempting; wl_deferred = _49_3911.wl_deferred; subst = _49_3911.subst; ctr = _49_3911.ctr; slack_vars = _49_3911.slack_vars; defer_ok = false; smt_ok = _49_3911.smt_ok; tcenv = _49_3911.tcenv})
end else begin
probs
end
in (let sol = (solve env probs)
in (match (sol) with
| Success (s, deferred) -> begin
(let _49_3919 = (commit env s)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _49_3925 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _102_1748 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _102_1748))
end else begin
()
end
in (err (d, s)))
end))))

let with_guard = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _102_1760 = (let _102_1759 = (let _102_1758 = (let _102_1757 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _102_1757 (fun _102_1756 -> NonTrivial (_102_1756))))
in {guard_f = _102_1758; deferred = d; implicits = []})
in (simplify_guard env _102_1759))
in (FStar_All.pipe_left (fun _102_1755 -> Some (_102_1755)) _102_1760))
end))

let try_keq = (fun env k1 k2 -> (let _49_3936 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1768 = (FStar_Absyn_Print.kind_to_string k1)
in (let _102_1767 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print2 "try_keq of %s and %s\n" _102_1768 _102_1767)))
end else begin
()
end
in (let prob = (let _102_1773 = (let _102_1772 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _102_1771 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _102_1770 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _102_1772 EQ _102_1771 None _102_1770))))
in (FStar_All.pipe_left (fun _102_1769 -> KProb (_102_1769)) _102_1773))
in (let _102_1775 = (solve_and_commit env (singleton env prob) (fun _49_3939 -> None))
in (FStar_All.pipe_left (with_guard env prob) _102_1775)))))

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
(let _102_1786 = (let _102_1785 = (let _102_1784 = (FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_102_1784, r))
in FStar_Absyn_Syntax.Error (_102_1785))
in (Prims.raise _102_1786))
end
| Some (t) -> begin
(let _102_1789 = (let _102_1788 = (let _102_1787 = (FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_102_1787, r))
in FStar_Absyn_Syntax.Error (_102_1788))
in (Prims.raise _102_1789))
end))
end
| Some (g) -> begin
g
end))

let subkind = (fun env k1 k2 -> (let _49_3958 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1799 = (let _102_1796 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _102_1796))
in (let _102_1798 = (FStar_Absyn_Print.kind_to_string k1)
in (let _102_1797 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print3 "(%s) subkind of %s and %s\n" _102_1799 _102_1798 _102_1797))))
end else begin
()
end
in (let prob = (let _102_1804 = (let _102_1803 = (whnf_k env k1)
in (let _102_1802 = (whnf_k env k2)
in (let _102_1801 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _102_1803 SUB _102_1802 None _102_1801))))
in (FStar_All.pipe_left (fun _102_1800 -> KProb (_102_1800)) _102_1804))
in (let res = (let _102_1811 = (let _102_1810 = (solve_and_commit env (singleton env prob) (fun _49_3961 -> (let _102_1809 = (let _102_1808 = (let _102_1807 = (FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _102_1806 = (FStar_Tc_Env.get_range env)
in (_102_1807, _102_1806)))
in FStar_Absyn_Syntax.Error (_102_1808))
in (Prims.raise _102_1809))))
in (FStar_All.pipe_left (with_guard env prob) _102_1810))
in (FStar_Util.must _102_1811))
in res))))

let try_teq = (fun env t1 t2 -> (let _49_3967 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1819 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1818 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _102_1819 _102_1818)))
end else begin
()
end
in (let prob = (let _102_1822 = (let _102_1821 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _102_1821))
in (FStar_All.pipe_left (fun _102_1820 -> TProb (_102_1820)) _102_1822))
in (let g = (let _102_1824 = (solve_and_commit env (singleton env prob) (fun _49_3970 -> None))
in (FStar_All.pipe_left (with_guard env prob) _102_1824))
in g))))

let teq = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _102_1834 = (let _102_1833 = (let _102_1832 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _102_1831 = (FStar_Tc_Env.get_range env)
in (_102_1832, _102_1831)))
in FStar_Absyn_Syntax.Error (_102_1833))
in (Prims.raise _102_1834))
end
| Some (g) -> begin
(let _49_3979 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1837 = (FStar_Absyn_Print.typ_to_string t1)
in (let _102_1836 = (FStar_Absyn_Print.typ_to_string t2)
in (let _102_1835 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _102_1837 _102_1836 _102_1835))))
end else begin
()
end
in g)
end))

let try_subtype = (fun env t1 t2 -> (let _49_3984 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1845 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _102_1844 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _102_1845 _102_1844)))
end else begin
()
end
in (let _49_3988 = (new_t_prob env t1 SUB t2)
in (match (_49_3988) with
| (prob, x) -> begin
(let g = (let _102_1847 = (solve_and_commit env (singleton env prob) (fun _49_3989 -> None))
in (FStar_All.pipe_left (with_guard env prob) _102_1847))
in (let _49_3992 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _102_1851 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _102_1850 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _102_1849 = (let _102_1848 = (FStar_Util.must g)
in (guard_to_string env _102_1848))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _102_1851 _102_1850 _102_1849))))
end else begin
()
end
in (abstract_guard x g)))
end))))

let subtype_fail = (fun env t1 t2 -> (let _102_1858 = (let _102_1857 = (let _102_1856 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _102_1855 = (FStar_Tc_Env.get_range env)
in (_102_1856, _102_1855)))
in FStar_Absyn_Syntax.Error (_102_1857))
in (Prims.raise _102_1858)))

let subtype = (fun env t1 t2 -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp = (fun env c1 c2 -> (let _49_4006 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1872 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _102_1871 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _102_1872 _102_1871)))
end else begin
()
end
in (let rel = if env.FStar_Tc_Env.use_eq then begin
EQ
end else begin
SUB
end
in (let prob = (let _102_1875 = (let _102_1874 = (FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _102_1874 "sub_comp"))
in (FStar_All.pipe_left (fun _102_1873 -> CProb (_102_1873)) _102_1875))
in (let _102_1877 = (solve_and_commit env (singleton env prob) (fun _49_4010 -> None))
in (FStar_All.pipe_left (with_guard env prob) _102_1877))))))

let solve_deferred_constraints = (fun env g -> (let fail = (fun _49_4017 -> (match (_49_4017) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _49_4022 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && ((FStar_List.length g.deferred.carry) <> 0)) then begin
(let _102_1890 = (let _102_1889 = (FStar_All.pipe_right g.deferred.carry (FStar_List.map (fun _49_4021 -> (match (_49_4021) with
| (msg, x) -> begin
(let _102_1888 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc x))
in (let _102_1887 = (prob_to_string env x)
in (let _102_1886 = (let _102_1885 = (FStar_All.pipe_right (p_guard x) Prims.fst)
in (FStar_Tc_Normalize.formula_norm_to_string env _102_1885))
in (FStar_Util.format4 "(At %s) %s\n%s\nguard is %s\n" _102_1888 msg _102_1887 _102_1886))))
end))))
in (FStar_All.pipe_right _102_1889 (FStar_String.concat "\n")))
in (FStar_All.pipe_left (FStar_Util.print1 "Trying to solve carried problems: begin\n%s\nend\n") _102_1890))
end else begin
()
end
in (let gopt = (let _102_1891 = (wl_of_guard env g.deferred)
in (solve_and_commit env _102_1891 fail))
in (match (gopt) with
| Some ({carry = _49_4027; slack = slack}) -> begin
(let _49_4030 = (fix_slack_vars slack)
in (let _49_4032 = g
in {guard_f = _49_4032.guard_f; deferred = no_deferred; implicits = _49_4032.implicits}))
end
| _49_4035 -> begin
(FStar_All.failwith "impossible")
end)))))

let try_discharge_guard = (fun env g -> (let g = (solve_deferred_constraints env g)
in if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
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
(let _49_4046 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _102_1898 = (FStar_Tc_Env.get_range env)
in (let _102_1897 = (let _102_1896 = (FStar_Absyn_Print.formula_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _102_1896))
in (FStar_Tc_Errors.diag _102_1898 _102_1897)))
end else begin
()
end
in (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env vc))
end))
end)
end))





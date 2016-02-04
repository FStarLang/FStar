
open Prims
let new_kvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.uvar_k) = (fun r binders -> (let u = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (let _154_7 = (let _154_6 = (let _154_5 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _154_5))
in (FStar_Absyn_Syntax.mk_Kind_uvar _154_6 r))
in (_154_7, u))))

let new_tvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Absyn_Syntax.is_null_binder x) Prims.op_Negation))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _51_48 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let k' = (FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _154_15 = (FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_154_15, uv)))))
end))))

let new_evar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.exp) = (fun r binders t -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (FStar_All.pipe_right (FStar_Absyn_Syntax.is_null_binder x) Prims.op_Negation))))
in (let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _51_61 -> begin
(let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (let t' = (let _154_24 = (let _154_23 = (FStar_Absyn_Syntax.mk_Total t)
in (binders, _154_23))
in (FStar_Absyn_Syntax.mk_Typ_fun _154_24 None r))
in (let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _51_67 -> begin
(let _154_25 = (FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_154_25, uv))
end))))
end))))

type rel =
| EQ
| SUB
| SUBINV

let is_EQ : rel  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| EQ -> begin
true
end
| _ -> begin
false
end))

let is_SUB : rel  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SUB -> begin
true
end
| _ -> begin
false
end))

let is_SUBINV : rel  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_COVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| COVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_CONTRAVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_INVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_KProb : prob  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| KProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_TProb : prob  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_EProb : prob  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| EProb (_) -> begin
true
end
| _ -> begin
false
end))

let is_CProb : prob  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

let ___KProb____0 : prob  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem = (fun projectee -> (match (projectee) with
| KProb (_51_84) -> begin
_51_84
end))

let ___TProb____0 : prob  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem = (fun projectee -> (match (projectee) with
| TProb (_51_87) -> begin
_51_87
end))

let ___EProb____0 : prob  ->  (FStar_Absyn_Syntax.exp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| EProb (_51_90) -> begin
_51_90
end))

let ___CProb____0 : prob  ->  (FStar_Absyn_Syntax.comp, Prims.unit) problem = (fun projectee -> (match (projectee) with
| CProb (_51_93) -> begin
_51_93
end))

type probs =
prob Prims.list

type uvi =
| UK of (FStar_Absyn_Syntax.uvar_k * FStar_Absyn_Syntax.knd)
| UT of ((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.typ)
| UE of ((FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.exp)

let is_UK : uvi  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UK (_) -> begin
true
end
| _ -> begin
false
end))

let is_UT : uvi  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UT (_) -> begin
true
end
| _ -> begin
false
end))

let is_UE : uvi  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UE (_) -> begin
true
end
| _ -> begin
false
end))

let ___UK____0 : uvi  ->  (FStar_Absyn_Syntax.uvar_k * FStar_Absyn_Syntax.knd) = (fun projectee -> (match (projectee) with
| UK (_51_96) -> begin
_51_96
end))

let ___UT____0 : uvi  ->  ((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| UT (_51_99) -> begin
_51_99
end))

let ___UE____0 : uvi  ->  ((FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.exp) = (fun projectee -> (match (projectee) with
| UE (_51_102) -> begin
_51_102
end))

type worklist =
{attempting : probs; wl_deferred : (Prims.int * Prims.string * prob) Prims.list; subst : uvi Prims.list; ctr : Prims.int; slack_vars : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_Tc_Env.env}

let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

type deferred =
{carry : (Prims.string * prob) Prims.list; slack : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list}

let is_Mkdeferred : deferred  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdeferred"))))

let no_deferred : deferred = {carry = []; slack = []}

type solution =
| Success of (uvi Prims.list * deferred)
| Failed of (prob * Prims.string)

let is_Success : solution  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

let is_Failed : solution  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

let ___Success____0 : solution  ->  (uvi Prims.list * deferred) = (fun projectee -> (match (projectee) with
| Success (_51_117) -> begin
_51_117
end))

let ___Failed____0 : solution  ->  (prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_51_120) -> begin
_51_120
end))

let rel_to_string : rel  ->  Prims.string = (fun _51_1 -> (match (_51_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

let prob_to_string : FStar_Tc_Env.env  ->  prob  ->  Prims.string = (fun env _51_2 -> (match (_51_2) with
| KProb (p) -> begin
(let _154_227 = (FStar_Absyn_Print.kind_to_string p.lhs)
in (let _154_226 = (FStar_Absyn_Print.kind_to_string p.rhs)
in (FStar_Util.format3 "\t%s\n\t\t%s\n\t%s" _154_227 (rel_to_string p.relation) _154_226)))
end
| TProb (p) -> begin
(let _154_240 = (let _154_239 = (FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _154_238 = (let _154_237 = (FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _154_236 = (let _154_235 = (let _154_234 = (FStar_All.pipe_right p.reason FStar_List.hd)
in (let _154_233 = (let _154_232 = (FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _154_231 = (let _154_230 = (FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _154_229 = (let _154_228 = (FStar_Tc_Normalize.formula_norm_to_string env (Prims.fst p.logical_guard))
in (_154_228)::[])
in (_154_230)::_154_229))
in (_154_232)::_154_231))
in (_154_234)::_154_233))
in ((rel_to_string p.relation))::_154_235)
in (_154_237)::_154_236))
in (_154_239)::_154_238))
in (FStar_Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _154_240))
end
| EProb (p) -> begin
(let _154_242 = (FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _154_241 = (FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _154_242 (rel_to_string p.relation) _154_241)))
end
| CProb (p) -> begin
(let _154_244 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _154_243 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _154_244 (rel_to_string p.relation) _154_243)))
end))

let uvi_to_string : FStar_Tc_Env.env  ->  uvi  ->  Prims.string = (fun env uvi -> (let str = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _154_250 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _154_250 FStar_Util.string_of_int))
end)
in (match (uvi) with
| UK (u, _51_142) -> begin
(let _154_251 = (str u)
in (FStar_All.pipe_right _154_251 (FStar_Util.format1 "UK %s")))
end
| UT ((u, _51_147), t) -> begin
(let _154_254 = (str u)
in (FStar_All.pipe_right _154_254 (fun x -> (let _154_253 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "UT %s %s" x _154_253)))))
end
| UE ((u, _51_155), _51_158) -> begin
(let _154_255 = (str u)
in (FStar_All.pipe_right _154_255 (FStar_Util.format1 "UE %s")))
end)))

let invert_rel : rel  ->  rel = (fun _51_3 -> (match (_51_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

let invert = (fun p -> (let _51_166 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _51_166.element; logical_guard = _51_166.logical_guard; scope = _51_166.scope; reason = _51_166.reason; loc = _51_166.loc; rank = _51_166.rank}))

let maybe_invert = (fun p -> if (p.relation = SUBINV) then begin
(invert p)
end else begin
p
end)

let maybe_invert_p : prob  ->  prob = (fun _51_4 -> (match (_51_4) with
| KProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _154_262 -> KProb (_154_262)))
end
| TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _154_263 -> TProb (_154_263)))
end
| EProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _154_264 -> EProb (_154_264)))
end
| CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _154_265 -> CProb (_154_265)))
end))

let vary_rel : rel  ->  variance  ->  rel = (fun rel _51_5 -> (match (_51_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_rel : prob  ->  rel = (fun _51_6 -> (match (_51_6) with
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

let p_reason : prob  ->  Prims.string Prims.list = (fun _51_7 -> (match (_51_7) with
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

let p_loc : prob  ->  FStar_Range.range = (fun _51_8 -> (match (_51_8) with
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

let p_context : prob  ->  FStar_Absyn_Syntax.binders = (fun _51_9 -> (match (_51_9) with
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

let p_guard : prob  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun _51_10 -> (match (_51_10) with
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

let p_scope : prob  ->  FStar_Absyn_Syntax.binders = (fun _51_11 -> (match (_51_11) with
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

let p_invert : prob  ->  prob = (fun _51_12 -> (match (_51_12) with
| KProb (p) -> begin
(FStar_All.pipe_left (fun _154_284 -> KProb (_154_284)) (invert p))
end
| TProb (p) -> begin
(FStar_All.pipe_left (fun _154_285 -> TProb (_154_285)) (invert p))
end
| EProb (p) -> begin
(FStar_All.pipe_left (fun _154_286 -> EProb (_154_286)) (invert p))
end
| CProb (p) -> begin
(FStar_All.pipe_left (fun _154_287 -> CProb (_154_287)) (invert p))
end))

let is_top_level_prob : prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _154_297 = (new_tvar (p_loc orig) scope FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _154_297; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

let new_problem = (fun env lhs rel rhs elt loc reason -> (let _154_307 = (let _154_306 = (FStar_Tc_Env.get_range env)
in (let _154_305 = (FStar_Tc_Env.binders env)
in (new_tvar _154_306 _154_305 FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _154_307; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

let problem_using_guard = (fun orig lhs rel rhs elt reason -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

let guard_on_element = (fun problem x phi -> (match (problem.element) with
| None -> begin
(FStar_Absyn_Util.close_forall (((FStar_Absyn_Syntax.v_binder x))::[]) phi)
end
| Some (e) -> begin
(FStar_Absyn_Util.subst_typ ((FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::[]) phi)
end))

let solve_prob' : Prims.bool  ->  prob  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (let phi = (match (logical_guard) with
| None -> begin
FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _51_285 = (p_guard prob)
in (match (_51_285) with
| (_51_283, uv) -> begin
(let _51_293 = (match ((let _154_327 = (FStar_Absyn_Util.compress_typ uv)
in _154_327.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uvar, k) -> begin
(let phi = (FStar_Absyn_Util.close_for_kind phi k)
in (FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _51_292 -> begin
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
| _51_297 -> begin
(let _51_298 = if (FStar_All.pipe_left (FStar_Tc_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _154_329 = (let _154_328 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _154_328 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Extending solution: %s\n" _154_329))
end else begin
()
end
in (let _51_300 = wl
in {attempting = _51_300.attempting; wl_deferred = _51_300.wl_deferred; subst = (FStar_List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _51_300.slack_vars; defer_ok = _51_300.defer_ok; smt_ok = _51_300.smt_ok; tcenv = _51_300.tcenv}))
end))
end))))

let extend_solution : uvi  ->  worklist  ->  worklist = (fun sol wl -> (let _51_304 = wl
in {attempting = _51_304.attempting; wl_deferred = _51_304.wl_deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _51_304.slack_vars; defer_ok = _51_304.defer_ok; smt_ok = _51_304.smt_ok; tcenv = _51_304.tcenv}))

let solve_prob : prob  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (solve_prob' false prob logical_guard uvis wl))

let explain : FStar_Tc_Env.env  ->  prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _154_350 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _154_349 = (prob_to_string env d)
in (let _154_348 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _154_350 _154_349 _154_348 s)))))

let empty_worklist : FStar_Tc_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

let singleton : FStar_Tc_Env.env  ->  prob  ->  worklist = (fun env prob -> (let _51_316 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _51_316.wl_deferred; subst = _51_316.subst; ctr = _51_316.ctr; slack_vars = _51_316.slack_vars; defer_ok = _51_316.defer_ok; smt_ok = _51_316.smt_ok; tcenv = _51_316.tcenv}))

let wl_of_guard : FStar_Tc_Env.env  ->  deferred  ->  worklist = (fun env g -> (let _51_320 = (empty_worklist env)
in (let _154_361 = (FStar_List.map Prims.snd g.carry)
in {attempting = _154_361; wl_deferred = _51_320.wl_deferred; subst = _51_320.subst; ctr = _51_320.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _51_320.smt_ok; tcenv = _51_320.tcenv})))

let defer : Prims.string  ->  prob  ->  worklist  ->  worklist = (fun reason prob wl -> (let _51_325 = wl
in {attempting = _51_325.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; subst = _51_325.subst; ctr = _51_325.ctr; slack_vars = _51_325.slack_vars; defer_ok = _51_325.defer_ok; smt_ok = _51_325.smt_ok; tcenv = _51_325.tcenv}))

let attempt : prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (let _51_329 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _51_329.wl_deferred; subst = _51_329.subst; ctr = _51_329.ctr; slack_vars = _51_329.slack_vars; defer_ok = _51_329.defer_ok; smt_ok = _51_329.smt_ok; tcenv = _51_329.tcenv}))

let add_slack_mul : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (let _51_333 = wl
in {attempting = _51_333.attempting; wl_deferred = _51_333.wl_deferred; subst = _51_333.subst; ctr = _51_333.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _51_333.defer_ok; smt_ok = _51_333.smt_ok; tcenv = _51_333.tcenv}))

let add_slack_add : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (let _51_337 = wl
in {attempting = _51_337.attempting; wl_deferred = _51_337.wl_deferred; subst = _51_337.subst; ctr = _51_337.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _51_337.defer_ok; smt_ok = _51_337.smt_ok; tcenv = _51_337.tcenv}))

let giveup : FStar_Tc_Env.env  ->  Prims.string  ->  prob  ->  solution = (fun env reason prob -> (let _51_342 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_386 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _154_386))
end else begin
()
end
in Failed ((prob, reason))))

let commit = (fun env uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _51_13 -> (match (_51_13) with
| UK (u, k) -> begin
(FStar_Absyn_Util.unchecked_unify u k)
end
| UT ((u, k), t) -> begin
(FStar_Absyn_Util.unchecked_unify u t)
end
| UE ((u, _51_359), e) -> begin
(FStar_Absyn_Util.unchecked_unify u e)
end)))))

let find_uvar_k : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.knd Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _51_14 -> (match (_51_14) with
| UK (u, t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _51_372 -> begin
None
end))))

let find_uvar_t : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.typ Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _51_15 -> (match (_51_15) with
| UT ((u, _51_378), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _51_384 -> begin
None
end))))

let find_uvar_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.exp Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _51_16 -> (match (_51_16) with
| UE ((u, _51_390), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _51_396 -> begin
None
end))))

let simplify_formula : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env f -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f))

let norm_targ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t))

let norm_arg = (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _154_417 = (let _154_416 = (norm_targ env t)
in (FStar_All.pipe_left (fun _154_415 -> FStar_Util.Inl (_154_415)) _154_416))
in (_154_417, (Prims.snd a)))
end
| FStar_Util.Inr (v) -> begin
(let _154_420 = (let _154_419 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env v)
in (FStar_All.pipe_left (fun _154_418 -> FStar_Util.Inr (_154_418)) _154_419))
in (_154_420, (Prims.snd a)))
end))

let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _154_425 = (FStar_Tc_Normalize.whnf env t)
in (FStar_All.pipe_right _154_425 FStar_Absyn_Util.compress_typ)))

let sn : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _154_430 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env t)
in (FStar_All.pipe_right _154_430 FStar_Absyn_Util.compress_typ)))

let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _51_17 -> (match (_51_17) with
| (FStar_Util.Inl (a), imp) -> begin
(let _154_436 = (let _154_435 = (let _51_418 = a
in (let _154_434 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _51_418.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_434; FStar_Absyn_Syntax.p = _51_418.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_154_435))
in (_154_436, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _154_439 = (let _154_438 = (let _51_424 = x
in (let _154_437 = (norm_targ env x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _51_424.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _154_437; FStar_Absyn_Syntax.p = _51_424.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_154_438))
in (_154_439, imp))
end)))))

let whnf_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env k -> (let _154_444 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env k)
in (FStar_All.pipe_right _154_444 FStar_Absyn_Util.compress_kind)))

let whnf_e : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env e -> (let _154_449 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env e)
in (FStar_All.pipe_right _154_449 FStar_Absyn_Util.compress_exp)))

let rec compress_k : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env wl k -> (let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((find_uvar_k uv wl.subst)) with
| None -> begin
k
end
| Some (k') -> begin
(match (k'.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, body) -> begin
(let k = (let _154_456 = (FStar_Absyn_Util.subst_of_list formals actuals)
in (FStar_Absyn_Util.subst_kind _154_456 body))
in (compress_k env wl k))
end
| _51_447 -> begin
if ((FStar_List.length actuals) = 0) then begin
(compress_k env wl k')
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end)
end
| _51_449 -> begin
k
end)))

let rec compress : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl t -> (let t = (let _154_463 = (FStar_Absyn_Util.unmeta_typ t)
in (whnf env _154_463))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _51_456) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _51_472); FStar_Absyn_Syntax.tk = _51_469; FStar_Absyn_Syntax.pos = _51_467; FStar_Absyn_Syntax.fvs = _51_465; FStar_Absyn_Syntax.uvs = _51_463}, args) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(let t = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _51_483 -> begin
t
end)
end
| _51_485 -> begin
t
end)))

let rec compress_e : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl e -> (let e = (FStar_Absyn_Util.unmeta_exp e)
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
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _51_507); FStar_Absyn_Syntax.tk = _51_504; FStar_Absyn_Syntax.pos = _51_502; FStar_Absyn_Syntax.fvs = _51_500; FStar_Absyn_Syntax.uvs = _51_498}, args) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(let e' = (compress_e env wl e')
in (FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.FStar_Absyn_Syntax.pos))
end)
end
| _51_519 -> begin
e
end)))

let normalize_refinement : FStar_Tc_Normalize.steps  ->  FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun steps env wl t0 -> (let _154_478 = (compress env wl t0)
in (FStar_Tc_Normalize.normalize_refinement steps env _154_478)))

let base_and_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.bvvar * FStar_Absyn_Syntax.typ) Prims.option) = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
if norm then begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, phi); FStar_Absyn_Syntax.tk = _51_541; FStar_Absyn_Syntax.pos = _51_539; FStar_Absyn_Syntax.fvs = _51_537; FStar_Absyn_Syntax.uvs = _51_535} -> begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _154_491 = (let _154_490 = (FStar_Absyn_Print.typ_to_string tt)
in (let _154_489 = (FStar_Absyn_Print.tag_of_typ tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _154_490 _154_489)))
in (FStar_All.failwith _154_491))
end)
end
end
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _51_556 = (let _154_492 = (normalize_refinement [] env wl t1)
in (aux true _154_492))
in (match (_51_556) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _51_559 -> begin
(t2', refinement)
end)
end))
end
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (FStar_Absyn_Syntax.Typ_ascribed (_)) | (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_meta (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _154_495 = (let _154_494 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_493 = (FStar_Absyn_Print.tag_of_typ t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _154_494 _154_493)))
in (FStar_All.failwith _154_495))
end))
in (let _154_496 = (compress env wl t1)
in (aux false _154_496))))

let unrefine : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _154_501 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _154_501 Prims.fst)))

let trivial_refinement = (fun t -> (let _154_503 = (FStar_Absyn_Util.gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in (_154_503, FStar_Absyn_Util.t_true)))

let as_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) = (fun env wl t -> (let _51_590 = (base_and_refinement env wl t)
in (match (_51_590) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

let force_refinement : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option)  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun _51_598 -> (match (_51_598) with
| (t_base, refopt) -> begin
(let _51_606 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_51_606) with
| (y, phi) -> begin
(FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.FStar_Absyn_Syntax.pos)
end))
end))

let rec occurs = (fun env wl uk t -> (let uvs = (FStar_Absyn_Util.uvars_in_typ t)
in (let _154_523 = (FStar_All.pipe_right uvs.FStar_Absyn_Syntax.uvars_t FStar_Util.set_elements)
in (FStar_All.pipe_right _154_523 (FStar_Util.for_some (fun _51_617 -> (match (_51_617) with
| (uvt, _51_616) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(FStar_Unionfind.equivalent uvt (Prims.fst uk))
end
| Some (t) -> begin
(let t = (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_51_630, t); FStar_Absyn_Syntax.tk = _51_628; FStar_Absyn_Syntax.pos = _51_626; FStar_Absyn_Syntax.fvs = _51_624; FStar_Absyn_Syntax.uvs = _51_622} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))

let occurs_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.string Prims.option) = (fun env wl uk t -> (let occurs_ok = (not ((occurs env wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _154_536 = (let _154_535 = (FStar_Absyn_Print.uvar_t_to_string uk)
in (let _154_534 = (FStar_Absyn_Print.typ_to_string t)
in (let _154_533 = (let _154_532 = (FStar_All.pipe_right wl.subst (FStar_List.map (uvi_to_string env)))
in (FStar_All.pipe_right _154_532 (FStar_String.concat ", ")))
in (FStar_Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _154_535 _154_534 _154_533))))
in Some (_154_536))
end
in (occurs_ok, msg))))

let occurs_and_freevars_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.bool * (Prims.string Prims.option * FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.freevars)) = (fun env wl uk fvs t -> (let fvs_t = (FStar_Absyn_Util.freevars_typ t)
in (let _51_651 = (occurs_check env wl uk t)
in (match (_51_651) with
| (occurs_ok, msg) -> begin
(let _154_547 = (FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _154_547, (msg, fvs, fvs_t)))
end))))

let occurs_check_e : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (Prims.bool * Prims.string Prims.option) = (fun env ut e -> (let uvs = (FStar_Absyn_Util.uvars_in_exp e)
in (let occurs_ok = (not ((FStar_Util.set_mem ut uvs.FStar_Absyn_Syntax.uvars_e)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _154_559 = (let _154_558 = (FStar_Absyn_Print.uvar_e_to_string ut)
in (let _154_557 = (let _154_555 = (let _154_554 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _154_554 (FStar_List.map FStar_Absyn_Print.uvar_e_to_string)))
in (FStar_All.pipe_right _154_555 (FStar_String.concat ", ")))
in (let _154_556 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _154_558 _154_557 _154_556))))
in Some (_154_559))
end
in (occurs_ok, msg)))))

let intersect_vars : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.btvar, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun v1 v2 -> (let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders v1)
in (let fvs2 = (FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _154_566 = (let _154_565 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _154_564 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _154_565; FStar_Absyn_Syntax.fxvs = _154_564}))
in (FStar_Absyn_Syntax.binders_of_freevars _154_566)))))

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun ax1 ax2 -> (match (((Prims.fst ax1), (Prims.fst ax2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Util.bvar_eq x y)
end
| _51_677 -> begin
false
end)) v1 v2)))

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((FStar_All.pipe_left Prims.fst hd)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _51_689; FStar_Absyn_Syntax.pos = _51_687; FStar_Absyn_Syntax.fvs = _51_685; FStar_Absyn_Syntax.uvs = _51_683}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _51_18 -> (match (_51_18) with
| (FStar_Util.Inl (b), _51_698) -> begin
(FStar_Absyn_Syntax.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)
end
| _51_701 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inl (a), (Prims.snd hd)))
end
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (x); FStar_Absyn_Syntax.tk = _51_709; FStar_Absyn_Syntax.pos = _51_707; FStar_Absyn_Syntax.fvs = _51_705; FStar_Absyn_Syntax.uvs = _51_703}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _51_19 -> (match (_51_19) with
| (FStar_Util.Inr (y), _51_718) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _51_721 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inr (x), (Prims.snd hd)))
end
end
| _51_723 -> begin
None
end)))

let rec pat_vars : FStar_Tc_Env.env  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _51_732 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_582 = (FStar_Absyn_Print.arg_to_string hd)
in (FStar_Util.print1 "Not a pattern: %s\n" _154_582))
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
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, k); FStar_Absyn_Syntax.tk = _51_748; FStar_Absyn_Syntax.pos = _51_746; FStar_Absyn_Syntax.fvs = _51_744; FStar_Absyn_Syntax.uvs = _51_742}, args) -> begin
(t, uv, k, args)
end
| _51_758 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_e = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, k) -> begin
(e, uv, k, [])
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, k); FStar_Absyn_Syntax.tk = _51_771; FStar_Absyn_Syntax.pos = _51_769; FStar_Absyn_Syntax.fvs = _51_767; FStar_Absyn_Syntax.uvs = _51_765}, args) -> begin
(e, uv, k, args)
end
| _51_781 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun env t -> (let _51_788 = (destruct_flex_t t)
in (match (_51_788) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _51_792 -> begin
((t, uv, k, args), None)
end)
end)))

type match_result =
| MisMatch
| HeadMatch
| FullMatch

let is_MisMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MisMatch -> begin
true
end
| _ -> begin
false
end))

let is_HeadMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| HeadMatch -> begin
true
end
| _ -> begin
false
end))

let is_FullMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| FullMatch -> begin
true
end
| _ -> begin
false
end))

let head_match : match_result  ->  match_result = (fun _51_20 -> (match (_51_20) with
| MisMatch -> begin
MisMatch
end
| _51_796 -> begin
HeadMatch
end))

let rec head_matches : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  match_result = (fun t1 t2 -> (match ((let _154_599 = (let _154_596 = (FStar_Absyn_Util.unmeta_typ t1)
in _154_596.FStar_Absyn_Syntax.n)
in (let _154_598 = (let _154_597 = (FStar_Absyn_Util.unmeta_typ t2)
in _154_597.FStar_Absyn_Syntax.n)
in (_154_599, _154_598)))) with
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
| (FStar_Absyn_Syntax.Typ_refine (x, _51_825), FStar_Absyn_Syntax.Typ_refine (y, _51_830)) -> begin
(let _154_600 = (head_matches x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _154_600 head_match))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _51_836), _51_840) -> begin
(let _154_601 = (head_matches x.FStar_Absyn_Syntax.sort t2)
in (FStar_All.pipe_right _154_601 head_match))
end
| (_51_843, FStar_Absyn_Syntax.Typ_refine (x, _51_846)) -> begin
(let _154_602 = (head_matches t1 x.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _154_602 head_match))
end
| (FStar_Absyn_Syntax.Typ_fun (_51_851), FStar_Absyn_Syntax.Typ_fun (_51_854)) -> begin
HeadMatch
end
| (FStar_Absyn_Syntax.Typ_app (head, _51_859), FStar_Absyn_Syntax.Typ_app (head', _51_864)) -> begin
(head_matches head head')
end
| (FStar_Absyn_Syntax.Typ_app (head, _51_870), _51_874) -> begin
(head_matches head t2)
end
| (_51_877, FStar_Absyn_Syntax.Typ_app (head, _51_880)) -> begin
(head_matches t1 head)
end
| (FStar_Absyn_Syntax.Typ_uvar (uv, _51_886), FStar_Absyn_Syntax.Typ_uvar (uv', _51_891)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (_51_896, FStar_Absyn_Syntax.Typ_lam (_51_898)) -> begin
HeadMatch
end
| _51_902 -> begin
MisMatch
end))

let head_matches_delta : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (match_result * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option) = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun _51_913 -> (match (()) with
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

let decompose_binder = (fun bs v_ktec rebuild_base -> (let fail = (fun _51_929 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let rebuild = (fun ktecs -> (let rec aux = (fun new_bs bs ktecs -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (FStar_List.rev new_bs) ktec)
end
| ((FStar_Util.Inl (a), imp)::rest, FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((FStar_Util.Inl ((let _51_951 = a
in {FStar_Absyn_Syntax.v = _51_951.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _51_951.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((FStar_Util.Inr (x), imp)::rest, FStar_Absyn_Syntax.T (t, _51_962)::rest') -> begin
(aux (((FStar_Util.Inr ((let _51_967 = x
in {FStar_Absyn_Syntax.v = _51_967.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _51_967.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _51_970 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (let rec mk_b_ktecs = (fun _51_974 _51_21 -> (match (_51_974) with
| (binders, b_ktecs) -> begin
(match (_51_21) with
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
in (let _154_656 = (mk_b_ktecs ([], []) bs)
in (rebuild, _154_656))))))

let rec decompose_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list) = (fun env k -> (let fail = (fun _51_993 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let k0 = k
in (let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(let rebuild = (fun _51_22 -> (match (_51_22) with
| [] -> begin
k
end
| _51_1001 -> begin
(fail ())
end))
in (rebuild, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(decompose_binder bs (FStar_Absyn_Syntax.K (k)) (fun bs _51_23 -> (match (_51_23) with
| FStar_Absyn_Syntax.K (k) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.FStar_Absyn_Syntax.pos)
end
| _51_1012 -> begin
(fail ())
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_51_1014, k) -> begin
(decompose_kind env k)
end
| _51_1019 -> begin
(FStar_All.failwith "Impossible")
end)))))

let rec decompose_typ = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((FStar_Util.Inl (_51_1034), imp), FStar_Absyn_Syntax.T (t, _51_1040)) -> begin
(FStar_Util.Inl (t), imp)
end
| ((FStar_Util.Inr (_51_1045), imp), FStar_Absyn_Syntax.E (e)) -> begin
(FStar_Util.Inr (e), imp)
end
| _51_1053 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.FStar_Absyn_Syntax.pos)))
in (let b_ktecs = (FStar_All.pipe_right args (FStar_List.map (fun _51_24 -> (match (_51_24) with
| (FStar_Util.Inl (t), _51_1059) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _51_1064) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(let _51_1079 = (decompose_binder bs (FStar_Absyn_Syntax.C (c)) (fun bs _51_25 -> (match (_51_25) with
| FStar_Absyn_Syntax.C (c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end
| _51_1076 -> begin
(FStar_All.failwith "Bad reconstruction")
end)))
in (match (_51_1079) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _51_1081 -> begin
(let rebuild = (fun _51_26 -> (match (_51_26) with
| [] -> begin
t
end
| _51_1085 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

let un_T : FStar_Absyn_Syntax.ktec  ->  FStar_Absyn_Syntax.typ = (fun _51_27 -> (match (_51_27) with
| FStar_Absyn_Syntax.T (x, _51_1091) -> begin
x
end
| _51_1095 -> begin
(FStar_All.failwith "impossible")
end))

let arg_of_ktec : FStar_Absyn_Syntax.ktec  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) = (fun _51_28 -> (match (_51_28) with
| FStar_Absyn_Syntax.T (t, _51_1099) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Absyn_Syntax.E (e) -> begin
(FStar_Absyn_Syntax.varg e)
end
| _51_1105 -> begin
(FStar_All.failwith "Impossible")
end))

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_51_1118, variance, FStar_Absyn_Syntax.K (ki)) -> begin
(let _51_1125 = (new_kvar r scope)
in (match (_51_1125) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _154_739 = (let _154_738 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (FStar_All.pipe_left (fun _154_737 -> KProb (_154_737)) _154_738))
in (FStar_Absyn_Syntax.K (gi_xs), _154_739)))
end))
end
| (_51_1128, variance, FStar_Absyn_Syntax.T (ti, kopt)) -> begin
(let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(FStar_Tc_Recheck.recompute_kind ti)
end)
in (let _51_1141 = (new_tvar r scope k)
in (match (_51_1141) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _154_742 = (let _154_741 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _154_740 -> TProb (_154_740)) _154_741))
in (FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _154_742)))
end)))
end
| (_51_1144, variance, FStar_Absyn_Syntax.E (ei)) -> begin
(let t = (FStar_Tc_Recheck.recompute_typ ei)
in (let _51_1152 = (new_evar r scope t)
in (match (_51_1152) with
| (gi_xs, gi) -> begin
(let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _154_745 = (let _154_744 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (FStar_All.pipe_left (fun _154_743 -> EProb (_154_743)) _154_744))
in (FStar_Absyn_Syntax.E (gi_xs), _154_745)))
end)))
end
| (_51_1155, _51_1157, FStar_Absyn_Syntax.C (_51_1159)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(let _51_1235 = (match (q) with
| (bopt, variance, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Total (ti); FStar_Absyn_Syntax.tk = _51_1179; FStar_Absyn_Syntax.pos = _51_1177; FStar_Absyn_Syntax.fvs = _51_1175; FStar_Absyn_Syntax.uvs = _51_1173})) -> begin
(match ((sub_prob scope args (bopt, variance, FStar_Absyn_Syntax.T ((ti, Some (FStar_Absyn_Syntax.ktype)))))) with
| (FStar_Absyn_Syntax.T (gi_xs, _51_1187), prob) -> begin
(let _154_754 = (let _154_753 = (FStar_Absyn_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _154_752 -> FStar_Absyn_Syntax.C (_154_752)) _154_753))
in (_154_754, (prob)::[]))
end
| _51_1193 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_51_1195, _51_1197, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (c); FStar_Absyn_Syntax.tk = _51_1205; FStar_Absyn_Syntax.pos = _51_1203; FStar_Absyn_Syntax.fvs = _51_1201; FStar_Absyn_Syntax.uvs = _51_1199})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map (fun _51_29 -> (match (_51_29) with
| (FStar_Util.Inl (t), _51_1215) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _51_1220) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (let components = ((None, COVARIANT, FStar_Absyn_Syntax.T ((c.FStar_Absyn_Syntax.result_typ, Some (FStar_Absyn_Syntax.ktype)))))::components
in (let _51_1226 = (let _154_756 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _154_756 FStar_List.unzip))
in (match (_51_1226) with
| (ktecs, sub_probs) -> begin
(let gi_xs = (let _154_761 = (let _154_760 = (let _154_757 = (FStar_List.hd ktecs)
in (FStar_All.pipe_right _154_757 un_T))
in (let _154_759 = (let _154_758 = (FStar_List.tl ktecs)
in (FStar_All.pipe_right _154_758 (FStar_List.map arg_of_ktec)))
in {FStar_Absyn_Syntax.effect_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _154_760; FStar_Absyn_Syntax.effect_args = _154_759; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _154_761))
in (FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _51_1229 -> begin
(let _51_1232 = (sub_prob scope args q)
in (match (_51_1232) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_51_1235) with
| (ktec, probs) -> begin
(let _51_1248 = (match (q) with
| (Some (b), _51_1239, _51_1241) -> begin
(let _154_763 = (let _154_762 = (FStar_Absyn_Util.arg_of_non_null_binder b)
in (_154_762)::args)
in (Some (b), (b)::scope, _154_763))
end
| _51_1244 -> begin
(None, scope, args)
end)
in (match (_51_1248) with
| (bopt, scope, args) -> begin
(let _51_1252 = (aux scope args qs)
in (match (_51_1252) with
| (sub_probs, ktecs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _154_766 = (let _154_765 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_154_765)
in (FStar_Absyn_Util.mk_conj_l _154_766))
end
| Some (b) -> begin
(let _154_770 = (let _154_769 = (FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _154_768 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_154_769)::_154_768))
in (FStar_Absyn_Util.mk_conj_l _154_770))
end)
in ((FStar_List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

type slack =
{lower : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); upper : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); flag : Prims.bool FStar_ST.ref}

let is_Mkslack : slack  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkslack"))))

let fix_slack_uv : (FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax)  ->  Prims.bool  ->  Prims.unit = (fun _51_1265 mul -> (match (_51_1265) with
| (uv, k) -> begin
(let inst = if mul then begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_true k)
end else begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_false k)
end
in (FStar_Absyn_Util.unchecked_unify uv inst))
end))

let fix_slack_vars : (Prims.bool * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.list  ->  Prims.unit = (fun slack -> (FStar_All.pipe_right slack (FStar_List.iter (fun _51_1271 -> (match (_51_1271) with
| (mul, s) -> begin
(match ((let _154_788 = (FStar_Absyn_Util.compress_typ s)
in _154_788.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(fix_slack_uv (uv, k) mul)
end
| _51_1277 -> begin
()
end)
end)))))

let fix_slack : slack  ->  FStar_Absyn_Syntax.typ = (fun slack -> (let _51_1285 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.lower))
in (match (_51_1285) with
| (_51_1280, ul, kl, _51_1284) -> begin
(let _51_1292 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.upper))
in (match (_51_1292) with
| (_51_1287, uh, kh, _51_1291) -> begin
(let _51_1293 = (fix_slack_uv (ul, kl) false)
in (let _51_1295 = (fix_slack_uv (uh, kh) true)
in (let _51_1297 = (FStar_ST.op_Colon_Equals slack.flag true)
in (FStar_Absyn_Util.mk_conj (Prims.fst slack.lower) (Prims.fst slack.upper)))))
end))
end)))

let new_slack_var : FStar_Tc_Env.env  ->  slack  ->  ((FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.binders) = (fun env slack -> (let xs = (let _154_796 = (let _154_795 = (destruct_flex_pattern env (Prims.snd slack.lower))
in (FStar_All.pipe_right _154_795 Prims.snd))
in (FStar_All.pipe_right _154_796 FStar_Util.must))
in (let _154_797 = (new_tvar (Prims.fst slack.lower).FStar_Absyn_Syntax.pos xs FStar_Absyn_Syntax.ktype)
in (_154_797, xs))))

let new_slack_formula = (fun p env wl xs low high -> (let _51_1310 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_51_1310) with
| (low_var, uv1) -> begin
(let wl = (add_slack_add uv1 wl)
in (let _51_1314 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_51_1314) with
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
in (let _154_807 = (let _154_806 = (let _154_805 = (let _154_804 = (FStar_Util.mk_ref false)
in (low, high, _154_804))
in FStar_Absyn_Syntax.Meta_slack_formula (_154_805))
in (FStar_Absyn_Syntax.mk_Typ_meta _154_806))
in (_154_807, wl)))))
end)))
end)))

let destruct_slack : FStar_Tc_Env.env  ->  worklist  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ, slack) FStar_Util.either = (fun env wl phi -> (let rec destruct = (fun conn_lid mk_conn phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _51_1338; FStar_Absyn_Syntax.pos = _51_1336; FStar_Absyn_Syntax.fvs = _51_1334; FStar_Absyn_Syntax.uvs = _51_1332}, (FStar_Util.Inl (lhs), _51_1350)::(FStar_Util.Inl (rhs), _51_1345)::[]) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v conn_lid) -> begin
(let rhs = (compress env wl rhs)
in (match (rhs.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
Some ((lhs, rhs))
end
| _51_1376 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some (rest, uvar) -> begin
(let _154_831 = (let _154_830 = (mk_conn lhs rest)
in (_154_830, uvar))
in Some (_154_831))
end)
end))
end
| _51_1383 -> begin
None
end))
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (phi1, phi2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _154_832 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_154_832))
end else begin
(let low = (let _154_833 = (compress env wl phi1)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.or_lid FStar_Absyn_Util.mk_disj) _154_833))
in (let hi = (let _154_834 = (compress env wl phi2)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.and_lid FStar_Absyn_Util.mk_disj) _154_834))
in (match ((low, hi)) with
| (None, None) -> begin
(let _51_1396 = (FStar_ST.op_Colon_Equals flag true)
in (let _154_835 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_154_835)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(FStar_All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
FStar_Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end
end
| _51_1414 -> begin
FStar_Util.Inl (phi)
end))))

let rec eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (let t1 = (FStar_Absyn_Util.compress_typ t1)
in (let t2 = (FStar_Absyn_Util.compress_typ t2)
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Typ_uvar (u1, _51_1431), FStar_Absyn_Syntax.Typ_uvar (u2, _51_1436)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Absyn_Syntax.Typ_app (h1, args1), FStar_Absyn_Syntax.Typ_app (h2, args2)) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _51_1450 -> begin
false
end))))
and eq_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e1 e2 -> (let e1 = (FStar_Absyn_Util.compress_exp e1)
in (let e2 = (FStar_Absyn_Util.compress_exp e2)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (a), FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _51_1462), FStar_Absyn_Syntax.Exp_fvar (g, _51_1467)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Exp_constant (c), FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (FStar_Absyn_Syntax.Exp_app (h1, args1), FStar_Absyn_Syntax.Exp_app (h2, args2)) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _51_1486 -> begin
false
end))))
and eq_args : FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.args  ->  Prims.bool = (fun a1 a2 -> if ((FStar_List.length a1) = (FStar_List.length a2)) then begin
(FStar_List.forall2 (fun a1 a2 -> (match ((a1, a2)) with
| ((FStar_Util.Inl (t), _51_1494), (FStar_Util.Inl (s), _51_1499)) -> begin
(eq_typ t s)
end
| ((FStar_Util.Inr (e), _51_1505), (FStar_Util.Inr (f), _51_1510)) -> begin
(eq_exp e f)
end
| _51_1514 -> begin
false
end)) a1 a2)
end else begin
false
end)

type flex_t =
(FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.args)

type im_or_proj_t =
((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.arg Prims.list * FStar_Absyn_Syntax.binders * ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ  ->  Prims.bool) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list))

let rigid_rigid : Prims.int = 0

let flex_rigid_eq : Prims.int = 1

let flex_refine_inner : Prims.int = 2

let flex_refine : Prims.int = 3

let flex_rigid : Prims.int = 4

let rigid_flex : Prims.int = 5

let refine_flex : Prims.int = 6

let flex_flex : Prims.int = 7

let compress_prob : worklist  ->  prob  ->  prob = (fun wl p -> (match (p) with
| KProb (p) -> begin
(let _154_865 = (let _51_1519 = p
in (let _154_863 = (compress_k wl.tcenv wl p.lhs)
in (let _154_862 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _154_863; relation = _51_1519.relation; rhs = _154_862; element = _51_1519.element; logical_guard = _51_1519.logical_guard; scope = _51_1519.scope; reason = _51_1519.reason; loc = _51_1519.loc; rank = _51_1519.rank})))
in (FStar_All.pipe_right _154_865 (fun _154_864 -> KProb (_154_864))))
end
| TProb (p) -> begin
(let _154_869 = (let _51_1523 = p
in (let _154_867 = (compress wl.tcenv wl p.lhs)
in (let _154_866 = (compress wl.tcenv wl p.rhs)
in {lhs = _154_867; relation = _51_1523.relation; rhs = _154_866; element = _51_1523.element; logical_guard = _51_1523.logical_guard; scope = _51_1523.scope; reason = _51_1523.reason; loc = _51_1523.loc; rank = _51_1523.rank})))
in (FStar_All.pipe_right _154_869 (fun _154_868 -> TProb (_154_868))))
end
| EProb (p) -> begin
(let _154_873 = (let _51_1527 = p
in (let _154_871 = (compress_e wl.tcenv wl p.lhs)
in (let _154_870 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _154_871; relation = _51_1527.relation; rhs = _154_870; element = _51_1527.element; logical_guard = _51_1527.logical_guard; scope = _51_1527.scope; reason = _51_1527.reason; loc = _51_1527.loc; rank = _51_1527.rank})))
in (FStar_All.pipe_right _154_873 (fun _154_872 -> EProb (_154_872))))
end
| CProb (_51_1530) -> begin
p
end))

let rank : worklist  ->  prob  ->  (Prims.int * prob) = (fun wl prob -> (let prob = (let _154_878 = (compress_prob wl prob)
in (FStar_All.pipe_right _154_878 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(let rank = (match ((kp.lhs.FStar_Absyn_Syntax.n, kp.rhs.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_uvar (_51_1538), FStar_Absyn_Syntax.Kind_uvar (_51_1541)) -> begin
flex_flex
end
| (FStar_Absyn_Syntax.Kind_uvar (_51_1545), _51_1548) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
flex_rigid
end
end
| (_51_1551, FStar_Absyn_Syntax.Kind_uvar (_51_1553)) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
rigid_flex
end
end
| (_51_1557, _51_1559) -> begin
rigid_rigid
end)
in (let _154_880 = (FStar_All.pipe_right (let _51_1562 = kp
in {lhs = _51_1562.lhs; relation = _51_1562.relation; rhs = _51_1562.rhs; element = _51_1562.element; logical_guard = _51_1562.logical_guard; scope = _51_1562.scope; reason = _51_1562.reason; loc = _51_1562.loc; rank = Some (rank)}) (fun _154_879 -> KProb (_154_879)))
in (rank, _154_880)))
end
| TProb (tp) -> begin
(let _51_1569 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_51_1569) with
| (lh, _51_1568) -> begin
(let _51_1573 = (FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_51_1573) with
| (rh, _51_1572) -> begin
(let _51_1629 = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_51_1575), FStar_Absyn_Syntax.Typ_uvar (_51_1578)) -> begin
(flex_flex, tp)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Absyn_Syntax.Typ_uvar (_51_1594), _51_1597) -> begin
(let _51_1601 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_51_1601) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _51_1604 -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _154_882 = (let _51_1606 = tp
in (let _154_881 = (force_refinement (b, ref_opt))
in {lhs = _51_1606.lhs; relation = _51_1606.relation; rhs = _154_881; element = _51_1606.element; logical_guard = _51_1606.logical_guard; scope = _51_1606.scope; reason = _51_1606.reason; loc = _51_1606.loc; rank = _51_1606.rank}))
in (rank, _154_882)))
end)
end))
end
| (_51_1609, FStar_Absyn_Syntax.Typ_uvar (_51_1611)) -> begin
(let _51_1616 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_51_1616) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _51_1619 -> begin
(let _154_884 = (let _51_1620 = tp
in (let _154_883 = (force_refinement (b, ref_opt))
in {lhs = _154_883; relation = _51_1620.relation; rhs = _51_1620.rhs; element = _51_1620.element; logical_guard = _51_1620.logical_guard; scope = _51_1620.scope; reason = _51_1620.reason; loc = _51_1620.loc; rank = _51_1620.rank}))
in (refine_flex, _154_884))
end)
end))
end
| (_51_1623, _51_1625) -> begin
(rigid_rigid, tp)
end)
in (match (_51_1629) with
| (rank, tp) -> begin
(let _154_886 = (FStar_All.pipe_right (let _51_1630 = tp
in {lhs = _51_1630.lhs; relation = _51_1630.relation; rhs = _51_1630.rhs; element = _51_1630.element; logical_guard = _51_1630.logical_guard; scope = _51_1630.scope; reason = _51_1630.reason; loc = _51_1630.loc; rank = Some (rank)}) (fun _154_885 -> TProb (_154_885)))
in (rank, _154_886))
end))
end))
end))
end
| EProb (ep) -> begin
(let _51_1637 = (FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_51_1637) with
| (lh, _51_1636) -> begin
(let _51_1641 = (FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_51_1641) with
| (rh, _51_1640) -> begin
(let rank = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_uvar (_51_1643), FStar_Absyn_Syntax.Exp_uvar (_51_1646)) -> begin
flex_flex
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_51_1662, _51_1664) -> begin
rigid_rigid
end)
in (let _154_888 = (FStar_All.pipe_right (let _51_1667 = ep
in {lhs = _51_1667.lhs; relation = _51_1667.relation; rhs = _51_1667.rhs; element = _51_1667.element; logical_guard = _51_1667.logical_guard; scope = _51_1667.scope; reason = _51_1667.reason; loc = _51_1667.loc; rank = Some (rank)}) (fun _154_887 -> EProb (_154_887)))
in (rank, _154_888)))
end))
end))
end
| CProb (cp) -> begin
(let _154_890 = (FStar_All.pipe_right (let _51_1671 = cp
in {lhs = _51_1671.lhs; relation = _51_1671.relation; rhs = _51_1671.rhs; element = _51_1671.element; logical_guard = _51_1671.logical_guard; scope = _51_1671.scope; reason = _51_1671.reason; loc = _51_1671.loc; rank = Some (rigid_rigid)}) (fun _154_889 -> CProb (_154_889)))
in (rigid_rigid, _154_890))
end)))

let next_prob : worklist  ->  (prob Prims.option * prob Prims.list * Prims.int) = (fun wl -> (let rec aux = (fun _51_1678 probs -> (match (_51_1678) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _51_1686 = (rank wl hd)
in (match (_51_1686) with
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

let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

let rec solve_flex_rigid_join : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (let _51_1697 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_940 = (prob_to_string env (TProb (tp)))
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _154_940))
end else begin
()
end
in (let _51_1701 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_51_1701) with
| (u, args) -> begin
(let _51_1707 = (0, 1, 2, 3, 4)
in (match (_51_1707) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun t1 t2 -> (let _51_1716 = (FStar_Absyn_Util.head_and_args t1)
in (match (_51_1716) with
| (h1, args1) -> begin
(let _51_1720 = (FStar_Absyn_Util.head_and_args t2)
in (match (_51_1720) with
| (h2, _51_1719) -> begin
(match ((h1.FStar_Absyn_Syntax.n, h2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (tc1), FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
if (FStar_Ident.lid_equals tc1.FStar_Absyn_Syntax.v tc2.FStar_Absyn_Syntax.v) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _154_952 = (let _154_951 = (let _154_950 = (new_problem env t1 EQ t2 None t1.FStar_Absyn_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _154_949 -> TProb (_154_949)) _154_950))
in (_154_951)::[])
in Some (_154_952))
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
| _51_1732 -> begin
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
(let phi2 = (let _154_957 = (FStar_Absyn_Util.mk_subst_one_binder (FStar_Absyn_Syntax.v_binder x) (FStar_Absyn_Syntax.v_binder y))
in (FStar_Absyn_Util.subst_typ _154_957 phi2))
in (let _154_961 = (let _154_960 = (let _154_959 = (let _154_958 = (FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _154_958))
in (FStar_Absyn_Syntax.mk_Typ_refine _154_959 (Some (FStar_Absyn_Syntax.ktype)) t1.FStar_Absyn_Syntax.pos))
in (_154_960, m))
in Some (_154_961)))
end))
end
| (_51_1751, FStar_Absyn_Syntax.Typ_refine (y, _51_1754)) -> begin
(let m = (base_types_match t1 y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _51_1764), _51_1768) -> begin
(let m = (base_types_match x.FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _51_1775 -> begin
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
| FStar_Absyn_Syntax.Typ_uvar (uv, _51_1783) -> begin
(let _51_1808 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _51_30 -> (match (_51_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _51_1794 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_51_1794) with
| (u', _51_1793) -> begin
(match ((let _154_963 = (compress env wl u')
in _154_963.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv', _51_1797) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _51_1801 -> begin
false
end)
end))
end
| _51_1803 -> begin
false
end)
end
| _51_1805 -> begin
false
end))))
in (match (_51_1808) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _51_1812 tps -> (match (_51_1812) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _154_968 = (compress env wl hd.rhs)
in (conjoin bound _154_968))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _51_1825 -> begin
None
end)
end))
in (match ((let _154_970 = (let _154_969 = (compress env wl tp.rhs)
in (_154_969, []))
in (make_upper_bound _154_970 upper_bounds))) with
| None -> begin
(let _51_1827 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (let _51_1834 = wl
in {attempting = sub_probs; wl_deferred = _51_1834.wl_deferred; subst = _51_1834.subst; ctr = _51_1834.ctr; slack_vars = _51_1834.slack_vars; defer_ok = _51_1834.defer_ok; smt_ok = _51_1834.smt_ok; tcenv = _51_1834.tcenv}))) with
| Success (subst, _51_1838) -> begin
(let wl = (let _51_1841 = wl
in {attempting = rest; wl_deferred = _51_1841.wl_deferred; subst = []; ctr = _51_1841.ctr; slack_vars = _51_1841.slack_vars; defer_ok = _51_1841.defer_ok; smt_ok = _51_1841.smt_ok; tcenv = _51_1841.tcenv})
in (let wl = (solve_prob (TProb (tp)) None subst wl)
in (let _51_1847 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _51_1850 -> begin
None
end))
end))
end))
end
| _51_1852 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve : FStar_Tc_Env.env  ->  worklist  ->  solution = (fun env probs -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _51_1860 = probs
in {attempting = tl; wl_deferred = _51_1860.wl_deferred; subst = _51_1860.subst; ctr = _51_1860.ctr; slack_vars = _51_1860.slack_vars; defer_ok = _51_1860.defer_ok; smt_ok = _51_1860.smt_ok; tcenv = _51_1860.tcenv})
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
| (None, _51_1876, _51_1878) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _51_1882 -> begin
(let _51_1891 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _51_1888 -> (match (_51_1888) with
| (c, _51_1885, _51_1887) -> begin
(c < probs.ctr)
end))))
in (match (_51_1891) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _154_979 = (let _154_978 = (let _154_977 = (FStar_List.map (fun _51_1897 -> (match (_51_1897) with
| (_51_1894, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in {carry = _154_977; slack = probs.slack_vars})
in (probs.subst, _154_978))
in Success (_154_979))
end
| _51_1899 -> begin
(let _154_982 = (let _51_1900 = probs
in (let _154_981 = (FStar_All.pipe_right attempt (FStar_List.map (fun _51_1907 -> (match (_51_1907) with
| (_51_1903, _51_1905, y) -> begin
y
end))))
in {attempting = _154_981; wl_deferred = rest; subst = _51_1900.subst; ctr = _51_1900.ctr; slack_vars = _51_1900.slack_vars; defer_ok = _51_1900.defer_ok; smt_ok = _51_1900.smt_ok; tcenv = _51_1900.tcenv}))
in (solve env _154_982))
end)
end))
end)
end))
and solve_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  prob  ->  worklist  ->  (FStar_Absyn_Syntax.binders  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.subst_elt Prims.list  ->  prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs scope env subst)
in (let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula))))
end
| (((FStar_Util.Inl (_), _)::_, (FStar_Util.Inr (_), _)::_)) | (((FStar_Util.Inr (_), _)::_, (FStar_Util.Inl (_), _)::_)) -> begin
FStar_Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(let subst = (let _154_1008 = (FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (FStar_List.append _154_1008 subst))
in (let env = (let _154_1009 = (FStar_Tc_Env.binding_of_binder hd2)
in (FStar_Tc_Env.push_local_binding env _154_1009))
in (let prob = (match (((Prims.fst hd1), (Prims.fst hd2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _154_1013 = (let _154_1012 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _154_1011 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _154_1012 _154_1011 b.FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (FStar_All.pipe_left (fun _154_1010 -> KProb (_154_1010)) _154_1013))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _154_1017 = (let _154_1016 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _154_1015 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _154_1016 _154_1015 y.FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (FStar_All.pipe_left (fun _154_1014 -> TProb (_154_1014)) _154_1017))
end
| _51_1983 -> begin
(FStar_All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| FStar_Util.Inr (msg) -> begin
FStar_Util.Inr (msg)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _154_1019 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _154_1018 = (FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (FStar_Absyn_Util.mk_conj _154_1019 _154_1018)))
in FStar_Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _51_1993 -> begin
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
and solve_k : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _51_2008 -> begin
(FStar_All.failwith "impossible")
end))
and solve_k' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (let orig = KProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _154_1026 = (solve_prob orig None [] wl)
in (solve env _154_1026))
end else begin
(let k1 = problem.lhs
in (let k2 = problem.rhs
in if (FStar_Util.physical_equality k1 k2) then begin
(let _154_1027 = (solve_prob orig None [] wl)
in (solve env _154_1027))
end else begin
(let r = (FStar_Tc_Env.get_range env)
in (let imitate_k = (fun _51_2024 -> (match (_51_2024) with
| (rel, u, ps, xs, (h, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let _51_2029 = (imitation_sub_probs orig env xs ps qs)
in (match (_51_2029) with
| (sub_probs, gs_xs, f) -> begin
(let im = (let _154_1043 = (let _154_1042 = (h gs_xs)
in (xs, _154_1042))
in (FStar_Absyn_Syntax.mk_Kind_lam _154_1043 r))
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
in (let _154_1052 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _154_1052)))
end else begin
(let _154_1057 = (let _154_1056 = (FStar_All.pipe_right xs FStar_Absyn_Util.args_of_non_null_binders)
in (let _154_1055 = (decompose_kind env k)
in (rel, u, _154_1056, xs, _154_1055)))
in (imitate_k _154_1057))
end)))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.FStar_Absyn_Syntax.n, k2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Kind_type, FStar_Absyn_Syntax.Kind_type)) | ((FStar_Absyn_Syntax.Kind_effect, FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _154_1058 = (solve_prob orig None [] wl)
in (FStar_All.pipe_left (solve env) _154_1058))
end
| (FStar_Absyn_Syntax.Kind_abbrev (_51_2052, k1), _51_2057) -> begin
(solve_k env (let _51_2059 = problem
in {lhs = k1; relation = _51_2059.relation; rhs = _51_2059.rhs; element = _51_2059.element; logical_guard = _51_2059.logical_guard; scope = _51_2059.scope; reason = _51_2059.reason; loc = _51_2059.loc; rank = _51_2059.rank}) wl)
end
| (_51_2062, FStar_Absyn_Syntax.Kind_abbrev (_51_2064, k2)) -> begin
(solve_k env (let _51_2069 = problem
in {lhs = _51_2069.lhs; relation = _51_2069.relation; rhs = k2; element = _51_2069.element; logical_guard = _51_2069.logical_guard; scope = _51_2069.scope; reason = _51_2069.reason; loc = _51_2069.loc; rank = _51_2069.rank}) wl)
end
| (FStar_Absyn_Syntax.Kind_arrow (bs1, k1'), FStar_Absyn_Syntax.Kind_arrow (bs2, k2')) -> begin
(let sub_prob = (fun scope env subst -> (let _154_1067 = (let _154_1066 = (FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _154_1066 problem.relation k2' None "Arrow-kind result"))
in (FStar_All.pipe_left (fun _154_1065 -> KProb (_154_1065)) _154_1067)))
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
in (let _51_2112 = (new_kvar r zs)
in (match (_51_2112) with
| (u, _51_2111) -> begin
(let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (let k2 = (FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end
end)))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, args), _51_2121) -> begin
(flex_rigid problem.relation u args k2)
end
| (_51_2124, FStar_Absyn_Syntax.Kind_uvar (u, args)) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, FStar_Absyn_Syntax.Kind_unknown)) -> begin
(FStar_All.failwith "Impossible")
end
| _51_2151 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end))
end))
and solve_t : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _51_2159 -> begin
(FStar_All.failwith "Impossible")
end)))
and solve_t' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> if wl.defer_ok then begin
(let _51_2166 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1078 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _154_1078 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
in (let imitate_t = (fun orig env wl p -> (let _51_2183 = p
in (match (_51_2183) with
| ((u, k), ps, xs, (h, _51_2180, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_Tc_Env.get_range env)
in (let _51_2189 = (imitation_sub_probs orig env xs ps qs)
in (match (_51_2189) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _154_1090 = (let _154_1089 = (h gs_xs)
in (xs, _154_1089))
in (FStar_Absyn_Syntax.mk_Typ_lam' _154_1090 None r))
in (let _51_2191 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1095 = (FStar_Absyn_Print.typ_to_string im)
in (let _154_1094 = (FStar_Absyn_Print.tag_of_typ im)
in (let _154_1093 = (let _154_1091 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _154_1091 (FStar_String.concat ", ")))
in (let _154_1092 = (FStar_Tc_Normalize.formula_norm_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _154_1095 _154_1094 _154_1093 _154_1092)))))
end else begin
()
end
in (let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project_t = (fun orig env wl i p -> (let _51_2207 = p
in (match (_51_2207) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_Tc_Env.get_range env)
in (let pi = (FStar_List.nth ps i)
in (let rec gs = (fun k -> (let _51_2214 = (FStar_Absyn_Util.kind_formals k)
in (match (_51_2214) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(let _51_2243 = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let k_a = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _51_2227 = (new_tvar r xs k_a)
in (match (_51_2227) with
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
in (let _51_2236 = (new_evar r xs t_x)
in (match (_51_2236) with
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
in (match (_51_2243) with
| (gi_xs, gi_ps, subst) -> begin
(let _51_2246 = (aux subst tl)
in (match (_51_2246) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _154_1115 = (let _154_1114 = (FStar_List.nth xs i)
in (FStar_All.pipe_left Prims.fst _154_1114))
in ((Prims.fst pi), _154_1115))) with
| (FStar_Util.Inl (pi), FStar_Util.Inl (xi)) -> begin
if (let _154_1116 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _154_1116)) then begin
None
end else begin
(let _51_2255 = (gs xi.FStar_Absyn_Syntax.sort)
in (match (_51_2255) with
| (g_xs, _51_2254) -> begin
(let xi = (FStar_Absyn_Util.btvar_to_typ xi)
in (let proj = (let _154_1118 = (let _154_1117 = (FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (FStar_Absyn_Syntax.ktype)) r)
in (xs, _154_1117))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_1118 None r))
in (let sub = (let _154_1124 = (let _154_1123 = (FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (FStar_Absyn_Syntax.ktype)) r)
in (let _154_1122 = (let _154_1121 = (FStar_List.map (fun _51_2263 -> (match (_51_2263) with
| (_51_2259, _51_2261, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _154_1121))
in (mk_problem (p_scope orig) orig _154_1123 (p_rel orig) _154_1122 None "projection")))
in (FStar_All.pipe_left (fun _154_1119 -> TProb (_154_1119)) _154_1124))
in (let _51_2265 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1126 = (FStar_Absyn_Print.typ_to_string proj)
in (let _154_1125 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _154_1126 _154_1125)))
end else begin
()
end
in (let wl = (let _154_1128 = (let _154_1127 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_154_1127))
in (solve_prob orig _154_1128 ((UT ((u, proj)))::[]) wl))
in (let _154_1130 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _154_1129 -> Some (_154_1129)) _154_1130)))))))
end))
end
end
| _51_2269 -> begin
None
end))))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _51_2281 = lhs
in (match (_51_2281) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _154_1157 = (FStar_Absyn_Util.kind_formals k)
in (FStar_All.pipe_right _154_1157 Prims.fst))
in (let xs = (FStar_Absyn_Util.name_binders xs)
in (let _154_1162 = (decompose_typ env t2)
in ((uv, k), ps, xs, _154_1162)))))
in (let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
if (i = (- (1))) then begin
(match ((imitate_t orig env wl st)) with
| Failed (_51_2291) -> begin
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
in (let check_head = (fun fvs1 t2 -> (let _51_2307 = (FStar_Absyn_Util.head_and_args t2)
in (match (_51_2307) with
| (hd, _51_2306) -> begin
(match (hd.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _51_2318 -> begin
(let fvs_hd = (FStar_Absyn_Util.freevars_typ hd)
in if (FStar_Absyn_Util.fvs_included fvs_hd fvs1) then begin
true
end else begin
(let _51_2320 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1173 = (FStar_Absyn_Print.freevars_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _154_1173))
end else begin
()
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _154_1177 = (let _154_1176 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _154_1176 Prims.fst))
in (FStar_All.pipe_right _154_1177 FStar_Absyn_Util.freevars_typ))
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
in (let _51_2333 = (occurs_check env wl (uv, k) t2)
in (match (_51_2333) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _154_1179 = (let _154_1178 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _154_1178))
in (giveup_or_defer orig _154_1179))
end else begin
if (FStar_Absyn_Util.fvs_included fvs2 fvs1) then begin
if ((FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ)) then begin
(let _154_1180 = (subterms args_lhs)
in (imitate_t orig env wl _154_1180))
end else begin
(let _51_2334 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1183 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1182 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _154_1181 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _154_1183 _154_1182 _154_1181))))
end else begin
()
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _51_2338 -> begin
(let _154_1185 = (let _154_1184 = (sn_binders env vars)
in (_154_1184, t2))
in (FStar_Absyn_Syntax.mk_Typ_lam _154_1185 None t1.FStar_Absyn_Syntax.pos))
end)
in (let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _51_2341 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1188 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1187 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _154_1186 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _154_1188 _154_1187 _154_1186))))
end else begin
()
end
in (let _154_1189 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _154_1189 (- (1)))))
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
if (let _154_1190 = (FStar_Absyn_Util.freevars_typ t1)
in (check_head _154_1190 t2)) then begin
(let im_ok = (imitate_ok t2)
in (let _51_2345 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1191 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _154_1191 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _154_1192 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _154_1192 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun xs_opt _51_2357 -> (match (_51_2357) with
| (t, u, k, args) -> begin
(let rec aux = (fun binders ys args -> (match (args) with
| [] -> begin
(let ys = (FStar_List.rev ys)
in (let binders = (FStar_List.rev binders)
in (let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _51_2369 = (new_tvar t.FStar_Absyn_Syntax.pos ys kk)
in (match (_51_2369) with
| (t', _51_2368) -> begin
(let _51_2375 = (destruct_flex_t t')
in (match (_51_2375) with
| (u1_ys, u1, k1, _51_2374) -> begin
(let sol = (let _154_1210 = (let _154_1209 = (FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((u, k), _154_1209))
in UT (_154_1210))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(let new_binder = (fun hd -> (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let _154_1214 = (let _154_1213 = (FStar_Tc_Recheck.recompute_kind a)
in (FStar_All.pipe_right _154_1213 (FStar_Absyn_Util.gen_bvar_p a.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _154_1214 FStar_Absyn_Syntax.t_binder))
end
| FStar_Util.Inr (x) -> begin
(let _154_1216 = (let _154_1215 = (FStar_Tc_Recheck.recompute_typ x)
in (FStar_All.pipe_right _154_1215 (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _154_1216 FStar_Absyn_Syntax.v_binder))
end))
in (let _51_2394 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _154_1217 = (new_binder hd)
in (_154_1217, ys))
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
(let _154_1218 = (new_binder hd)
in (_154_1218, ys))
end
end)
end)
in (match (_51_2394) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (let solve_both_pats = (fun wl _51_2400 _51_2404 k r -> (match ((_51_2400, _51_2404)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _154_1229 = (solve_prob orig None [] wl)
in (solve env _154_1229))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _51_2413 = (new_tvar r zs k)
in (match (_51_2413) with
| (u_zs, _51_2412) -> begin
(let sub1 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (let _51_2417 = (occurs_check env wl (u1, k1) sub1)
in (match (_51_2417) with
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
in (let _51_2423 = (occurs_check env wl (u2, k2) sub2)
in (match (_51_2423) with
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
in (let solve_one_pat = (fun _51_2431 _51_2436 -> (match ((_51_2431, _51_2436)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _51_2437 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1235 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1234 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _154_1235 _154_1234)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let sub_probs = (FStar_List.map2 (fun a b -> (let a = (FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Prims.fst a), (Prims.fst b))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _154_1239 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _154_1239 (fun _154_1238 -> TProb (_154_1238))))
end
| (FStar_Util.Inr (t1), FStar_Util.Inr (t2)) -> begin
(let _154_1241 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _154_1241 (fun _154_1240 -> EProb (_154_1240))))
end
| _51_2453 -> begin
(FStar_All.failwith "Impossible")
end))) xs args2)
in (let guard = (let _154_1243 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _154_1243))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Absyn_Util.freevars_typ t2)
in (let _51_2463 = (occurs_check env wl (u1, k1) t2)
in (match (_51_2463) with
| (occurs_ok, _51_2462) -> begin
(let lhs_vars = (FStar_Absyn_Syntax.freevars_of_binders xs)
in if (occurs_ok && (FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)) then begin
(let sol = (let _154_1245 = (let _154_1244 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.FStar_Absyn_Syntax.pos)
in ((u1, k1), _154_1244))
in UT (_154_1245))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(let _51_2474 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_51_2474) with
| (sol, (_51_2469, u2, k2, ys)) -> begin
(let wl = (extend_solution sol wl)
in (let _51_2476 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _154_1246 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _154_1246))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _51_2481 -> begin
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
in (let _51_2486 = lhs
in (match (_51_2486) with
| (t1, u1, k1, args1) -> begin
(let _51_2491 = rhs
in (match (_51_2491) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _154_1247 = (FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _154_1247 t2.FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _51_2509 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _51_2513 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_51_2513) with
| (sol, _51_2512) -> begin
(let wl = (extend_solution sol wl)
in (let _51_2515 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _154_1248 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _154_1248))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _51_2520 -> begin
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
(let _154_1249 = (solve_prob orig None [] wl)
in (solve env _154_1249))
end else begin
(let t1 = problem.lhs
in (let t2 = problem.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _154_1250 = (solve_prob orig None [] wl)
in (solve env _154_1250))
end else begin
(let _51_2524 = if (FStar_Tc_Env.debug env (FStar_Options.Other ("Rel"))) then begin
(let _154_1253 = (prob_to_string env orig)
in (let _154_1252 = (let _154_1251 = (FStar_List.map (uvi_to_string wl.tcenv) wl.subst)
in (FStar_All.pipe_right _154_1251 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Attempting %s\n\tSubst is %s\n" _154_1253 _154_1252)))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let match_num_binders = (fun _51_2529 _51_2532 -> (match ((_51_2529, _51_2532)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _51_2539 = (FStar_Util.first_N n bs)
in (match (_51_2539) with
| (bs, rest) -> begin
(let _154_1283 = (mk_cod rest)
in (bs, _154_1283))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _154_1287 = (let _154_1284 = (mk_cod1 [])
in (bs1, _154_1284))
in (let _154_1286 = (let _154_1285 = (mk_cod2 [])
in (bs2, _154_1285))
in (_154_1287, _154_1286)))
end else begin
if (l1 > l2) then begin
(let _154_1290 = (curry l2 bs1 mk_cod1)
in (let _154_1289 = (let _154_1288 = (mk_cod2 [])
in (bs2, _154_1288))
in (_154_1290, _154_1289)))
end else begin
(let _154_1293 = (let _154_1291 = (mk_cod1 [])
in (bs1, _154_1291))
in (let _154_1292 = (curry l1 bs2 mk_cod2)
in (_154_1293, _154_1292)))
end
end)))
end))
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (FStar_Absyn_Util.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
(let _154_1294 = (solve_prob orig None [] wl)
in (solve env _154_1294))
end else begin
(let _154_1298 = (let _154_1297 = (let _154_1296 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _154_1295 -> Some (_154_1295)) _154_1296))
in (solve_prob orig _154_1297 [] wl))
in (solve env _154_1298))
end
end
| (FStar_Absyn_Syntax.Typ_fun (bs1, c1), FStar_Absyn_Syntax.Typ_fun (bs2, c2)) -> begin
(let mk_c = (fun c _51_31 -> (match (_51_31) with
| [] -> begin
c
end
| bs -> begin
(let _154_1303 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Total _154_1303))
end))
in (let _51_2570 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_51_2570) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Absyn_Util.subst_comp subst c1)
in (let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
EQ
end else begin
problem.relation
end
in (let _51_2576 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(let _154_1310 = (let _154_1309 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_right _154_1309 FStar_Range.string_of_range))
in (FStar_Util.print2 "(%s) Using relation %s at higher order\n" _154_1310 (rel_to_string rel)))
end else begin
()
end
in (let _154_1312 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _154_1311 -> CProb (_154_1311)) _154_1312)))))))
end)))
end
| (FStar_Absyn_Syntax.Typ_lam (bs1, t1'), FStar_Absyn_Syntax.Typ_lam (bs2, t2')) -> begin
(let mk_t = (fun t _51_32 -> (match (_51_32) with
| [] -> begin
t
end
| bs -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end))
in (let _51_2598 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_51_2598) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let t1' = (FStar_Absyn_Util.subst_typ subst t1')
in (let _154_1323 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (FStar_All.pipe_left (fun _154_1322 -> TProb (_154_1322)) _154_1323)))))
end)))
end
| (FStar_Absyn_Syntax.Typ_refine (_51_2604), FStar_Absyn_Syntax.Typ_refine (_51_2607)) -> begin
(let _51_2612 = (as_refinement env wl t1)
in (match (_51_2612) with
| (x1, phi1) -> begin
(let _51_2615 = (as_refinement env wl t2)
in (match (_51_2615) with
| (x2, phi2) -> begin
(let base_prob = (let _154_1325 = (mk_problem (p_scope orig) orig x1.FStar_Absyn_Syntax.sort problem.relation x2.FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (FStar_All.pipe_left (fun _154_1324 -> TProb (_154_1324)) _154_1325))
in (let x1_for_x2 = (FStar_Absyn_Util.mk_subst_one_binder (FStar_Absyn_Syntax.v_binder x1) (FStar_Absyn_Syntax.v_binder x2))
in (let phi2 = (FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (let mk_imp = (fun imp phi1 phi2 -> (let _154_1342 = (imp phi1 phi2)
in (FStar_All.pipe_right _154_1342 (guard_on_element problem x1))))
in (let fallback = (fun _51_2624 -> (match (()) with
| () -> begin
(let impl = if (problem.relation = EQ) then begin
(mk_imp FStar_Absyn_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Absyn_Util.mk_imp phi1 phi2)
end
in (let guard = (let _154_1345 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _154_1345 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.relation = EQ) then begin
(let ref_prob = (let _154_1347 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _154_1346 -> TProb (_154_1346)) _154_1347))
in (match ((solve env (let _51_2629 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; subst = _51_2629.subst; ctr = _51_2629.ctr; slack_vars = _51_2629.slack_vars; defer_ok = false; smt_ok = _51_2629.smt_ok; tcenv = _51_2629.tcenv}))) with
| Failed (_51_2632) -> begin
(fallback ())
end
| Success (subst, _51_2636) -> begin
(let guard = (let _154_1350 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _154_1349 = (let _154_1348 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _154_1348 (guard_on_element problem x1)))
in (FStar_Absyn_Util.mk_conj _154_1350 _154_1349)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _51_2641 = wl
in {attempting = _51_2641.attempting; wl_deferred = _51_2641.wl_deferred; subst = subst; ctr = (wl.ctr + 1); slack_vars = _51_2641.slack_vars; defer_ok = _51_2641.defer_ok; smt_ok = _51_2641.smt_ok; tcenv = _51_2641.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end)))))
end))
end))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _154_1352 = (destruct_flex_t t1)
in (let _154_1351 = (destruct_flex_t t2)
in (flex_flex orig _154_1352 _154_1351)))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) when (problem.relation = EQ) -> begin
(let _154_1353 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _154_1353 t2 wl))
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
in if (let _154_1354 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _154_1354)) then begin
(let _154_1357 = (FStar_All.pipe_left (fun _154_1355 -> TProb (_154_1355)) (let _51_2800 = problem
in {lhs = _51_2800.lhs; relation = new_rel; rhs = _51_2800.rhs; element = _51_2800.element; logical_guard = _51_2800.logical_guard; scope = _51_2800.scope; reason = _51_2800.reason; loc = _51_2800.loc; rank = _51_2800.rank}))
in (let _154_1356 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _154_1357 _154_1356 t2 wl)))
end else begin
(let _51_2804 = (base_and_refinement env wl t2)
in (match (_51_2804) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _154_1360 = (FStar_All.pipe_left (fun _154_1358 -> TProb (_154_1358)) (let _51_2806 = problem
in {lhs = _51_2806.lhs; relation = new_rel; rhs = _51_2806.rhs; element = _51_2806.element; logical_guard = _51_2806.logical_guard; scope = _51_2806.scope; reason = _51_2806.reason; loc = _51_2806.loc; rank = _51_2806.rank}))
in (let _154_1359 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _154_1360 _154_1359 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _51_2812 = y
in {FStar_Absyn_Syntax.v = _51_2812.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t1; FStar_Absyn_Syntax.p = _51_2812.FStar_Absyn_Syntax.p})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _154_1362 = (mk_problem problem.scope orig t1 new_rel y.FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _154_1361 -> TProb (_154_1361)) _154_1362))
in (let guard = (let _154_1363 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _154_1363 impl))
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
(let _51_2847 = (base_and_refinement env wl t1)
in (match (_51_2847) with
| (t_base, _51_2846) -> begin
(solve_t env (let _51_2848 = problem
in {lhs = t_base; relation = EQ; rhs = _51_2848.rhs; element = _51_2848.element; logical_guard = _51_2848.logical_guard; scope = _51_2848.scope; reason = _51_2848.reason; loc = _51_2848.loc; rank = _51_2848.rank}) wl)
end))
end
end
| (FStar_Absyn_Syntax.Typ_refine (_51_2851), _51_2854) -> begin
(let t2 = (let _154_1364 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _154_1364))
in (solve_t env (let _51_2857 = problem
in {lhs = _51_2857.lhs; relation = _51_2857.relation; rhs = t2; element = _51_2857.element; logical_guard = _51_2857.logical_guard; scope = _51_2857.scope; reason = _51_2857.reason; loc = _51_2857.loc; rank = _51_2857.rank}) wl))
end
| (_51_2860, FStar_Absyn_Syntax.Typ_refine (_51_2862)) -> begin
(let t1 = (let _154_1365 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _154_1365))
in (solve_t env (let _51_2866 = problem
in {lhs = t1; relation = _51_2866.relation; rhs = _51_2866.rhs; element = _51_2866.element; logical_guard = _51_2866.logical_guard; scope = _51_2866.scope; reason = _51_2866.reason; loc = _51_2866.loc; rank = _51_2866.rank}) wl))
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) | ((FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, FStar_Absyn_Syntax.Typ_const (_))) | ((_, FStar_Absyn_Syntax.Typ_app (_))) -> begin
(let _51_2906 = (head_matches_delta env wl t1 t2)
in (match (_51_2906) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _51_2909) -> begin
(let head1 = (let _154_1366 = (FStar_Absyn_Util.head_and_args t1)
in (FStar_All.pipe_right _154_1366 Prims.fst))
in (let head2 = (let _154_1367 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _154_1367 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_51_2916) -> begin
true
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Tc_Env.is_projector env tc.FStar_Absyn_Syntax.v)
end
| _51_2921 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _154_1373 = (let _154_1372 = (let _154_1371 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _154_1370 -> Some (_154_1370)) _154_1371))
in (solve_prob orig _154_1372 [] wl))
in (solve env _154_1373))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_51_2923, Some (t1, t2)) -> begin
(solve_t env (let _51_2929 = problem
in {lhs = t1; relation = _51_2929.relation; rhs = t2; element = _51_2929.element; logical_guard = _51_2929.logical_guard; scope = _51_2929.scope; reason = _51_2929.reason; loc = _51_2929.loc; rank = _51_2929.rank}) wl)
end
| (_51_2932, None) -> begin
(let _51_2935 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1375 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1374 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Head matches: %s and %s\n" _154_1375 _154_1374)))
end else begin
()
end
in (let _51_2939 = (FStar_Absyn_Util.head_and_args t1)
in (match (_51_2939) with
| (head, args) -> begin
(let _51_2942 = (FStar_Absyn_Util.head_and_args t2)
in (match (_51_2942) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _154_1380 = (let _154_1379 = (FStar_Absyn_Print.typ_to_string head)
in (let _154_1378 = (FStar_Absyn_Print.args_to_string args)
in (let _154_1377 = (FStar_Absyn_Print.typ_to_string head')
in (let _154_1376 = (FStar_Absyn_Print.args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _154_1379 _154_1378 _154_1377 _154_1376)))))
in (giveup env _154_1380 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(let _154_1381 = (solve_prob orig None [] wl)
in (solve env _154_1381))
end else begin
(let _51_2946 = (base_and_refinement env wl t1)
in (match (_51_2946) with
| (base1, refinement1) -> begin
(let _51_2949 = (base_and_refinement env wl t2)
in (match (_51_2949) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(let _51_2953 = if ((head_matches head head) <> FullMatch) then begin
(let _154_1384 = (let _154_1383 = (FStar_Absyn_Print.typ_to_string head)
in (let _154_1382 = (FStar_Absyn_Print.typ_to_string head')
in (FStar_Util.format2 "Assertion failed: expected full match of %s and %s\n" _154_1383 _154_1382)))
in (FStar_All.failwith _154_1384))
end else begin
()
end
in (let subprobs = (FStar_List.map2 (fun a a' -> (match (((Prims.fst a), (Prims.fst a'))) with
| (FStar_Util.Inl (t), FStar_Util.Inl (t')) -> begin
(let _154_1388 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (FStar_All.pipe_left (fun _154_1387 -> TProb (_154_1387)) _154_1388))
end
| (FStar_Util.Inr (v), FStar_Util.Inr (v')) -> begin
(let _154_1390 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (FStar_All.pipe_left (fun _154_1389 -> EProb (_154_1389)) _154_1390))
end
| _51_2968 -> begin
(FStar_All.failwith "Impossible")
end)) args args')
in (let formula = (let _154_1392 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Absyn_Util.mk_conj_l _154_1392))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _51_2974 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _51_2977 = problem
in {lhs = lhs; relation = _51_2977.relation; rhs = rhs; element = _51_2977.element; logical_guard = _51_2977.logical_guard; scope = _51_2977.scope; reason = _51_2977.reason; loc = _51_2977.loc; rank = _51_2977.rank}) wl)))
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
| _51_3016 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (let c1 = problem.lhs
in (let c2 = problem.rhs
in (let orig = CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _51_3033 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (let sub_probs = (FStar_List.map2 (fun arg1 arg2 -> (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _154_1407 = (sub_prob t1 EQ t2 "effect arg")
in (FStar_All.pipe_left (fun _154_1406 -> TProb (_154_1406)) _154_1407))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _154_1409 = (sub_prob e1 EQ e2 "effect arg")
in (FStar_All.pipe_left (fun _154_1408 -> EProb (_154_1408)) _154_1409))
end
| _51_3048 -> begin
(FStar_All.failwith "impossible")
end)) c1_comp.FStar_Absyn_Syntax.effect_args c2_comp.FStar_Absyn_Syntax.effect_args)
in (let guard = (let _154_1411 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _154_1411))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _154_1412 = (solve_prob orig None [] wl)
in (solve env _154_1412))
end else begin
(let _51_3053 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1414 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _154_1413 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _154_1414 (rel_to_string problem.relation) _154_1413)))
end else begin
()
end
in (let r = (FStar_Tc_Env.get_range env)
in (let _51_3058 = (c1, c2)
in (match (_51_3058) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Absyn_Syntax.n, c2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Total (t1), FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (FStar_Absyn_Syntax.Total (_51_3065), FStar_Absyn_Syntax.Comp (_51_3068)) -> begin
(let _154_1416 = (let _51_3071 = problem
in (let _154_1415 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _154_1415; relation = _51_3071.relation; rhs = _51_3071.rhs; element = _51_3071.element; logical_guard = _51_3071.logical_guard; scope = _51_3071.scope; reason = _51_3071.reason; loc = _51_3071.loc; rank = _51_3071.rank}))
in (solve_c env _154_1416 wl))
end
| (FStar_Absyn_Syntax.Comp (_51_3074), FStar_Absyn_Syntax.Total (_51_3077)) -> begin
(let _154_1418 = (let _51_3080 = problem
in (let _154_1417 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _51_3080.lhs; relation = _51_3080.relation; rhs = _154_1417; element = _51_3080.element; logical_guard = _51_3080.logical_guard; scope = _51_3080.scope; reason = _51_3080.reason; loc = _51_3080.loc; rank = _51_3080.rank}))
in (solve_c env _154_1418 wl))
end
| (FStar_Absyn_Syntax.Comp (_51_3083), FStar_Absyn_Syntax.Comp (_51_3086)) -> begin
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
in (let _51_3093 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Absyn_Syntax.effect_name.FStar_Ident.str c2.FStar_Absyn_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_Tc_Env.monad_leq env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _154_1421 = (let _154_1420 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _154_1419 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _154_1420 _154_1419)))
in (giveup env _154_1421 orig))
end
| Some (edge) -> begin
if (problem.relation = EQ) then begin
(let _51_3113 = (match (c1.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp1), _51_3106)::(FStar_Util.Inl (wlp1), _51_3101)::[] -> begin
(wp1, wlp1)
end
| _51_3110 -> begin
(let _154_1423 = (let _154_1422 = (FStar_Range.string_of_range (FStar_Absyn_Syntax.range_of_lid c1.FStar_Absyn_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _154_1422))
in (FStar_All.failwith _154_1423))
end)
in (match (_51_3113) with
| (wp, wlp) -> begin
(let c1 = (let _154_1429 = (let _154_1428 = (let _154_1424 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _154_1424))
in (let _154_1427 = (let _154_1426 = (let _154_1425 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _154_1425))
in (_154_1426)::[])
in (_154_1428)::_154_1427))
in {FStar_Absyn_Syntax.effect_name = c2.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _154_1429; FStar_Absyn_Syntax.flags = c1.FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _51_33 -> (match (_51_33) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.MLEFFECT) | (FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _51_3120 -> begin
false
end))))
in (let _51_3143 = (match ((c1.FStar_Absyn_Syntax.effect_args, c2.FStar_Absyn_Syntax.effect_args)) with
| ((FStar_Util.Inl (wp1), _51_3127)::_51_3123, (FStar_Util.Inl (wp2), _51_3135)::_51_3131) -> begin
(wp1, wp2)
end
| _51_3140 -> begin
(let _154_1433 = (let _154_1432 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _154_1431 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _154_1432 _154_1431)))
in (FStar_All.failwith _154_1433))
end)
in (match (_51_3143) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(solve_t env (problem_using_guard orig c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ None "result type") wl)
end else begin
(let c2_decl = (FStar_Tc_Env.get_effect_decl env c2.FStar_Absyn_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _51_3145 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _154_1438 = (let _154_1437 = (let _154_1436 = (let _154_1435 = (let _154_1434 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_1434))
in (_154_1435)::[])
in ((FStar_Absyn_Syntax.targ c1.FStar_Absyn_Syntax.result_typ))::_154_1436)
in (c2_decl.FStar_Absyn_Syntax.trivial, _154_1437))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1438 (Some (FStar_Absyn_Syntax.ktype)) r)))
end else begin
(let wp2_imp_wp1 = (let _154_1448 = (let _154_1447 = (let _154_1446 = (let _154_1445 = (let _154_1444 = (let _154_1440 = (let _154_1439 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.imp_lid _154_1439))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_1440))
in (let _154_1443 = (let _154_1442 = (let _154_1441 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _154_1441))
in (_154_1442)::[])
in (_154_1444)::_154_1443))
in ((FStar_Absyn_Syntax.targ wpc2))::_154_1445)
in ((FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ))::_154_1446)
in (c2_decl.FStar_Absyn_Syntax.wp_binop, _154_1447))
in (FStar_Absyn_Syntax.mk_Typ_app _154_1448 None r))
in (FStar_Absyn_Syntax.mk_Typ_app (c2_decl.FStar_Absyn_Syntax.wp_as_type, ((FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ))::((FStar_Absyn_Syntax.targ wp2_imp_wp1))::[]) (Some (FStar_Absyn_Syntax.ktype)) r))
end
in (let base_prob = (let _154_1450 = (sub_prob c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _154_1449 -> TProb (_154_1449)) _154_1450))
in (let wl = (let _154_1454 = (let _154_1453 = (let _154_1452 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _154_1452 g))
in (FStar_All.pipe_left (fun _154_1451 -> Some (_154_1451)) _154_1453))
in (solve_prob orig _154_1454 [] wl))
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
and solve_e : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (match ((compress_prob wl (EProb (problem)))) with
| EProb (p) -> begin
(solve_e' env p wl)
end
| _51_3157 -> begin
(FStar_All.failwith "Impossible")
end))
and solve_e' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (let problem = (let _51_3161 = problem
in {lhs = _51_3161.lhs; relation = EQ; rhs = _51_3161.rhs; element = _51_3161.element; logical_guard = _51_3161.logical_guard; scope = _51_3161.scope; reason = _51_3161.reason; loc = _51_3161.loc; rank = _51_3161.rank})
in (let e1 = problem.lhs
in (let e2 = problem.rhs
in (let orig = EProb (problem)
in (let sub_prob = (fun lhs rhs reason -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (let _51_3173 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1464 = (prob_to_string env orig)
in (FStar_Util.print1 "Attempting:\n%s\n" _154_1464))
end else begin
()
end
in (let flex_rigid = (fun _51_3180 e2 -> (match (_51_3180) with
| (e1, u1, t1, args1) -> begin
(let maybe_vars1 = (pat_vars env [] args1)
in (let sub_problems = (fun xs args2 -> (let _51_3207 = (let _154_1480 = (FStar_All.pipe_right args2 (FStar_List.map (fun _51_34 -> (match (_51_34) with
| (FStar_Util.Inl (t), imp) -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind t)
in (let _51_3194 = (new_tvar t.FStar_Absyn_Syntax.pos xs kk)
in (match (_51_3194) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args1) (Some (kk)) t.FStar_Absyn_Syntax.pos)
in (let _154_1476 = (let _154_1475 = (sub_prob gi_pi t "type index")
in (FStar_All.pipe_left (fun _154_1474 -> TProb (_154_1474)) _154_1475))
in ((FStar_Util.Inl (gi_xi), imp), _154_1476)))
end)))
end
| (FStar_Util.Inr (v), imp) -> begin
(let tt = (FStar_Tc_Recheck.recompute_typ v)
in (let _51_3203 = (new_evar v.FStar_Absyn_Syntax.pos xs tt)
in (match (_51_3203) with
| (gi_xi, gi) -> begin
(let gi_pi = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args1) (Some (tt)) v.FStar_Absyn_Syntax.pos)
in (let _154_1479 = (let _154_1478 = (sub_prob gi_pi v "expression index")
in (FStar_All.pipe_left (fun _154_1477 -> EProb (_154_1477)) _154_1478))
in ((FStar_Util.Inr (gi_xi), imp), _154_1479)))
end)))
end))))
in (FStar_All.pipe_right _154_1480 FStar_List.unzip))
in (match (_51_3207) with
| (gi_xi, gi_pi) -> begin
(let formula = (let _154_1482 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) gi_pi)
in (FStar_Absyn_Util.mk_conj_l _154_1482))
in (gi_xi, gi_pi, formula))
end)))
in (let project_e = (fun head2 args2 -> (let giveup = (fun reason -> (let _154_1489 = (FStar_Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _154_1489 orig)))
in (match ((let _154_1490 = (FStar_Absyn_Util.compress_exp head2)
in _154_1490.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(let _51_3224 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_51_3224) with
| (all_xs, tres) -> begin
if ((FStar_List.length all_xs) <> (FStar_List.length args1)) then begin
(let _154_1493 = (let _154_1492 = (FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _154_1491 = (FStar_Absyn_Print.args_to_string args2)
in (FStar_Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _154_1492 _154_1491)))
in (giveup _154_1493))
end else begin
(let rec aux = (fun xs args -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(FStar_All.failwith "impossible")
end
| ((FStar_Util.Inl (_51_3241), _51_3244)::xs, (FStar_Util.Inl (_51_3249), _51_3252)::args) -> begin
(aux xs args)
end
| ((FStar_Util.Inr (xi), _51_3260)::xs, (FStar_Util.Inr (arg), _51_3267)::args) -> begin
(match ((let _154_1498 = (FStar_Absyn_Util.compress_exp arg)
in _154_1498.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (z) -> begin
if (FStar_Absyn_Util.bvar_eq y z) then begin
(let _51_3276 = (sub_problems all_xs args2)
in (match (_51_3276) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let _154_1502 = (let _154_1501 = (let _154_1500 = (let _154_1499 = (FStar_Absyn_Util.bvar_to_exp xi)
in (_154_1499, gi_xi))
in (FStar_Absyn_Syntax.mk_Exp_app' _154_1500 None e1.FStar_Absyn_Syntax.pos))
in (all_xs, _154_1501))
in (FStar_Absyn_Syntax.mk_Exp_abs _154_1502 None e1.FStar_Absyn_Syntax.pos))
in (let _51_3278 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1506 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _154_1505 = (FStar_Absyn_Print.exp_to_string sol)
in (let _154_1504 = (let _154_1503 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _154_1503 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Projected: %s -> %s\nSubprobs=\n%s\n" _154_1506 _154_1505 _154_1504))))
end else begin
()
end
in (let _154_1508 = (let _154_1507 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _154_1507))
in (solve env _154_1508))))
end))
end else begin
(aux xs args)
end
end
| _51_3281 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _154_1511 = (let _154_1510 = (FStar_Absyn_Print.binder_to_string x)
in (let _154_1509 = (FStar_Absyn_Print.arg_to_string arg)
in (FStar_Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _154_1510 _154_1509)))
in (giveup _154_1511))
end))
in (aux (FStar_List.rev all_xs) (FStar_List.rev args1)))
end
end))
end
| _51_3290 -> begin
(giveup "rigid head term is not a variable")
end)))
in (let imitate_or_project_e = (fun _51_3292 -> (match (()) with
| () -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end else begin
(let _51_3293 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1515 = (FStar_Absyn_Print.exp_to_string e1)
in (let _154_1514 = (FStar_Absyn_Print.exp_to_string e2)
in (FStar_Util.print2 "Imitating expressions: %s =?= %s\n" _154_1515 _154_1514)))
end else begin
()
end
in (let _51_3297 = (FStar_Absyn_Util.head_and_args_e e2)
in (match (_51_3297) with
| (head2, args2) -> begin
(let fvhead = (FStar_Absyn_Util.freevars_exp head2)
in (let _51_3302 = (occurs_check_e env (u1, t1) head2)
in (match (_51_3302) with
| (occurs_ok, _51_3301) -> begin
if ((FStar_Absyn_Util.fvs_included fvhead FStar_Absyn_Syntax.no_fvs) && occurs_ok) then begin
(let _51_3310 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_51_3310) with
| (xs, tres) -> begin
(let _51_3314 = (sub_problems xs args2)
in (match (_51_3314) with
| (gi_xi, gi_pi, f) -> begin
(let sol = (let body = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _51_3318 -> begin
(let _154_1517 = (let _154_1516 = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (xs, _154_1516))
in (FStar_Absyn_Syntax.mk_Exp_abs _154_1517 None e1.FStar_Absyn_Syntax.pos))
end))
in (let _51_3320 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1521 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _154_1520 = (FStar_Absyn_Print.exp_to_string sol)
in (let _154_1519 = (let _154_1518 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _154_1518 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _154_1521 _154_1520 _154_1519))))
end else begin
()
end
in (let _154_1523 = (let _154_1522 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _154_1522))
in (solve env _154_1523))))
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
in (let _51_3332 = (occurs_check_e env (u1, t1) e2)
in (match (_51_3332) with
| (occurs_ok, _51_3331) -> begin
if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && occurs_ok) then begin
(let sol = (FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.FStar_Absyn_Syntax.pos)
in (let _154_1524 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _154_1524)))
end else begin
(imitate_or_project_e ())
end
end))))
end)))))
end))
in (let flex_flex = (fun _51_3339 _51_3344 -> (match ((_51_3339, _51_3344)) with
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
in (let _51_3365 = (let _154_1529 = (FStar_Tc_Env.get_range env)
in (new_evar _154_1529 zs tt))
in (match (_51_3365) with
| (u, _51_3364) -> begin
(let sub1 = (match (xs) with
| [] -> begin
u
end
| _51_3368 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.FStar_Absyn_Syntax.pos)
end)
in (let sub2 = (match (ys) with
| [] -> begin
u
end
| _51_3372 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.FStar_Absyn_Syntax.pos)
end)
in (let _154_1530 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _154_1530))))
end))))
end
end)))
end))
in (let smt_fallback = (fun e1 e2 -> if wl.smt_ok then begin
(let _51_3377 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1535 = (prob_to_string env orig)
in (FStar_Util.print1 "Using SMT to solve:\n%s\n" _154_1535))
end else begin
()
end
in (let _51_3382 = (let _154_1537 = (FStar_Tc_Env.get_range env)
in (let _154_1536 = (FStar_Tc_Env.binders env)
in (new_tvar _154_1537 _154_1536 FStar_Absyn_Syntax.ktype)))
in (match (_51_3382) with
| (t, _51_3381) -> begin
(let _154_1541 = (let _154_1540 = (let _154_1539 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _154_1538 -> Some (_154_1538)) _154_1539))
in (solve_prob orig _154_1540 [] wl))
in (solve env _154_1541))
end)))
end else begin
(giveup env "no SMT solution permitted" orig)
end)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_ascribed (e1, _51_3385, _51_3387), _51_3391) -> begin
(solve_e env (let _51_3393 = problem
in {lhs = e1; relation = _51_3393.relation; rhs = _51_3393.rhs; element = _51_3393.element; logical_guard = _51_3393.logical_guard; scope = _51_3393.scope; reason = _51_3393.reason; loc = _51_3393.loc; rank = _51_3393.rank}) wl)
end
| (_51_3396, FStar_Absyn_Syntax.Exp_ascribed (e2, _51_3399, _51_3401)) -> begin
(solve_e env (let _51_3405 = problem
in {lhs = _51_3405.lhs; relation = _51_3405.relation; rhs = e2; element = _51_3405.element; logical_guard = _51_3405.logical_guard; scope = _51_3405.scope; reason = _51_3405.reason; loc = _51_3405.loc; rank = _51_3405.rank}) wl)
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _154_1543 = (destruct_flex_e e1)
in (let _154_1542 = (destruct_flex_e e2)
in (flex_flex _154_1543 _154_1542)))
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(let _154_1544 = (destruct_flex_e e1)
in (flex_rigid _154_1544 e2))
end
| ((_, FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _154_1545 = (destruct_flex_e e2)
in (flex_rigid _154_1545 e1))
end
| (FStar_Absyn_Syntax.Exp_bvar (x1), FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
if (FStar_Absyn_Util.bvd_eq x1.FStar_Absyn_Syntax.v x1'.FStar_Absyn_Syntax.v) then begin
(let _154_1546 = (solve_prob orig None [] wl)
in (solve env _154_1546))
end else begin
(let _154_1552 = (let _154_1551 = (let _154_1550 = (let _154_1549 = (FStar_Tc_Recheck.recompute_typ e1)
in (let _154_1548 = (FStar_Tc_Recheck.recompute_typ e2)
in (FStar_Absyn_Util.mk_eq _154_1549 _154_1548 e1 e2)))
in (FStar_All.pipe_left (fun _154_1547 -> Some (_154_1547)) _154_1550))
in (solve_prob orig _154_1551 [] wl))
in (solve env _154_1552))
end
end
| (FStar_Absyn_Syntax.Exp_fvar (fv1, _51_3544), FStar_Absyn_Syntax.Exp_fvar (fv1', _51_3549)) -> begin
if (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv1'.FStar_Absyn_Syntax.v) then begin
(let _154_1553 = (solve_prob orig None [] wl)
in (solve env _154_1553))
end else begin
(giveup env "free-variables unequal" orig)
end
end
| (FStar_Absyn_Syntax.Exp_constant (s1), FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(let const_eq = (fun s1 s2 -> (match ((s1, s2)) with
| (FStar_Const.Const_bytearray (b1, _51_3563), FStar_Const.Const_bytearray (b2, _51_3568)) -> begin
(b1 = b2)
end
| (FStar_Const.Const_string (b1, _51_3574), FStar_Const.Const_string (b2, _51_3579)) -> begin
(b1 = b2)
end
| _51_3584 -> begin
(s1 = s2)
end))
in if (const_eq s1 s1') then begin
(let _154_1558 = (solve_prob orig None [] wl)
in (solve env _154_1558))
end else begin
(giveup env "constants unequal" orig)
end)
end
| (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_51_3594); FStar_Absyn_Syntax.tk = _51_3592; FStar_Absyn_Syntax.pos = _51_3590; FStar_Absyn_Syntax.fvs = _51_3588; FStar_Absyn_Syntax.uvs = _51_3586}, _51_3598), _51_3602) -> begin
(let _154_1560 = (let _51_3604 = problem
in (let _154_1559 = (whnf_e env e1)
in {lhs = _154_1559; relation = _51_3604.relation; rhs = _51_3604.rhs; element = _51_3604.element; logical_guard = _51_3604.logical_guard; scope = _51_3604.scope; reason = _51_3604.reason; loc = _51_3604.loc; rank = _51_3604.rank}))
in (solve_e env _154_1560 wl))
end
| (_51_3607, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_51_3617); FStar_Absyn_Syntax.tk = _51_3615; FStar_Absyn_Syntax.pos = _51_3613; FStar_Absyn_Syntax.fvs = _51_3611; FStar_Absyn_Syntax.uvs = _51_3609}, _51_3621)) -> begin
(let _154_1562 = (let _51_3625 = problem
in (let _154_1561 = (whnf_e env e2)
in {lhs = _51_3625.lhs; relation = _51_3625.relation; rhs = _154_1561; element = _51_3625.element; logical_guard = _51_3625.logical_guard; scope = _51_3625.scope; reason = _51_3625.reason; loc = _51_3625.loc; rank = _51_3625.rank}))
in (solve_e env _154_1562 wl))
end
| (FStar_Absyn_Syntax.Exp_app (head1, args1), FStar_Absyn_Syntax.Exp_app (head2, args2)) -> begin
(let orig_wl = wl
in (let rec solve_args = (fun sub_probs wl args1 args2 -> (match ((args1, args2)) with
| ([], []) -> begin
(let guard = (let _154_1572 = (let _154_1571 = (FStar_List.map p_guard sub_probs)
in (FStar_All.pipe_right _154_1571 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Util.mk_conj_l _154_1572))
in (let g = (simplify_formula env guard)
in (let g = (FStar_Absyn_Util.compress_typ g)
in (match (g.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
(let _154_1573 = (solve_prob orig None wl.subst (let _51_3650 = orig_wl
in {attempting = _51_3650.attempting; wl_deferred = _51_3650.wl_deferred; subst = []; ctr = _51_3650.ctr; slack_vars = _51_3650.slack_vars; defer_ok = _51_3650.defer_ok; smt_ok = _51_3650.smt_ok; tcenv = _51_3650.tcenv}))
in (solve env _154_1573))
end
| _51_3653 -> begin
(let _51_3657 = (let _154_1575 = (FStar_Tc_Env.get_range env)
in (let _154_1574 = (FStar_Tc_Env.binders env)
in (new_tvar _154_1575 _154_1574 FStar_Absyn_Syntax.ktype)))
in (match (_51_3657) with
| (t, _51_3656) -> begin
(let guard = (let _154_1576 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_Absyn_Util.mk_disj g _154_1576))
in (let _154_1577 = (solve_prob orig (Some (guard)) wl.subst (let _51_3659 = orig_wl
in {attempting = _51_3659.attempting; wl_deferred = _51_3659.wl_deferred; subst = []; ctr = _51_3659.ctr; slack_vars = _51_3659.slack_vars; defer_ok = _51_3659.defer_ok; smt_ok = _51_3659.smt_ok; tcenv = _51_3659.tcenv}))
in (solve env _154_1577)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(let prob = (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _154_1579 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (FStar_All.pipe_left (fun _154_1578 -> TProb (_154_1578)) _154_1579))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _154_1581 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (FStar_All.pipe_left (fun _154_1580 -> EProb (_154_1580)) _154_1581))
end
| _51_3679 -> begin
(FStar_All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (let _51_3681 = wl
in {attempting = (prob)::[]; wl_deferred = []; subst = _51_3681.subst; ctr = _51_3681.ctr; slack_vars = _51_3681.slack_vars; defer_ok = false; smt_ok = false; tcenv = _51_3681.tcenv}))) with
| Failed (_51_3684) -> begin
(smt_fallback e1 e2)
end
| Success (subst, _51_3688) -> begin
(solve_args ((prob)::sub_probs) (let _51_3691 = wl
in {attempting = _51_3691.attempting; wl_deferred = _51_3691.wl_deferred; subst = subst; ctr = _51_3691.ctr; slack_vars = _51_3691.slack_vars; defer_ok = _51_3691.defer_ok; smt_ok = _51_3691.smt_ok; tcenv = _51_3691.tcenv}) rest1 rest2)
end))
end
| _51_3694 -> begin
(FStar_All.failwith "Impossible: lengths defer")
end))
in (let rec match_head_and_args = (fun head1 head2 -> (match ((let _154_1589 = (let _154_1586 = (FStar_Absyn_Util.compress_exp head1)
in _154_1586.FStar_Absyn_Syntax.n)
in (let _154_1588 = (let _154_1587 = (FStar_Absyn_Util.compress_exp head2)
in _154_1587.FStar_Absyn_Syntax.n)
in (_154_1589, _154_1588)))) with
| (FStar_Absyn_Syntax.Exp_bvar (x), FStar_Absyn_Syntax.Exp_bvar (y)) when ((FStar_Absyn_Util.bvar_eq x y) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _51_3705), FStar_Absyn_Syntax.Exp_fvar (g, _51_3710)) when (((FStar_Absyn_Util.fvar_eq f g) && (not ((FStar_Absyn_Util.is_interpreted f.FStar_Absyn_Syntax.v)))) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_ascribed (e, _51_3716, _51_3718), _51_3722) -> begin
(match_head_and_args e head2)
end
| (_51_3725, FStar_Absyn_Syntax.Exp_ascribed (e, _51_3728, _51_3730)) -> begin
(match_head_and_args head1 e)
end
| (FStar_Absyn_Syntax.Exp_abs (_51_3735), _51_3738) -> begin
(let _154_1591 = (let _51_3740 = problem
in (let _154_1590 = (whnf_e env e1)
in {lhs = _154_1590; relation = _51_3740.relation; rhs = _51_3740.rhs; element = _51_3740.element; logical_guard = _51_3740.logical_guard; scope = _51_3740.scope; reason = _51_3740.reason; loc = _51_3740.loc; rank = _51_3740.rank}))
in (solve_e env _154_1591 wl))
end
| (_51_3743, FStar_Absyn_Syntax.Exp_abs (_51_3745)) -> begin
(let _154_1593 = (let _51_3748 = problem
in (let _154_1592 = (whnf_e env e2)
in {lhs = _51_3748.lhs; relation = _51_3748.relation; rhs = _154_1592; element = _51_3748.element; logical_guard = _51_3748.logical_guard; scope = _51_3748.scope; reason = _51_3748.reason; loc = _51_3748.loc; rank = _51_3748.rank}))
in (solve_e env _154_1593 wl))
end
| _51_3751 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _51_3753 -> begin
(let _51_3757 = (let _154_1595 = (FStar_Tc_Env.get_range env)
in (let _154_1594 = (FStar_Tc_Env.binders env)
in (new_tvar _154_1595 _154_1594 FStar_Absyn_Syntax.ktype)))
in (match (_51_3757) with
| (t, _51_3756) -> begin
(let guard = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (let _51_3759 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1596 = (FStar_Absyn_Print.typ_to_string guard)
in (FStar_Util.print1 "Emitting guard %s\n" _154_1596))
end else begin
()
end
in (let _154_1600 = (let _154_1599 = (let _154_1598 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _154_1597 -> Some (_154_1597)) _154_1598))
in (solve_prob orig _154_1599 [] wl))
in (solve env _154_1600))))
end))
end)))))))))))

type guard_formula =
| Trivial
| NonTrivial of FStar_Absyn_Syntax.formula

let is_Trivial : guard_formula  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Trivial -> begin
true
end
| _ -> begin
false
end))

let is_NonTrivial : guard_formula  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

let ___NonTrivial____0 : guard_formula  ->  FStar_Absyn_Syntax.formula = (fun projectee -> (match (projectee) with
| NonTrivial (_51_3763) -> begin
_51_3763
end))

type implicits =
((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list

type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

let guard_to_string : FStar_Tc_Env.env  ->  guard_t  ->  Prims.string = (fun env g -> (let form = (match (g.guard_f) with
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
in (let carry = (let _154_1631 = (FStar_List.map (fun _51_3777 -> (match (_51_3777) with
| (_51_3775, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (FStar_All.pipe_right _154_1631 (FStar_String.concat ",\n")))
in (FStar_Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

let guard_of_guard_formula : guard_formula  ->  guard_t = (fun g -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

let guard_form : guard_t  ->  guard_formula = (fun g -> g.guard_f)

let is_trivial : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _51_3783} -> begin
true
end
| _51_3790 -> begin
false
end))

let trivial_guard : guard_t = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}

let abstract_guard : FStar_Absyn_Syntax.bvvar  ->  guard_t Prims.option  ->  guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _51_3806 -> begin
(FStar_All.failwith "impossible")
end)
in (let _154_1645 = (let _51_3808 = g
in (let _154_1644 = (let _154_1643 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder x))::[], f) None f.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left (fun _154_1642 -> NonTrivial (_154_1642)) _154_1643))
in {guard_f = _154_1644; deferred = _51_3808.deferred; implicits = _51_3808.implicits}))
in Some (_154_1645)))
end))

let apply_guard : guard_t  ->  FStar_Absyn_Syntax.exp  ->  guard_t = (fun g e -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _51_3815 = g
in (let _154_1653 = (let _154_1652 = (FStar_All.pipe_left (FStar_Absyn_Syntax.syn f.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) (FStar_Absyn_Syntax.mk_Typ_app (f, ((FStar_Absyn_Syntax.varg e))::[])))
in NonTrivial (_154_1652))
in {guard_f = _154_1653; deferred = _51_3815.deferred; implicits = _51_3815.implicits}))
end))

let trivial : guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_51_3820) -> begin
(FStar_All.failwith "impossible")
end))

let conj_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _154_1660 = (FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_154_1660))
end))

let check_trivial : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  guard_formula = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _51_3838 -> begin
NonTrivial (t)
end))

let imp_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
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

let binop_guard : (guard_formula  ->  guard_formula  ->  guard_formula)  ->  guard_t  ->  guard_t  ->  guard_t = (fun f g1 g2 -> (let _154_1683 = (f g1.guard_f g2.guard_f)
in {guard_f = _154_1683; deferred = {carry = (FStar_List.append g1.deferred.carry g2.deferred.carry); slack = (FStar_List.append g1.deferred.slack g2.deferred.slack)}; implicits = (FStar_List.append g1.implicits g2.implicits)}))

let conj_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

let imp_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

let close_guard : FStar_Absyn_Syntax.binders  ->  guard_t  ->  guard_t = (fun binders g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _51_3865 = g
in (let _154_1698 = (let _154_1697 = (FStar_Absyn_Util.close_forall binders f)
in (FStar_All.pipe_right _154_1697 (fun _154_1696 -> NonTrivial (_154_1696))))
in {guard_f = _154_1698; deferred = _51_3865.deferred; implicits = _51_3865.implicits}))
end))

let mk_guard = (fun g ps slack locs -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _154_1710 = (FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _154_1709 = (FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _154_1710 (rel_to_string rel) _154_1709)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  rel  ->  FStar_Absyn_Syntax.typ  ->  (prob * ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) = (fun env t1 rel t2 -> (let x = (let _154_1719 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.gen_bvar_p _154_1719 t1))
in (let env = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (let p = (let _154_1723 = (let _154_1721 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left (fun _154_1720 -> Some (_154_1720)) _154_1721))
in (let _154_1722 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _154_1723 _154_1722)))
in (TProb (p), x)))))

let new_k_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _154_1731 = (FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _154_1730 = (FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _154_1731 (rel_to_string rel) _154_1730)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let simplify_guard : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(let _51_3899 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _154_1736 = (FStar_Absyn_Print.typ_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _154_1736))
end else begin
()
end
in (let f = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f)
in (let f = (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _51_3905 -> begin
NonTrivial (f)
end)
in (let _51_3907 = g
in {guard_f = f; deferred = _51_3907.deferred; implicits = _51_3907.implicits}))))
end))

let solve_and_commit : FStar_Tc_Env.env  ->  worklist  ->  ((prob * Prims.string)  ->  deferred Prims.option)  ->  deferred Prims.option = (fun env probs err -> (let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(let _51_3912 = probs
in {attempting = _51_3912.attempting; wl_deferred = _51_3912.wl_deferred; subst = _51_3912.subst; ctr = _51_3912.ctr; slack_vars = _51_3912.slack_vars; defer_ok = false; smt_ok = _51_3912.smt_ok; tcenv = _51_3912.tcenv})
end else begin
probs
end
in (let sol = (solve env probs)
in (match (sol) with
| Success (s, deferred) -> begin
(let _51_3920 = (commit env s)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _51_3926 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _154_1748 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _154_1748))
end else begin
()
end
in (err (d, s)))
end))))

let with_guard : FStar_Tc_Env.env  ->  prob  ->  deferred Prims.option  ->  guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _154_1760 = (let _154_1759 = (let _154_1758 = (let _154_1757 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _154_1757 (fun _154_1756 -> NonTrivial (_154_1756))))
in {guard_f = _154_1758; deferred = d; implicits = []})
in (simplify_guard env _154_1759))
in (FStar_All.pipe_left (fun _154_1755 -> Some (_154_1755)) _154_1760))
end))

let try_keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t Prims.option = (fun env k1 k2 -> (let _51_3937 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1768 = (FStar_Absyn_Print.kind_to_string k1)
in (let _154_1767 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print2 "try_keq of %s and %s\n" _154_1768 _154_1767)))
end else begin
()
end
in (let prob = (let _154_1773 = (let _154_1772 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _154_1771 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _154_1770 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _154_1772 EQ _154_1771 None _154_1770))))
in (FStar_All.pipe_left (fun _154_1769 -> KProb (_154_1769)) _154_1773))
in (let _154_1775 = (solve_and_commit env (singleton env prob) (fun _51_3940 -> None))
in (FStar_All.pipe_left (with_guard env prob) _154_1775)))))

let keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env t k1 k2 -> (match ((try_keq env k1 k2)) with
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
(let _154_1786 = (let _154_1785 = (let _154_1784 = (FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_154_1784, r))
in FStar_Absyn_Syntax.Error (_154_1785))
in (Prims.raise _154_1786))
end
| Some (t) -> begin
(let _154_1789 = (let _154_1788 = (let _154_1787 = (FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_154_1787, r))
in FStar_Absyn_Syntax.Error (_154_1788))
in (Prims.raise _154_1789))
end))
end
| Some (g) -> begin
g
end))

let subkind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env k1 k2 -> (let _51_3959 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1799 = (let _154_1796 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _154_1796))
in (let _154_1798 = (FStar_Absyn_Print.kind_to_string k1)
in (let _154_1797 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print3 "(%s) subkind of %s and %s\n" _154_1799 _154_1798 _154_1797))))
end else begin
()
end
in (let prob = (let _154_1804 = (let _154_1803 = (whnf_k env k1)
in (let _154_1802 = (whnf_k env k2)
in (let _154_1801 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _154_1803 SUB _154_1802 None _154_1801))))
in (FStar_All.pipe_left (fun _154_1800 -> KProb (_154_1800)) _154_1804))
in (let res = (let _154_1811 = (let _154_1810 = (solve_and_commit env (singleton env prob) (fun _51_3962 -> (let _154_1809 = (let _154_1808 = (let _154_1807 = (FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _154_1806 = (FStar_Tc_Env.get_range env)
in (_154_1807, _154_1806)))
in FStar_Absyn_Syntax.Error (_154_1808))
in (Prims.raise _154_1809))))
in (FStar_All.pipe_left (with_guard env prob) _154_1810))
in (FStar_Util.must _154_1811))
in res))))

let try_teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (let _51_3968 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1819 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1818 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _154_1819 _154_1818)))
end else begin
()
end
in (let prob = (let _154_1822 = (let _154_1821 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _154_1821))
in (FStar_All.pipe_left (fun _154_1820 -> TProb (_154_1820)) _154_1822))
in (let g = (let _154_1824 = (solve_and_commit env (singleton env prob) (fun _51_3971 -> None))
in (FStar_All.pipe_left (with_guard env prob) _154_1824))
in g))))

let teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _154_1834 = (let _154_1833 = (let _154_1832 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _154_1831 = (FStar_Tc_Env.get_range env)
in (_154_1832, _154_1831)))
in FStar_Absyn_Syntax.Error (_154_1833))
in (Prims.raise _154_1834))
end
| Some (g) -> begin
(let _51_3980 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1837 = (FStar_Absyn_Print.typ_to_string t1)
in (let _154_1836 = (FStar_Absyn_Print.typ_to_string t2)
in (let _154_1835 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _154_1837 _154_1836 _154_1835))))
end else begin
()
end
in g)
end))

let try_subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (let kopt = (fun _51_35 -> (match (_51_35) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.kind_to_string t)
end))
in (let k = (fun t1 -> (match ((let _154_1848 = (FStar_Absyn_Util.compress_typ t1)
in _154_1848.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (x) -> begin
(let _154_1852 = (let _154_1849 = (FStar_Absyn_Print.kind_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _154_1849 " ... "))
in (let _154_1851 = (let _154_1850 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _154_1850))
in (Prims.strcat _154_1852 _154_1851)))
end
| _51_3995 -> begin
(let _154_1853 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _154_1853))
end))
in (let _51_3996 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1857 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _154_1856 = (k t1)
in (let _154_1855 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _154_1854 = (k t2)
in (FStar_Util.print4 "try_subtype of %s : %s and %s : %s\n" _154_1857 _154_1856 _154_1855 _154_1854)))))
end else begin
()
end
in (let _51_4000 = (new_t_prob env t1 SUB t2)
in (match (_51_4000) with
| (prob, x) -> begin
(let g = (let _154_1859 = (solve_and_commit env (singleton env prob) (fun _51_4001 -> None))
in (FStar_All.pipe_left (with_guard env prob) _154_1859))
in (let _51_4004 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _154_1863 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _154_1862 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _154_1861 = (let _154_1860 = (FStar_Util.must g)
in (guard_to_string env _154_1860))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _154_1863 _154_1862 _154_1861))))
end else begin
()
end
in (abstract_guard x g)))
end))))))

let subtype_fail = (fun env t1 t2 -> (let _154_1870 = (let _154_1869 = (let _154_1868 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _154_1867 = (FStar_Tc_Env.get_range env)
in (_154_1868, _154_1867)))
in FStar_Absyn_Syntax.Error (_154_1869))
in (Prims.raise _154_1870)))

let subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

let sub_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  guard_t Prims.option = (fun env c1 c2 -> (let _51_4018 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1884 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _154_1883 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _154_1884 _154_1883)))
end else begin
()
end
in (let rel = if env.FStar_Tc_Env.use_eq then begin
EQ
end else begin
SUB
end
in (let prob = (let _154_1887 = (let _154_1886 = (FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _154_1886 "sub_comp"))
in (FStar_All.pipe_left (fun _154_1885 -> CProb (_154_1885)) _154_1887))
in (let _154_1889 = (solve_and_commit env (singleton env prob) (fun _51_4022 -> None))
in (FStar_All.pipe_left (with_guard env prob) _154_1889))))))

let solve_deferred_constraints : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (let fail = (fun _51_4029 -> (match (_51_4029) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (let _51_4034 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && ((FStar_List.length g.deferred.carry) <> 0)) then begin
(let _154_1902 = (let _154_1901 = (FStar_All.pipe_right g.deferred.carry (FStar_List.map (fun _51_4033 -> (match (_51_4033) with
| (msg, x) -> begin
(let _154_1900 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc x))
in (let _154_1899 = (prob_to_string env x)
in (let _154_1898 = (let _154_1897 = (FStar_All.pipe_right (p_guard x) Prims.fst)
in (FStar_Tc_Normalize.formula_norm_to_string env _154_1897))
in (FStar_Util.format4 "(At %s) %s\n%s\nguard is %s\n" _154_1900 msg _154_1899 _154_1898))))
end))))
in (FStar_All.pipe_right _154_1901 (FStar_String.concat "\n")))
in (FStar_All.pipe_left (FStar_Util.print1 "Trying to solve carried problems: begin\n%s\nend\n") _154_1902))
end else begin
()
end
in (let gopt = (let _154_1903 = (wl_of_guard env g.deferred)
in (solve_and_commit env _154_1903 fail))
in (match (gopt) with
| Some ({carry = _51_4039; slack = slack}) -> begin
(let _51_4042 = (fix_slack_vars slack)
in (let _51_4044 = g
in {guard_f = _51_4044.guard_f; deferred = no_deferred; implicits = _51_4044.implicits}))
end
| _51_4047 -> begin
(FStar_All.failwith "impossible")
end)))))

let try_discharge_guard : FStar_Tc_Env.env  ->  guard_t  ->  Prims.unit = (fun env g -> (let g = (solve_deferred_constraints env g)
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
(let _51_4058 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _154_1910 = (FStar_Tc_Env.get_range env)
in (let _154_1909 = (let _154_1908 = (FStar_Absyn_Print.formula_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _154_1908))
in (FStar_Tc_Errors.diag _154_1910 _154_1909)))
end else begin
()
end
in (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env vc))
end))
end)
end))





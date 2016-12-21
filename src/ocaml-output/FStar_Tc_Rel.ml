
open Prims

type rel =
| EQ
| SUB
| SUBINV


let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))


let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))


let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
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
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))


let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
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
| KProb (_45_52) -> begin
_45_52
end))


let ___TProb____0 = (fun projectee -> (match (projectee) with
| TProb (_45_55) -> begin
_45_55
end))


let ___EProb____0 = (fun projectee -> (match (projectee) with
| EProb (_45_58) -> begin
_45_58
end))


let ___CProb____0 = (fun projectee -> (match (projectee) with
| CProb (_45_61) -> begin
_45_61
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
| UK (_45_64) -> begin
_45_64
end))


let ___UT____0 = (fun projectee -> (match (projectee) with
| UT (_45_67) -> begin
_45_67
end))


let ___UE____0 = (fun projectee -> (match (projectee) with
| UE (_45_70) -> begin
_45_70
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
| Success (_45_85) -> begin
_45_85
end))


let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_45_88) -> begin
_45_88
end))


type guard_formula =
| Trivial
| NonTrivial of FStar_Absyn_Syntax.formula


let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
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
| NonTrivial (_45_91) -> begin
_45_91
end))


type implicits =
((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list


type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}


let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))


let new_kvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.uvar_k) = (fun r binders -> (

let u = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (let _142_226 = (let _142_225 = (let _142_224 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in ((u), (_142_224)))
in (FStar_Absyn_Syntax.mk_Kind_uvar _142_225 r))
in ((_142_226), (u)))))


let new_tvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun r binders k -> (

let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _142_234 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _142_234 Prims.op_Negation)))))
in (

let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' ((uv), (k)) None r)
in ((uv), (uv)))
end
| _45_109 -> begin
(

let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (

let k' = (FStar_Absyn_Syntax.mk_Kind_arrow ((binders), (k)) r)
in (

let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' ((uv), (k')) None r)
in (let _142_235 = (FStar_Absyn_Syntax.mk_Typ_app ((uv), (args)) None r)
in ((_142_235), (uv))))))
end))))


let new_evar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.exp) = (fun r binders t -> (

let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _142_243 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _142_243 Prims.op_Negation)))))
in (

let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(

let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' ((uv), (t)) None r)
in ((uv), (uv)))
end
| _45_122 -> begin
(

let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (

let t' = (let _142_245 = (let _142_244 = (FStar_Absyn_Syntax.mk_Total t)
in ((binders), (_142_244)))
in (FStar_Absyn_Syntax.mk_Typ_fun _142_245 None r))
in (

let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' ((uv), (t')) None r)
in (match (args) with
| [] -> begin
((uv), (uv))
end
| _45_128 -> begin
(let _142_246 = (FStar_Absyn_Syntax.mk_Exp_app ((uv), (args)) None r)
in ((_142_246), (uv)))
end))))
end))))


let rel_to_string : rel  ->  Prims.string = (fun _45_1 -> (match (_45_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))


let prob_to_string : FStar_Tc_Env.env  ->  prob  ->  Prims.string = (fun env _45_2 -> (match (_45_2) with
| KProb (p) -> begin
(let _142_254 = (FStar_Absyn_Print.kind_to_string p.lhs)
in (let _142_253 = (FStar_Absyn_Print.kind_to_string p.rhs)
in (FStar_Util.format3 "\t%s\n\t\t%s\n\t%s" _142_254 (rel_to_string p.relation) _142_253)))
end
| TProb (p) -> begin
(let _142_267 = (let _142_266 = (FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _142_265 = (let _142_264 = (FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _142_263 = (let _142_262 = (let _142_261 = (FStar_All.pipe_right p.reason FStar_List.hd)
in (let _142_260 = (let _142_259 = (FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _142_258 = (let _142_257 = (FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _142_256 = (let _142_255 = (FStar_Tc_Normalize.formula_norm_to_string env (Prims.fst p.logical_guard))
in (_142_255)::[])
in (_142_257)::_142_256))
in (_142_259)::_142_258))
in (_142_261)::_142_260))
in ((rel_to_string p.relation))::_142_262)
in (_142_264)::_142_263))
in (_142_266)::_142_265))
in (FStar_Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _142_267))
end
| EProb (p) -> begin
(let _142_269 = (FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _142_268 = (FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _142_269 (rel_to_string p.relation) _142_268)))
end
| CProb (p) -> begin
(let _142_271 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _142_270 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _142_271 (rel_to_string p.relation) _142_270)))
end))


let uvi_to_string : FStar_Tc_Env.env  ->  uvi  ->  Prims.string = (fun env uvi -> (

let str = (fun u -> if (FStar_Options.hide_uvar_nums ()) then begin
"?"
end else begin
(let _142_277 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _142_277 FStar_Util.string_of_int))
end)
in (match (uvi) with
| UK (u, _45_150) -> begin
(let _142_278 = (str u)
in (FStar_All.pipe_right _142_278 (FStar_Util.format1 "UK %s")))
end
| UT ((u, _45_155), t) -> begin
(let _142_281 = (str u)
in (FStar_All.pipe_right _142_281 (fun x -> (let _142_280 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "UT %s %s" x _142_280)))))
end
| UE ((u, _45_163), _45_166) -> begin
(let _142_282 = (str u)
in (FStar_All.pipe_right _142_282 (FStar_Util.format1 "UE %s")))
end)))


let invert_rel : rel  ->  rel = (fun _45_3 -> (match (_45_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))


let invert = (fun p -> (

let _45_174 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _45_174.element; logical_guard = _45_174.logical_guard; scope = _45_174.scope; reason = _45_174.reason; loc = _45_174.loc; rank = _45_174.rank}))


let maybe_invert = (fun p -> if (p.relation = SUBINV) then begin
(invert p)
end else begin
p
end)


let maybe_invert_p : prob  ->  prob = (fun _45_4 -> (match (_45_4) with
| KProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _142_289 -> KProb (_142_289)))
end
| TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _142_290 -> TProb (_142_290)))
end
| EProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _142_291 -> EProb (_142_291)))
end
| CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _142_292 -> CProb (_142_292)))
end))


let vary_rel : rel  ->  variance  ->  rel = (fun rel _45_5 -> (match (_45_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))


let p_rel : prob  ->  rel = (fun _45_6 -> (match (_45_6) with
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


let p_reason : prob  ->  Prims.string Prims.list = (fun _45_7 -> (match (_45_7) with
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


let p_loc : prob  ->  FStar_Range.range = (fun _45_8 -> (match (_45_8) with
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


let p_context : prob  ->  FStar_Absyn_Syntax.binders = (fun _45_9 -> (match (_45_9) with
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


let p_guard : prob  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun _45_10 -> (match (_45_10) with
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


let p_scope : prob  ->  FStar_Absyn_Syntax.binders = (fun _45_11 -> (match (_45_11) with
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


let p_invert : prob  ->  prob = (fun _45_12 -> (match (_45_12) with
| KProb (p) -> begin
(FStar_All.pipe_left (fun _142_311 -> KProb (_142_311)) (invert p))
end
| TProb (p) -> begin
(FStar_All.pipe_left (fun _142_312 -> TProb (_142_312)) (invert p))
end
| EProb (p) -> begin
(FStar_All.pipe_left (fun _142_313 -> EProb (_142_313)) (invert p))
end
| CProb (p) -> begin
(FStar_All.pipe_left (fun _142_314 -> CProb (_142_314)) (invert p))
end))


let is_top_level_prob : prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = (Prims.parse_int "1")))


let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _142_324 = (new_tvar (p_loc orig) scope FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _142_324; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))


let new_problem = (fun env lhs rel rhs elt loc reason -> (let _142_334 = (let _142_333 = (FStar_Tc_Env.get_range env)
in (let _142_332 = (FStar_Tc_Env.binders env)
in (new_tvar _142_333 _142_332 FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _142_334; scope = []; reason = (reason)::[]; loc = loc; rank = None}))


let problem_using_guard = (fun orig lhs rel rhs elt reason -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})


let guard_on_element = (fun problem x phi -> (match (problem.element) with
| None -> begin
(let _142_345 = (let _142_344 = (FStar_Absyn_Syntax.v_binder x)
in (_142_344)::[])
in (FStar_Absyn_Util.close_forall _142_345 phi))
end
| Some (e) -> begin
(FStar_Absyn_Util.subst_typ ((FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (e))))::[]) phi)
end))


let solve_prob' : Prims.bool  ->  prob  ->  FStar_Absyn_Syntax.typ Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (

let phi = (match (logical_guard) with
| None -> begin
FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (

let _45_293 = (p_guard prob)
in (match (_45_293) with
| (_45_291, uv) -> begin
(

let _45_301 = (match ((let _142_356 = (FStar_Absyn_Util.compress_typ uv)
in _142_356.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uvar, k) -> begin
(

let phi = (FStar_Absyn_Util.close_for_kind phi k)
in (FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _45_300 -> begin
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
| _45_305 -> begin
(

let _45_306 = if (FStar_All.pipe_left (FStar_Tc_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _142_358 = (let _142_357 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _142_357 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Extending solution: %s\n" _142_358))
end else begin
()
end
in (

let _45_308 = wl
in {attempting = _45_308.attempting; wl_deferred = _45_308.wl_deferred; subst = (FStar_List.append uvis wl.subst); ctr = (wl.ctr + (Prims.parse_int "1")); slack_vars = _45_308.slack_vars; defer_ok = _45_308.defer_ok; smt_ok = _45_308.smt_ok; tcenv = _45_308.tcenv}))
end))
end))))


let extend_solution : uvi  ->  worklist  ->  worklist = (fun sol wl -> (

let _45_312 = wl
in {attempting = _45_312.attempting; wl_deferred = _45_312.wl_deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + (Prims.parse_int "1")); slack_vars = _45_312.slack_vars; defer_ok = _45_312.defer_ok; smt_ok = _45_312.smt_ok; tcenv = _45_312.tcenv}))


let solve_prob : prob  ->  FStar_Absyn_Syntax.typ Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (solve_prob' false prob logical_guard uvis wl))


let explain : FStar_Tc_Env.env  ->  prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _142_379 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _142_378 = (prob_to_string env d)
in (let _142_377 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _142_379 _142_378 _142_377 s)))))


let empty_worklist : FStar_Tc_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; subst = []; ctr = (Prims.parse_int "0"); slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})


let singleton : FStar_Tc_Env.env  ->  prob  ->  worklist = (fun env prob -> (

let _45_324 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _45_324.wl_deferred; subst = _45_324.subst; ctr = _45_324.ctr; slack_vars = _45_324.slack_vars; defer_ok = _45_324.defer_ok; smt_ok = _45_324.smt_ok; tcenv = _45_324.tcenv}))


let wl_of_guard : FStar_Tc_Env.env  ->  deferred  ->  worklist = (fun env g -> (

let _45_328 = (empty_worklist env)
in (let _142_390 = (FStar_List.map Prims.snd g.carry)
in {attempting = _142_390; wl_deferred = _45_328.wl_deferred; subst = _45_328.subst; ctr = _45_328.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _45_328.smt_ok; tcenv = _45_328.tcenv})))


let defer : Prims.string  ->  prob  ->  worklist  ->  worklist = (fun reason prob wl -> (

let _45_333 = wl
in {attempting = _45_333.attempting; wl_deferred = (((wl.ctr), (reason), (prob)))::wl.wl_deferred; subst = _45_333.subst; ctr = _45_333.ctr; slack_vars = _45_333.slack_vars; defer_ok = _45_333.defer_ok; smt_ok = _45_333.smt_ok; tcenv = _45_333.tcenv}))


let attempt : prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (

let _45_337 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _45_337.wl_deferred; subst = _45_337.subst; ctr = _45_337.ctr; slack_vars = _45_337.slack_vars; defer_ok = _45_337.defer_ok; smt_ok = _45_337.smt_ok; tcenv = _45_337.tcenv}))


let add_slack_mul : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (

let _45_341 = wl
in {attempting = _45_341.attempting; wl_deferred = _45_341.wl_deferred; subst = _45_341.subst; ctr = _45_341.ctr; slack_vars = (((true), (slack)))::wl.slack_vars; defer_ok = _45_341.defer_ok; smt_ok = _45_341.smt_ok; tcenv = _45_341.tcenv}))


let add_slack_add : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (

let _45_345 = wl
in {attempting = _45_345.attempting; wl_deferred = _45_345.wl_deferred; subst = _45_345.subst; ctr = _45_345.ctr; slack_vars = (((false), (slack)))::wl.slack_vars; defer_ok = _45_345.defer_ok; smt_ok = _45_345.smt_ok; tcenv = _45_345.tcenv}))


let giveup : FStar_Tc_Env.env  ->  Prims.string  ->  prob  ->  solution = (fun env reason prob -> (

let _45_350 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_415 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _142_415))
end else begin
()
end
in Failed (((prob), (reason)))))


let commit = (fun env uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _45_13 -> (match (_45_13) with
| UK (u, k) -> begin
(FStar_Absyn_Util.unchecked_unify u k)
end
| UT ((u, k), t) -> begin
(FStar_Absyn_Util.unchecked_unify u t)
end
| UE ((u, _45_367), e) -> begin
(FStar_Absyn_Util.unchecked_unify u e)
end)))))


let find_uvar_k : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.knd Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _45_14 -> (match (_45_14) with
| UK (u, t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _45_380 -> begin
None
end))))


let find_uvar_t : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.typ Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _45_15 -> (match (_45_15) with
| UT ((u, _45_386), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _45_392 -> begin
None
end))))


let find_uvar_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.exp Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _45_16 -> (match (_45_16) with
| UE ((u, _45_398), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _45_404 -> begin
None
end))))


let simplify_formula : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env f -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f))


let norm_targ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t))


let norm_arg = (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _142_446 = (let _142_445 = (norm_targ env t)
in (FStar_All.pipe_left (fun _142_444 -> FStar_Util.Inl (_142_444)) _142_445))
in ((_142_446), ((Prims.snd a))))
end
| FStar_Util.Inr (v) -> begin
(let _142_449 = (let _142_448 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env v)
in (FStar_All.pipe_left (fun _142_447 -> FStar_Util.Inr (_142_447)) _142_448))
in ((_142_449), ((Prims.snd a))))
end))


let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _142_454 = (FStar_Tc_Normalize.whnf env t)
in (FStar_All.pipe_right _142_454 FStar_Absyn_Util.compress_typ)))


let sn : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _142_459 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env t)
in (FStar_All.pipe_right _142_459 FStar_Absyn_Util.compress_typ)))


let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _45_17 -> (match (_45_17) with
| (FStar_Util.Inl (a), imp) -> begin
(let _142_465 = (let _142_464 = (

let _45_426 = a
in (let _142_463 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _45_426.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _142_463; FStar_Absyn_Syntax.p = _45_426.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_142_464))
in ((_142_465), (imp)))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _142_468 = (let _142_467 = (

let _45_432 = x
in (let _142_466 = (norm_targ env x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _45_432.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _142_466; FStar_Absyn_Syntax.p = _45_432.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_142_467))
in ((_142_468), (imp)))
end)))))


let whnf_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env k -> (let _142_473 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env k)
in (FStar_All.pipe_right _142_473 FStar_Absyn_Util.compress_kind)))


let whnf_e : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env e -> (let _142_478 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env e)
in (FStar_All.pipe_right _142_478 FStar_Absyn_Util.compress_exp)))


let rec compress_k : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env wl k -> (

let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((find_uvar_k uv wl.subst)) with
| None -> begin
k
end
| Some (k') -> begin
(match (k'.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, body) -> begin
(

let k = (let _142_485 = (FStar_Absyn_Util.subst_of_list formals actuals)
in (FStar_Absyn_Util.subst_kind _142_485 body))
in (compress_k env wl k))
end
| _45_455 -> begin
if ((FStar_List.length actuals) = (Prims.parse_int "0")) then begin
(compress_k env wl k')
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end)
end
| _45_457 -> begin
k
end)))


let rec compress : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl t -> (

let t = (let _142_492 = (FStar_Absyn_Util.unmeta_typ t)
in (whnf env _142_492))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _45_464) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _45_480); FStar_Absyn_Syntax.tk = _45_477; FStar_Absyn_Syntax.pos = _45_475; FStar_Absyn_Syntax.fvs = _45_473; FStar_Absyn_Syntax.uvs = _45_471}, args) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(

let t = (FStar_Absyn_Syntax.mk_Typ_app ((t'), (args)) None t.FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _45_491 -> begin
t
end)
end
| _45_493 -> begin
t
end)))


let rec compress_e : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl e -> (

let e = (FStar_Absyn_Util.unmeta_exp e)
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
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _45_515); FStar_Absyn_Syntax.tk = _45_512; FStar_Absyn_Syntax.pos = _45_510; FStar_Absyn_Syntax.fvs = _45_508; FStar_Absyn_Syntax.uvs = _45_506}, args) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(

let e' = (compress_e env wl e')
in (FStar_Absyn_Syntax.mk_Exp_app ((e'), (args)) None e.FStar_Absyn_Syntax.pos))
end)
end
| _45_527 -> begin
e
end)))


let normalize_refinement : FStar_Tc_Normalize.steps  ->  FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun steps env wl t0 -> (let _142_507 = (compress env wl t0)
in (FStar_Tc_Normalize.normalize_refinement steps env _142_507)))


let base_and_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.bvvar * FStar_Absyn_Syntax.typ) Prims.option) = (fun env wl t1 -> (

let rec aux = (fun norm t1 -> (match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
if norm then begin
((x.FStar_Absyn_Syntax.sort), (Some (((x), (phi)))))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, phi); FStar_Absyn_Syntax.tk = _45_549; FStar_Absyn_Syntax.pos = _45_547; FStar_Absyn_Syntax.fvs = _45_545; FStar_Absyn_Syntax.uvs = _45_543} -> begin
((x.FStar_Absyn_Syntax.sort), (Some (((x), (phi)))))
end
| tt -> begin
(let _142_520 = (let _142_519 = (FStar_Absyn_Print.typ_to_string tt)
in (let _142_518 = (FStar_Absyn_Print.tag_of_typ tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _142_519 _142_518)))
in (FStar_All.failwith _142_520))
end)
end
end
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_app (_)) -> begin
if norm then begin
((t1), (None))
end else begin
(

let _45_564 = (let _142_521 = (normalize_refinement [] env wl t1)
in (aux true _142_521))
in (match (_45_564) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
((t1), (None))
end
| _45_567 -> begin
((t2'), (refinement))
end)
end))
end
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
((t1), (None))
end
| (FStar_Absyn_Syntax.Typ_ascribed (_)) | (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_meta (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _142_524 = (let _142_523 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_522 = (FStar_Absyn_Print.tag_of_typ t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _142_523 _142_522)))
in (FStar_All.failwith _142_524))
end))
in (let _142_525 = (compress env wl t1)
in (aux false _142_525))))


let unrefine : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _142_530 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _142_530 Prims.fst)))


let trivial_refinement = (fun t -> (let _142_532 = (FStar_Absyn_Util.gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in ((_142_532), (FStar_Absyn_Util.t_true))))


let as_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * FStar_Absyn_Syntax.typ) = (fun env wl t -> (

let _45_598 = (base_and_refinement env wl t)
in (match (_45_598) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
((x), (phi))
end)
end)))


let force_refinement : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * FStar_Absyn_Syntax.typ) Prims.option)  ->  FStar_Absyn_Syntax.typ = (fun _45_606 -> (match (_45_606) with
| (t_base, refopt) -> begin
(

let _45_614 = (match (refopt) with
| Some (y, phi) -> begin
((y), (phi))
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_45_614) with
| (y, phi) -> begin
(FStar_Absyn_Syntax.mk_Typ_refine ((y), (phi)) None t_base.FStar_Absyn_Syntax.pos)
end))
end))


let rec occurs = (fun env wl uk t -> (

let uvs = (FStar_Absyn_Util.uvars_in_typ t)
in (let _142_552 = (FStar_All.pipe_right uvs.FStar_Absyn_Syntax.uvars_t FStar_Util.set_elements)
in (FStar_All.pipe_right _142_552 (FStar_Util.for_some (fun _45_625 -> (match (_45_625) with
| (uvt, _45_624) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(FStar_Unionfind.equivalent uvt (Prims.fst uk))
end
| Some (t) -> begin
(

let t = (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_45_638, t); FStar_Absyn_Syntax.tk = _45_636; FStar_Absyn_Syntax.pos = _45_634; FStar_Absyn_Syntax.fvs = _45_632; FStar_Absyn_Syntax.uvs = _45_630} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))


let occurs_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.string Prims.option) = (fun env wl uk t -> (

let occurs_ok = (not ((occurs env wl uk t)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _142_565 = (let _142_564 = (FStar_Absyn_Print.uvar_t_to_string uk)
in (let _142_563 = (FStar_Absyn_Print.typ_to_string t)
in (let _142_562 = (let _142_561 = (FStar_All.pipe_right wl.subst (FStar_List.map (uvi_to_string env)))
in (FStar_All.pipe_right _142_561 (FStar_String.concat ", ")))
in (FStar_Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _142_564 _142_563 _142_562))))
in Some (_142_565))
end
in ((occurs_ok), (msg)))))


let occurs_and_freevars_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.bool * (Prims.string Prims.option * FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.freevars)) = (fun env wl uk fvs t -> (

let fvs_t = (FStar_Absyn_Util.freevars_typ t)
in (

let _45_659 = (occurs_check env wl uk t)
in (match (_45_659) with
| (occurs_ok, msg) -> begin
(let _142_576 = (FStar_Absyn_Util.fvs_included fvs_t fvs)
in ((occurs_ok), (_142_576), (((msg), (fvs), (fvs_t)))))
end))))


let occurs_check_e : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (Prims.bool * Prims.string Prims.option) = (fun env ut e -> (

let uvs = (FStar_Absyn_Util.uvars_in_exp e)
in (

let occurs_ok = (not ((FStar_Util.set_mem ut uvs.FStar_Absyn_Syntax.uvars_e)))
in (

let msg = if occurs_ok then begin
None
end else begin
(let _142_588 = (let _142_587 = (FStar_Absyn_Print.uvar_e_to_string ut)
in (let _142_586 = (let _142_584 = (let _142_583 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _142_583 (FStar_List.map FStar_Absyn_Print.uvar_e_to_string)))
in (FStar_All.pipe_right _142_584 (FStar_String.concat ", ")))
in (let _142_585 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _142_587 _142_586 _142_585))))
in Some (_142_588))
end
in ((occurs_ok), (msg))))))


let intersect_vars : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders = (fun v1 v2 -> (

let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders v1)
in (

let fvs2 = (FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _142_595 = (let _142_594 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _142_593 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _142_594; FStar_Absyn_Syntax.fxvs = _142_593}))
in (FStar_Absyn_Syntax.binders_of_freevars _142_595)))))


let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun ax1 ax2 -> (match ((((Prims.fst ax1)), ((Prims.fst ax2)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Util.bvar_eq x y)
end
| _45_685 -> begin
false
end)) v1 v2)))


let pat_var_opt = (fun env seen arg -> (

let hd = (norm_arg env arg)
in (match ((FStar_All.pipe_left Prims.fst hd)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _45_697; FStar_Absyn_Syntax.pos = _45_695; FStar_Absyn_Syntax.fvs = _45_693; FStar_Absyn_Syntax.uvs = _45_691}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _45_18 -> (match (_45_18) with
| (FStar_Util.Inl (b), _45_706) -> begin
(FStar_Absyn_Syntax.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)
end
| _45_709 -> begin
false
end)))) then begin
None
end else begin
Some (((FStar_Util.Inl (a)), ((Prims.snd hd))))
end
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (x); FStar_Absyn_Syntax.tk = _45_717; FStar_Absyn_Syntax.pos = _45_715; FStar_Absyn_Syntax.fvs = _45_713; FStar_Absyn_Syntax.uvs = _45_711}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _45_19 -> (match (_45_19) with
| (FStar_Util.Inr (y), _45_726) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _45_729 -> begin
false
end)))) then begin
None
end else begin
Some (((FStar_Util.Inr (x)), ((Prims.snd hd))))
end
end
| _45_731 -> begin
None
end)))


let rec pat_vars : FStar_Tc_Env.env  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| (hd)::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(

let _45_740 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_611 = (FStar_Absyn_Print.arg_to_string hd)
in (FStar_Util.print1 "Not a pattern: %s\n" _142_611))
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
((t), (uv), (k), ([]))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, k); FStar_Absyn_Syntax.tk = _45_756; FStar_Absyn_Syntax.pos = _45_754; FStar_Absyn_Syntax.fvs = _45_752; FStar_Absyn_Syntax.uvs = _45_750}, args) -> begin
((t), (uv), (k), (args))
end
| _45_766 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_e = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, k) -> begin
((e), (uv), (k), ([]))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, k); FStar_Absyn_Syntax.tk = _45_779; FStar_Absyn_Syntax.pos = _45_777; FStar_Absyn_Syntax.fvs = _45_775; FStar_Absyn_Syntax.uvs = _45_773}, args) -> begin
((e), (uv), (k), (args))
end
| _45_789 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))


let destruct_flex_pattern = (fun env t -> (

let _45_796 = (destruct_flex_t t)
in (match (_45_796) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((((t), (uv), (k), (args))), (Some (vars)))
end
| _45_800 -> begin
((((t), (uv), (k), (args))), (None))
end)
end)))


type match_result =
| MisMatch
| HeadMatch
| FullMatch


let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))


let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))


let head_match : match_result  ->  match_result = (fun _45_20 -> (match (_45_20) with
| MisMatch -> begin
MisMatch
end
| _45_804 -> begin
HeadMatch
end))


let rec head_matches : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  match_result = (fun t1 t2 -> (match ((let _142_628 = (let _142_625 = (FStar_Absyn_Util.unmeta_typ t1)
in _142_625.FStar_Absyn_Syntax.n)
in (let _142_627 = (let _142_626 = (FStar_Absyn_Util.unmeta_typ t2)
in _142_626.FStar_Absyn_Syntax.n)
in ((_142_628), (_142_627))))) with
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
| (FStar_Absyn_Syntax.Typ_refine (x, _45_833), FStar_Absyn_Syntax.Typ_refine (y, _45_838)) -> begin
(let _142_629 = (head_matches x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _142_629 head_match))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _45_844), _45_848) -> begin
(let _142_630 = (head_matches x.FStar_Absyn_Syntax.sort t2)
in (FStar_All.pipe_right _142_630 head_match))
end
| (_45_851, FStar_Absyn_Syntax.Typ_refine (x, _45_854)) -> begin
(let _142_631 = (head_matches t1 x.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _142_631 head_match))
end
| (FStar_Absyn_Syntax.Typ_fun (_45_859), FStar_Absyn_Syntax.Typ_fun (_45_862)) -> begin
HeadMatch
end
| (FStar_Absyn_Syntax.Typ_app (head, _45_867), FStar_Absyn_Syntax.Typ_app (head', _45_872)) -> begin
(head_matches head head')
end
| (FStar_Absyn_Syntax.Typ_app (head, _45_878), _45_882) -> begin
(head_matches head t2)
end
| (_45_885, FStar_Absyn_Syntax.Typ_app (head, _45_888)) -> begin
(head_matches t1 head)
end
| (FStar_Absyn_Syntax.Typ_uvar (uv, _45_894), FStar_Absyn_Syntax.Typ_uvar (uv', _45_899)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (_45_904, FStar_Absyn_Syntax.Typ_lam (_45_906)) -> begin
HeadMatch
end
| _45_910 -> begin
MisMatch
end))


let head_matches_delta : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (match_result * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option) = (fun env wl t1 t2 -> (

let success = (fun d r t1 t2 -> ((r), (if (d > (Prims.parse_int "0")) then begin
Some (((t1), (t2)))
end else begin
None
end)))
in (

let fail = (fun _45_921 -> (match (()) with
| () -> begin
((MisMatch), (None))
end))
in (

let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = (Prims.parse_int "2")) then begin
(fail ())
end else begin
if (d = (Prims.parse_int "1")) then begin
(

let t1' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t1)
in (

let t2' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t2)
in (aux (Prims.parse_int "2") t1' t2')))
end else begin
(

let t1 = (normalize_refinement [] env wl t1)
in (

let t2 = (normalize_refinement [] env wl t2)
in (aux (d + (Prims.parse_int "1")) t1 t2)))
end
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux (Prims.parse_int "0") t1 t2)))))


let decompose_binder = (fun bs v_ktec rebuild_base -> (

let fail = (fun _45_937 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let rebuild = (fun ktecs -> (

let rec aux = (fun new_bs bs ktecs -> (match (((bs), (ktecs))) with
| ([], (ktec)::[]) -> begin
(rebuild_base (FStar_List.rev new_bs) ktec)
end
| (((FStar_Util.Inl (a), imp))::rest, (FStar_Absyn_Syntax.K (k))::rest') -> begin
(aux ((((FStar_Util.Inl ((

let _45_959 = a
in {FStar_Absyn_Syntax.v = _45_959.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _45_959.FStar_Absyn_Syntax.p}))), (imp)))::new_bs) rest rest')
end
| (((FStar_Util.Inr (x), imp))::rest, (FStar_Absyn_Syntax.T (t, _45_970))::rest') -> begin
(aux ((((FStar_Util.Inr ((

let _45_975 = x
in {FStar_Absyn_Syntax.v = _45_975.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _45_975.FStar_Absyn_Syntax.p}))), (imp)))::new_bs) rest rest')
end
| _45_978 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (

let rec mk_b_ktecs = (fun _45_982 _45_21 -> (match (_45_982) with
| (binders, b_ktecs) -> begin
(match (_45_21) with
| [] -> begin
(FStar_List.rev ((((None), (COVARIANT), (v_ktec)))::b_ktecs))
end
| (hd)::rest -> begin
(

let bopt = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (

let b_ktec = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
((bopt), (CONTRAVARIANT), (FStar_Absyn_Syntax.K (a.FStar_Absyn_Syntax.sort)))
end
| FStar_Util.Inr (x) -> begin
((bopt), (CONTRAVARIANT), (FStar_Absyn_Syntax.T (((x.FStar_Absyn_Syntax.sort), (Some (FStar_Absyn_Syntax.ktype))))))
end)
in (

let binders' = (match (bopt) with
| None -> begin
binders
end
| Some (hd) -> begin
(FStar_List.append binders ((hd)::[]))
end)
in (mk_b_ktecs ((binders'), ((b_ktec)::b_ktecs)) rest))))
end)
end))
in (let _142_685 = (mk_b_ktecs (([]), ([])) bs)
in ((rebuild), (_142_685)))))))


let rec decompose_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list) = (fun env k -> (

let fail = (fun _45_1001 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (

let k0 = k
in (

let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(

let rebuild = (fun _45_22 -> (match (_45_22) with
| [] -> begin
k
end
| _45_1009 -> begin
(fail ())
end))
in ((rebuild), ([])))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(decompose_binder bs (FStar_Absyn_Syntax.K (k)) (fun bs _45_23 -> (match (_45_23) with
| FStar_Absyn_Syntax.K (k) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow ((bs), (k)) k0.FStar_Absyn_Syntax.pos)
end
| _45_1020 -> begin
(fail ())
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_45_1022, k) -> begin
(decompose_kind env k)
end
| _45_1027 -> begin
(FStar_All.failwith "Impossible")
end)))))


let rec decompose_typ = (fun env t -> (

let t = (FStar_Absyn_Util.unmeta_typ t)
in (

let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (hd, args) -> begin
(

let rebuild = (fun args' -> (

let args = (FStar_List.map2 (fun x y -> (match (((x), (y))) with
| ((FStar_Util.Inl (_45_1042), imp), FStar_Absyn_Syntax.T (t, _45_1048)) -> begin
((FStar_Util.Inl (t)), (imp))
end
| ((FStar_Util.Inr (_45_1053), imp), FStar_Absyn_Syntax.E (e)) -> begin
((FStar_Util.Inr (e)), (imp))
end
| _45_1061 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Absyn_Syntax.mk_Typ_app ((hd), (args)) None t.FStar_Absyn_Syntax.pos)))
in (

let b_ktecs = (FStar_All.pipe_right args (FStar_List.map (fun _45_24 -> (match (_45_24) with
| (FStar_Util.Inl (t), _45_1067) -> begin
((None), (INVARIANT), (FStar_Absyn_Syntax.T (((t), (None)))))
end
| (FStar_Util.Inr (e), _45_1072) -> begin
((None), (INVARIANT), (FStar_Absyn_Syntax.E (e)))
end))))
in ((rebuild), (matches), (b_ktecs))))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(

let _45_1087 = (decompose_binder bs (FStar_Absyn_Syntax.C (c)) (fun bs _45_25 -> (match (_45_25) with
| FStar_Absyn_Syntax.C (c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t.FStar_Absyn_Syntax.pos)
end
| _45_1084 -> begin
(FStar_All.failwith "Bad reconstruction")
end)))
in (match (_45_1087) with
| (rebuild, b_ktecs) -> begin
((rebuild), (matches), (b_ktecs))
end))
end
| _45_1089 -> begin
(

let rebuild = (fun _45_26 -> (match (_45_26) with
| [] -> begin
t
end
| _45_1093 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in ((rebuild), ((fun t -> true)), ([])))
end))))


let un_T : FStar_Absyn_Syntax.ktec  ->  FStar_Absyn_Syntax.typ = (fun _45_27 -> (match (_45_27) with
| FStar_Absyn_Syntax.T (x, _45_1099) -> begin
x
end
| _45_1103 -> begin
(FStar_All.failwith "impossible")
end))


let arg_of_ktec : FStar_Absyn_Syntax.ktec  ->  FStar_Absyn_Syntax.arg = (fun _45_28 -> (match (_45_28) with
| FStar_Absyn_Syntax.T (t, _45_1107) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Absyn_Syntax.E (e) -> begin
(FStar_Absyn_Syntax.varg e)
end
| _45_1113 -> begin
(FStar_All.failwith "Impossible")
end))


let imitation_sub_probs = (fun orig env scope ps qs -> (

let r = (p_loc orig)
in (

let rel = (p_rel orig)
in (

let sub_prob = (fun scope args q -> (match (q) with
| (_45_1126, variance, FStar_Absyn_Syntax.K (ki)) -> begin
(

let _45_1133 = (new_kvar r scope)
in (match (_45_1133) with
| (gi_xs, gi) -> begin
(

let gi_ps = (FStar_Absyn_Syntax.mk_Kind_uvar ((gi), (args)) r)
in (let _142_768 = (let _142_767 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (FStar_All.pipe_left (fun _142_766 -> KProb (_142_766)) _142_767))
in ((FStar_Absyn_Syntax.K (gi_xs)), (_142_768))))
end))
end
| (_45_1136, variance, FStar_Absyn_Syntax.T (ti, kopt)) -> begin
(

let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(FStar_Tc_Recheck.recompute_kind ti)
end)
in (

let _45_1149 = (new_tvar r scope k)
in (match (_45_1149) with
| (gi_xs, gi) -> begin
(

let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app' ((gi), (args)) None r)
in (let _142_771 = (let _142_770 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _142_769 -> TProb (_142_769)) _142_770))
in ((FStar_Absyn_Syntax.T (((gi_xs), (Some (k))))), (_142_771))))
end)))
end
| (_45_1152, variance, FStar_Absyn_Syntax.E (ei)) -> begin
(

let t = (FStar_Tc_Recheck.recompute_typ ei)
in (

let _45_1160 = (new_evar r scope t)
in (match (_45_1160) with
| (gi_xs, gi) -> begin
(

let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app' ((gi), (args)) (Some (t)) r)
in (let _142_774 = (let _142_773 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (FStar_All.pipe_left (fun _142_772 -> EProb (_142_772)) _142_773))
in ((FStar_Absyn_Syntax.E (gi_xs)), (_142_774))))
end)))
end
| (_45_1163, _45_1165, FStar_Absyn_Syntax.C (_45_1167)) -> begin
(FStar_All.failwith "impos")
end))
in (

let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
(([]), ([]), (FStar_Absyn_Util.t_true))
end
| (q)::qs -> begin
(

let _45_1243 = (match (q) with
| (bopt, variance, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Total (ti); FStar_Absyn_Syntax.tk = _45_1187; FStar_Absyn_Syntax.pos = _45_1185; FStar_Absyn_Syntax.fvs = _45_1183; FStar_Absyn_Syntax.uvs = _45_1181})) -> begin
(match ((sub_prob scope args ((bopt), (variance), (FStar_Absyn_Syntax.T (((ti), (Some (FStar_Absyn_Syntax.ktype)))))))) with
| (FStar_Absyn_Syntax.T (gi_xs, _45_1195), prob) -> begin
(let _142_783 = (let _142_782 = (FStar_Absyn_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _142_781 -> FStar_Absyn_Syntax.C (_142_781)) _142_782))
in ((_142_783), ((prob)::[])))
end
| _45_1201 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_45_1203, _45_1205, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (c); FStar_Absyn_Syntax.tk = _45_1213; FStar_Absyn_Syntax.pos = _45_1211; FStar_Absyn_Syntax.fvs = _45_1209; FStar_Absyn_Syntax.uvs = _45_1207})) -> begin
(

let components = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map (fun _45_29 -> (match (_45_29) with
| (FStar_Util.Inl (t), _45_1223) -> begin
((None), (INVARIANT), (FStar_Absyn_Syntax.T (((t), (None)))))
end
| (FStar_Util.Inr (e), _45_1228) -> begin
((None), (INVARIANT), (FStar_Absyn_Syntax.E (e)))
end))))
in (

let components = (((None), (COVARIANT), (FStar_Absyn_Syntax.T (((c.FStar_Absyn_Syntax.result_typ), (Some (FStar_Absyn_Syntax.ktype)))))))::components
in (

let _45_1234 = (let _142_785 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _142_785 FStar_List.unzip))
in (match (_45_1234) with
| (ktecs, sub_probs) -> begin
(

let gi_xs = (let _142_790 = (let _142_789 = (let _142_786 = (FStar_List.hd ktecs)
in (FStar_All.pipe_right _142_786 un_T))
in (let _142_788 = (let _142_787 = (FStar_List.tl ktecs)
in (FStar_All.pipe_right _142_787 (FStar_List.map arg_of_ktec)))
in {FStar_Absyn_Syntax.effect_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _142_789; FStar_Absyn_Syntax.effect_args = _142_788; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _142_790))
in ((FStar_Absyn_Syntax.C (gi_xs)), (sub_probs)))
end))))
end
| _45_1237 -> begin
(

let _45_1240 = (sub_prob scope args q)
in (match (_45_1240) with
| (ktec, prob) -> begin
((ktec), ((prob)::[]))
end))
end)
in (match (_45_1243) with
| (ktec, probs) -> begin
(

let _45_1256 = (match (q) with
| (Some (b), _45_1247, _45_1249) -> begin
(let _142_792 = (let _142_791 = (FStar_Absyn_Util.arg_of_non_null_binder b)
in (_142_791)::args)
in ((Some (b)), ((b)::scope), (_142_792)))
end
| _45_1252 -> begin
((None), (scope), (args))
end)
in (match (_45_1256) with
| (bopt, scope, args) -> begin
(

let _45_1260 = (aux scope args qs)
in (match (_45_1260) with
| (sub_probs, ktecs, f) -> begin
(

let f = (match (bopt) with
| None -> begin
(let _142_795 = (let _142_794 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_142_794)
in (FStar_Absyn_Util.mk_conj_l _142_795))
end
| Some (b) -> begin
(let _142_799 = (let _142_798 = (FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _142_797 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_142_798)::_142_797))
in (FStar_Absyn_Util.mk_conj_l _142_799))
end)
in (((FStar_List.append probs sub_probs)), ((ktec)::ktecs), (f)))
end))
end))
end))
end))
in (aux scope ps qs))))))


type slack =
{lower : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); upper : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); flag : Prims.bool FStar_ST.ref}


let is_Mkslack : slack  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkslack"))))


let fix_slack_uv : (FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax)  ->  Prims.bool  ->  Prims.unit = (fun _45_1273 mul -> (match (_45_1273) with
| (uv, k) -> begin
(

let inst = if mul then begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_true k)
end else begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_false k)
end
in (FStar_Absyn_Util.unchecked_unify uv inst))
end))


let fix_slack_vars : (Prims.bool * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.list  ->  Prims.unit = (fun slack -> (FStar_All.pipe_right slack (FStar_List.iter (fun _45_1279 -> (match (_45_1279) with
| (mul, s) -> begin
(match ((let _142_817 = (FStar_Absyn_Util.compress_typ s)
in _142_817.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(fix_slack_uv ((uv), (k)) mul)
end
| _45_1285 -> begin
()
end)
end)))))


let fix_slack : slack  ->  FStar_Absyn_Syntax.typ = (fun slack -> (

let _45_1293 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.lower))
in (match (_45_1293) with
| (_45_1288, ul, kl, _45_1292) -> begin
(

let _45_1300 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.upper))
in (match (_45_1300) with
| (_45_1295, uh, kh, _45_1299) -> begin
(

let _45_1301 = (fix_slack_uv ((ul), (kl)) false)
in (

let _45_1303 = (fix_slack_uv ((uh), (kh)) true)
in (

let _45_1305 = (FStar_ST.op_Colon_Equals slack.flag true)
in (FStar_Absyn_Util.mk_conj (Prims.fst slack.lower) (Prims.fst slack.upper)))))
end))
end)))


let new_slack_var : FStar_Tc_Env.env  ->  slack  ->  ((FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.binders) = (fun env slack -> (

let xs = (let _142_825 = (let _142_824 = (destruct_flex_pattern env (Prims.snd slack.lower))
in (FStar_All.pipe_right _142_824 Prims.snd))
in (FStar_All.pipe_right _142_825 FStar_Util.must))
in (let _142_826 = (new_tvar (Prims.fst slack.lower).FStar_Absyn_Syntax.pos xs FStar_Absyn_Syntax.ktype)
in ((_142_826), (xs)))))


let new_slack_formula = (fun p env wl xs low high -> (

let _45_1318 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_45_1318) with
| (low_var, uv1) -> begin
(

let wl = (add_slack_add uv1 wl)
in (

let _45_1322 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_45_1322) with
| (high_var, uv2) -> begin
(

let wl = (add_slack_mul uv2 wl)
in (

let low = (match (low) with
| None -> begin
(FStar_Absyn_Util.mk_disj FStar_Absyn_Util.t_false low_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_disj f low_var)
end)
in (

let high = (match (high) with
| None -> begin
(FStar_Absyn_Util.mk_conj FStar_Absyn_Util.t_true high_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_conj f high_var)
end)
in (let _142_836 = (let _142_835 = (let _142_834 = (let _142_833 = (FStar_Util.mk_ref false)
in ((low), (high), (_142_833)))
in FStar_Absyn_Syntax.Meta_slack_formula (_142_834))
in (FStar_Absyn_Syntax.mk_Typ_meta _142_835))
in ((_142_836), (wl))))))
end)))
end)))


let destruct_slack : FStar_Tc_Env.env  ->  worklist  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ, slack) FStar_Util.either = (fun env wl phi -> (

let rec destruct = (fun conn_lid mk_conn phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _45_1346; FStar_Absyn_Syntax.pos = _45_1344; FStar_Absyn_Syntax.fvs = _45_1342; FStar_Absyn_Syntax.uvs = _45_1340}, ((FStar_Util.Inl (lhs), _45_1358))::((FStar_Util.Inl (rhs), _45_1353))::[]) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v conn_lid) -> begin
(

let rhs = (compress env wl rhs)
in (match (rhs.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
Some (((lhs), (rhs)))
end
| _45_1384 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some (rest, uvar) -> begin
(let _142_860 = (let _142_859 = (mk_conn lhs rest)
in ((_142_859), (uvar)))
in Some (_142_860))
end)
end))
end
| _45_1391 -> begin
None
end))
in (

let phi = (FStar_Absyn_Util.compress_typ phi)
in (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (phi1, phi2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _142_861 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_142_861))
end else begin
(

let low = (let _142_862 = (compress env wl phi1)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.or_lid FStar_Absyn_Util.mk_disj) _142_862))
in (

let hi = (let _142_863 = (compress env wl phi2)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.and_lid FStar_Absyn_Util.mk_disj) _142_863))
in (match (((low), (hi))) with
| (None, None) -> begin
(

let _45_1404 = (FStar_ST.op_Colon_Equals flag true)
in (let _142_864 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_142_864)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(FStar_All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
FStar_Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end
end
| _45_1422 -> begin
FStar_Util.Inl (phi)
end))))


let rec eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (

let t1 = (FStar_Absyn_Util.compress_typ t1)
in (

let t2 = (FStar_Absyn_Util.compress_typ t2)
in (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Typ_uvar (u1, _45_1439), FStar_Absyn_Syntax.Typ_uvar (u2, _45_1444)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Absyn_Syntax.Typ_app (h1, args1), FStar_Absyn_Syntax.Typ_app (h2, args2)) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _45_1458 -> begin
false
end))))
and eq_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e1 e2 -> (

let e1 = (FStar_Absyn_Util.compress_exp e1)
in (

let e2 = (FStar_Absyn_Util.compress_exp e2)
in (match (((e1.FStar_Absyn_Syntax.n), (e2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Exp_bvar (a), FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _45_1470), FStar_Absyn_Syntax.Exp_fvar (g, _45_1475)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Exp_constant (c), FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (FStar_Absyn_Syntax.Exp_app (h1, args1), FStar_Absyn_Syntax.Exp_app (h2, args2)) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _45_1494 -> begin
false
end))))
and eq_args : FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.args  ->  Prims.bool = (fun a1 a2 -> if ((FStar_List.length a1) = (FStar_List.length a2)) then begin
(FStar_List.forall2 (fun a1 a2 -> (match (((a1), (a2))) with
| ((FStar_Util.Inl (t), _45_1502), (FStar_Util.Inl (s), _45_1507)) -> begin
(eq_typ t s)
end
| ((FStar_Util.Inr (e), _45_1513), (FStar_Util.Inr (f), _45_1518)) -> begin
(eq_exp e f)
end
| _45_1522 -> begin
false
end)) a1 a2)
end else begin
false
end)


type flex_t =
(FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.args)


type im_or_proj_t =
((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.arg Prims.list * FStar_Absyn_Syntax.binders * ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ  ->  Prims.bool) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list))


let rigid_rigid : Prims.int = (Prims.parse_int "0")


let flex_rigid_eq : Prims.int = (Prims.parse_int "1")


let flex_refine_inner : Prims.int = (Prims.parse_int "2")


let flex_refine : Prims.int = (Prims.parse_int "3")


let flex_rigid : Prims.int = (Prims.parse_int "4")


let rigid_flex : Prims.int = (Prims.parse_int "5")


let refine_flex : Prims.int = (Prims.parse_int "6")


let flex_flex : Prims.int = (Prims.parse_int "7")


let compress_prob : worklist  ->  prob  ->  prob = (fun wl p -> (match (p) with
| KProb (p) -> begin
(let _142_894 = (

let _45_1527 = p
in (let _142_892 = (compress_k wl.tcenv wl p.lhs)
in (let _142_891 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _142_892; relation = _45_1527.relation; rhs = _142_891; element = _45_1527.element; logical_guard = _45_1527.logical_guard; scope = _45_1527.scope; reason = _45_1527.reason; loc = _45_1527.loc; rank = _45_1527.rank})))
in (FStar_All.pipe_right _142_894 (fun _142_893 -> KProb (_142_893))))
end
| TProb (p) -> begin
(let _142_898 = (

let _45_1531 = p
in (let _142_896 = (compress wl.tcenv wl p.lhs)
in (let _142_895 = (compress wl.tcenv wl p.rhs)
in {lhs = _142_896; relation = _45_1531.relation; rhs = _142_895; element = _45_1531.element; logical_guard = _45_1531.logical_guard; scope = _45_1531.scope; reason = _45_1531.reason; loc = _45_1531.loc; rank = _45_1531.rank})))
in (FStar_All.pipe_right _142_898 (fun _142_897 -> TProb (_142_897))))
end
| EProb (p) -> begin
(let _142_902 = (

let _45_1535 = p
in (let _142_900 = (compress_e wl.tcenv wl p.lhs)
in (let _142_899 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _142_900; relation = _45_1535.relation; rhs = _142_899; element = _45_1535.element; logical_guard = _45_1535.logical_guard; scope = _45_1535.scope; reason = _45_1535.reason; loc = _45_1535.loc; rank = _45_1535.rank})))
in (FStar_All.pipe_right _142_902 (fun _142_901 -> EProb (_142_901))))
end
| CProb (_45_1538) -> begin
p
end))


let rank : worklist  ->  prob  ->  (Prims.int * prob) = (fun wl prob -> (

let prob = (let _142_907 = (compress_prob wl prob)
in (FStar_All.pipe_right _142_907 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(

let rank = (match (((kp.lhs.FStar_Absyn_Syntax.n), (kp.rhs.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Kind_uvar (_45_1546), FStar_Absyn_Syntax.Kind_uvar (_45_1549)) -> begin
flex_flex
end
| (FStar_Absyn_Syntax.Kind_uvar (_45_1553), _45_1556) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
flex_rigid
end
end
| (_45_1559, FStar_Absyn_Syntax.Kind_uvar (_45_1561)) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
rigid_flex
end
end
| (_45_1565, _45_1567) -> begin
rigid_rigid
end)
in (let _142_909 = (FStar_All.pipe_right (

let _45_1570 = kp
in {lhs = _45_1570.lhs; relation = _45_1570.relation; rhs = _45_1570.rhs; element = _45_1570.element; logical_guard = _45_1570.logical_guard; scope = _45_1570.scope; reason = _45_1570.reason; loc = _45_1570.loc; rank = Some (rank)}) (fun _142_908 -> KProb (_142_908)))
in ((rank), (_142_909))))
end
| TProb (tp) -> begin
(

let _45_1577 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_45_1577) with
| (lh, _45_1576) -> begin
(

let _45_1581 = (FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_45_1581) with
| (rh, _45_1580) -> begin
(

let _45_1637 = (match (((lh.FStar_Absyn_Syntax.n), (rh.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Typ_uvar (_45_1583), FStar_Absyn_Syntax.Typ_uvar (_45_1586)) -> begin
((flex_flex), (tp))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
((flex_rigid_eq), (tp))
end
| (FStar_Absyn_Syntax.Typ_uvar (_45_1602), _45_1605) -> begin
(

let _45_1609 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_45_1609) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((flex_rigid), (tp))
end
| _45_1612 -> begin
(

let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _142_911 = (

let _45_1614 = tp
in (let _142_910 = (force_refinement ((b), (ref_opt)))
in {lhs = _45_1614.lhs; relation = _45_1614.relation; rhs = _142_910; element = _45_1614.element; logical_guard = _45_1614.logical_guard; scope = _45_1614.scope; reason = _45_1614.reason; loc = _45_1614.loc; rank = _45_1614.rank}))
in ((rank), (_142_911))))
end)
end))
end
| (_45_1617, FStar_Absyn_Syntax.Typ_uvar (_45_1619)) -> begin
(

let _45_1624 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_45_1624) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
((rigid_flex), (tp))
end
| _45_1627 -> begin
(let _142_913 = (

let _45_1628 = tp
in (let _142_912 = (force_refinement ((b), (ref_opt)))
in {lhs = _142_912; relation = _45_1628.relation; rhs = _45_1628.rhs; element = _45_1628.element; logical_guard = _45_1628.logical_guard; scope = _45_1628.scope; reason = _45_1628.reason; loc = _45_1628.loc; rank = _45_1628.rank}))
in ((refine_flex), (_142_913)))
end)
end))
end
| (_45_1631, _45_1633) -> begin
((rigid_rigid), (tp))
end)
in (match (_45_1637) with
| (rank, tp) -> begin
(let _142_915 = (FStar_All.pipe_right (

let _45_1638 = tp
in {lhs = _45_1638.lhs; relation = _45_1638.relation; rhs = _45_1638.rhs; element = _45_1638.element; logical_guard = _45_1638.logical_guard; scope = _45_1638.scope; reason = _45_1638.reason; loc = _45_1638.loc; rank = Some (rank)}) (fun _142_914 -> TProb (_142_914)))
in ((rank), (_142_915)))
end))
end))
end))
end
| EProb (ep) -> begin
(

let _45_1645 = (FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_45_1645) with
| (lh, _45_1644) -> begin
(

let _45_1649 = (FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_45_1649) with
| (rh, _45_1648) -> begin
(

let rank = (match (((lh.FStar_Absyn_Syntax.n), (rh.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Exp_uvar (_45_1651), FStar_Absyn_Syntax.Exp_uvar (_45_1654)) -> begin
flex_flex
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_45_1670, _45_1672) -> begin
rigid_rigid
end)
in (let _142_917 = (FStar_All.pipe_right (

let _45_1675 = ep
in {lhs = _45_1675.lhs; relation = _45_1675.relation; rhs = _45_1675.rhs; element = _45_1675.element; logical_guard = _45_1675.logical_guard; scope = _45_1675.scope; reason = _45_1675.reason; loc = _45_1675.loc; rank = Some (rank)}) (fun _142_916 -> EProb (_142_916)))
in ((rank), (_142_917))))
end))
end))
end
| CProb (cp) -> begin
(let _142_919 = (FStar_All.pipe_right (

let _45_1679 = cp
in {lhs = _45_1679.lhs; relation = _45_1679.relation; rhs = _45_1679.rhs; element = _45_1679.element; logical_guard = _45_1679.logical_guard; scope = _45_1679.scope; reason = _45_1679.reason; loc = _45_1679.loc; rank = Some (rigid_rigid)}) (fun _142_918 -> CProb (_142_918)))
in ((rigid_rigid), (_142_919)))
end)))


let next_prob : worklist  ->  (prob Prims.option * prob Prims.list * Prims.int) = (fun wl -> (

let rec aux = (fun _45_1686 probs -> (match (_45_1686) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
((min), (out), (min_rank))
end
| (hd)::tl -> begin
(

let _45_1694 = (rank wl hd)
in (match (_45_1694) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
((Some (hd)), ((FStar_List.append out tl)), (rank))
end
| Some (m) -> begin
((Some (hd)), ((FStar_List.append out ((m)::tl))), (rank))
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux ((rank), (Some (hd)), (out)) tl)
end
| Some (m) -> begin
(aux ((rank), (Some (hd)), ((m)::out)) tl)
end)
end else begin
(aux ((min_rank), (min), ((hd)::out)) tl)
end
end
end))
end)
end))
in (aux (((flex_flex + (Prims.parse_int "1"))), (None), ([])) wl.attempting)))


let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))


let rec solve_flex_rigid_join : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (

let _45_1705 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_969 = (prob_to_string env (TProb (tp)))
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _142_969))
end else begin
()
end
in (

let _45_1709 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_45_1709) with
| (u, args) -> begin
(

let _45_1715 = (((Prims.parse_int "0")), ((Prims.parse_int "1")), ((Prims.parse_int "2")), ((Prims.parse_int "3")), ((Prims.parse_int "4")))
in (match (_45_1715) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(

let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (

let base_types_match = (fun t1 t2 -> (

let _45_1724 = (FStar_Absyn_Util.head_and_args t1)
in (match (_45_1724) with
| (h1, args1) -> begin
(

let _45_1728 = (FStar_Absyn_Util.head_and_args t2)
in (match (_45_1728) with
| (h2, _45_1727) -> begin
(match (((h1.FStar_Absyn_Syntax.n), (h2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Typ_const (tc1), FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
if (FStar_Ident.lid_equals tc1.FStar_Absyn_Syntax.v tc2.FStar_Absyn_Syntax.v) then begin
if ((FStar_List.length args1) = (Prims.parse_int "0")) then begin
Some ([])
end else begin
(let _142_981 = (let _142_980 = (let _142_979 = (new_problem env t1 EQ t2 None t1.FStar_Absyn_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _142_978 -> TProb (_142_978)) _142_979))
in (_142_980)::[])
in Some (_142_981))
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
| _45_1740 -> begin
None
end)
end))
end)))
in (

let conjoin = (fun t1 t2 -> (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Typ_refine (x, phi1), FStar_Absyn_Syntax.Typ_refine (y, phi2)) -> begin
(

let m = (base_types_match x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(

let phi2 = (let _142_988 = (let _142_987 = (FStar_Absyn_Syntax.v_binder x)
in (let _142_986 = (FStar_Absyn_Syntax.v_binder y)
in (FStar_Absyn_Util.mk_subst_one_binder _142_987 _142_986)))
in (FStar_Absyn_Util.subst_typ _142_988 phi2))
in (let _142_992 = (let _142_991 = (let _142_990 = (let _142_989 = (FStar_Absyn_Util.mk_conj phi1 phi2)
in ((x), (_142_989)))
in (FStar_Absyn_Syntax.mk_Typ_refine _142_990 (Some (FStar_Absyn_Syntax.ktype)) t1.FStar_Absyn_Syntax.pos))
in ((_142_991), (m)))
in Some (_142_992)))
end))
end
| (_45_1759, FStar_Absyn_Syntax.Typ_refine (y, _45_1762)) -> begin
(

let m = (base_types_match t1 y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t2), (m)))
end))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _45_1772), _45_1776) -> begin
(

let m = (base_types_match x.FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end
| _45_1783 -> begin
(

let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some (((t1), (m)))
end))
end))
in (

let tt = u
in (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _45_1791) -> begin
(

let _45_1816 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _45_30 -> (match (_45_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(

let _45_1802 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_45_1802) with
| (u', _45_1801) -> begin
(match ((let _142_994 = (compress env wl u')
in _142_994.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv', _45_1805) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _45_1809 -> begin
false
end)
end))
end
| _45_1811 -> begin
false
end)
end
| _45_1813 -> begin
false
end))))
in (match (_45_1816) with
| (upper_bounds, rest) -> begin
(

let rec make_upper_bound = (fun _45_1820 tps -> (match (_45_1820) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some (((bound), (sub_probs)))
end
| (TProb (hd))::tl -> begin
(match ((let _142_999 = (compress env wl hd.rhs)
in (conjoin bound _142_999))) with
| Some (bound, sub) -> begin
(make_upper_bound ((bound), ((FStar_List.append sub sub_probs))) tl)
end
| None -> begin
None
end)
end
| _45_1833 -> begin
None
end)
end))
in (match ((let _142_1001 = (let _142_1000 = (compress env wl tp.rhs)
in ((_142_1000), ([])))
in (make_upper_bound _142_1001 upper_bounds))) with
| None -> begin
(

let _45_1835 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(

let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (

let _45_1842 = wl
in {attempting = sub_probs; wl_deferred = _45_1842.wl_deferred; subst = _45_1842.subst; ctr = _45_1842.ctr; slack_vars = _45_1842.slack_vars; defer_ok = _45_1842.defer_ok; smt_ok = _45_1842.smt_ok; tcenv = _45_1842.tcenv}))) with
| Success (subst, _45_1846) -> begin
(

let wl = (

let _45_1849 = wl
in {attempting = rest; wl_deferred = _45_1849.wl_deferred; subst = []; ctr = _45_1849.ctr; slack_vars = _45_1849.slack_vars; defer_ok = _45_1849.defer_ok; smt_ok = _45_1849.smt_ok; tcenv = _45_1849.tcenv})
in (

let wl = (solve_prob (TProb (tp)) None subst wl)
in (

let _45_1855 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _45_1858 -> begin
None
end))
end))
end))
end
| _45_1860 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve : FStar_Tc_Env.env  ->  worklist  ->  solution = (fun env probs -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(

let probs = (

let _45_1868 = probs
in {attempting = tl; wl_deferred = _45_1868.wl_deferred; subst = _45_1868.subst; ctr = _45_1868.ctr; slack_vars = _45_1868.slack_vars; defer_ok = _45_1868.defer_ok; smt_ok = _45_1868.smt_ok; tcenv = _45_1868.tcenv})
in (match (hd) with
| KProb (kp) -> begin
(solve_k' env (maybe_invert kp) probs)
end
| TProb (tp) -> begin
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
end
| EProb (ep) -> begin
(solve_e' env (maybe_invert ep) probs)
end
| CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end))
end
| (None, _45_1884, _45_1886) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success (((probs.subst), ({carry = []; slack = probs.slack_vars})))
end
| _45_1890 -> begin
(

let _45_1899 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _45_1896 -> (match (_45_1896) with
| (c, _45_1893, _45_1895) -> begin
(c < probs.ctr)
end))))
in (match (_45_1899) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _142_1010 = (let _142_1009 = (let _142_1008 = (FStar_List.map (fun _45_1905 -> (match (_45_1905) with
| (_45_1902, x, y) -> begin
((x), (y))
end)) probs.wl_deferred)
in {carry = _142_1008; slack = probs.slack_vars})
in ((probs.subst), (_142_1009)))
in Success (_142_1010))
end
| _45_1907 -> begin
(let _142_1013 = (

let _45_1908 = probs
in (let _142_1012 = (FStar_All.pipe_right attempt (FStar_List.map (fun _45_1915 -> (match (_45_1915) with
| (_45_1911, _45_1913, y) -> begin
y
end))))
in {attempting = _142_1012; wl_deferred = rest; subst = _45_1908.subst; ctr = _45_1908.ctr; slack_vars = _45_1908.slack_vars; defer_ok = _45_1908.defer_ok; smt_ok = _45_1908.smt_ok; tcenv = _45_1908.tcenv}))
in (solve env _142_1013))
end)
end))
end)
end))
and solve_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  prob  ->  worklist  ->  (FStar_Absyn_Syntax.binders  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.subst_elt Prims.list  ->  prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (

let rec aux = (fun scope env subst xs ys -> (match (((xs), (ys))) with
| ([], []) -> begin
(

let rhs_prob = (rhs scope env subst)
in (

let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl ((((rhs_prob)::[]), (formula)))))
end
| ((((FStar_Util.Inl (_), _))::_, ((FStar_Util.Inr (_), _))::_)) | ((((FStar_Util.Inr (_), _))::_, ((FStar_Util.Inl (_), _))::_)) -> begin
FStar_Util.Inr ("sort mismatch")
end
| ((hd1)::xs, (hd2)::ys) -> begin
(

let subst = (let _142_1039 = (FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (FStar_List.append _142_1039 subst))
in (

let env = (let _142_1040 = (FStar_Tc_Env.binding_of_binder hd2)
in (FStar_Tc_Env.push_local_binding env _142_1040))
in (

let prob = (match ((((Prims.fst hd1)), ((Prims.fst hd2)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _142_1044 = (let _142_1043 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _142_1042 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _142_1043 _142_1042 b.FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (FStar_All.pipe_left (fun _142_1041 -> KProb (_142_1041)) _142_1044))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _142_1048 = (let _142_1047 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _142_1046 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _142_1047 _142_1046 y.FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (FStar_All.pipe_left (fun _142_1045 -> TProb (_142_1045)) _142_1048))
end
| _45_1991 -> begin
(FStar_All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| FStar_Util.Inr (msg) -> begin
FStar_Util.Inr (msg)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let phi = (let _142_1050 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _142_1049 = (FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (FStar_Absyn_Util.mk_conj _142_1050 _142_1049)))
in FStar_Util.Inl ((((prob)::sub_probs), (phi))))
end))))
end
| _45_2001 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (

let scope = (FStar_Tc_Env.binders env)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(

let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_k : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _45_2016 -> begin
(FStar_All.failwith "impossible")
end))
and solve_k' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (

let orig = KProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _142_1057 = (solve_prob orig None [] wl)
in (solve env _142_1057))
end else begin
(

let k1 = problem.lhs
in (

let k2 = problem.rhs
in if (FStar_Util.physical_equality k1 k2) then begin
(let _142_1058 = (solve_prob orig None [] wl)
in (solve env _142_1058))
end else begin
(

let r = (FStar_Tc_Env.get_range env)
in (

let imitate_k = (fun _45_2032 -> (match (_45_2032) with
| (rel, u, ps, xs, (h, qs)) -> begin
(

let r = (FStar_Tc_Env.get_range env)
in (

let _45_2037 = (imitation_sub_probs orig env xs ps qs)
in (match (_45_2037) with
| (sub_probs, gs_xs, f) -> begin
(

let im = (let _142_1074 = (let _142_1073 = (h gs_xs)
in ((xs), (_142_1073)))
in (FStar_Absyn_Syntax.mk_Kind_lam _142_1074 r))
in (

let wl = (solve_prob orig (Some (f)) ((UK (((u), (im))))::[]) wl)
in (solve env (attempt sub_probs wl))))
end)))
end))
in (

let flex_rigid = (fun rel u args k -> (

let maybe_vars1 = (pat_vars env [] args)
in (match (maybe_vars1) with
| Some (xs) -> begin
(

let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (

let fvs2 = (FStar_Absyn_Util.freevars_kind k2)
in (

let uvs2 = (FStar_Absyn_Util.uvars_in_kind k2)
in if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && (not ((FStar_Util.set_mem u uvs2.FStar_Absyn_Syntax.uvars_k)))) then begin
(

let k1 = (FStar_Absyn_Syntax.mk_Kind_lam ((xs), (k2)) r)
in (let _142_1083 = (solve_prob orig None ((UK (((u), (k1))))::[]) wl)
in (solve env _142_1083)))
end else begin
(let _142_1088 = (let _142_1087 = (FStar_All.pipe_right xs FStar_Absyn_Util.args_of_non_null_binders)
in (let _142_1086 = (decompose_kind env k)
in ((rel), (u), (_142_1087), (xs), (_142_1086))))
in (imitate_k _142_1088))
end)))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match (((k1.FStar_Absyn_Syntax.n), (k2.FStar_Absyn_Syntax.n))) with
| ((FStar_Absyn_Syntax.Kind_type, FStar_Absyn_Syntax.Kind_type)) | ((FStar_Absyn_Syntax.Kind_effect, FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _142_1089 = (solve_prob orig None [] wl)
in (FStar_All.pipe_left (solve env) _142_1089))
end
| (FStar_Absyn_Syntax.Kind_abbrev (_45_2060, k1), _45_2065) -> begin
(solve_k env (

let _45_2067 = problem
in {lhs = k1; relation = _45_2067.relation; rhs = _45_2067.rhs; element = _45_2067.element; logical_guard = _45_2067.logical_guard; scope = _45_2067.scope; reason = _45_2067.reason; loc = _45_2067.loc; rank = _45_2067.rank}) wl)
end
| (_45_2070, FStar_Absyn_Syntax.Kind_abbrev (_45_2072, k2)) -> begin
(solve_k env (

let _45_2077 = problem
in {lhs = _45_2077.lhs; relation = _45_2077.relation; rhs = k2; element = _45_2077.element; logical_guard = _45_2077.logical_guard; scope = _45_2077.scope; reason = _45_2077.reason; loc = _45_2077.loc; rank = _45_2077.rank}) wl)
end
| (FStar_Absyn_Syntax.Kind_arrow (bs1, k1'), FStar_Absyn_Syntax.Kind_arrow (bs2, k2')) -> begin
(

let sub_prob = (fun scope env subst -> (let _142_1098 = (let _142_1097 = (FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _142_1097 problem.relation k2' None "Arrow-kind result"))
in (FStar_All.pipe_left (fun _142_1096 -> KProb (_142_1096)) _142_1098)))
in (solve_binders env bs1 bs2 orig wl sub_prob))
end
| (FStar_Absyn_Syntax.Kind_uvar (u1, args1), FStar_Absyn_Syntax.Kind_uvar (u2, args2)) -> begin
(

let maybe_vars1 = (pat_vars env [] args1)
in (

let maybe_vars2 = (pat_vars env [] args2)
in (match (((maybe_vars1), (maybe_vars2))) with
| ((None, _)) | ((_, None)) -> begin
(giveup env "flex-flex: non patterns" (KProb (problem)))
end
| (Some (xs), Some (ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(

let zs = (intersect_vars xs ys)
in (

let _45_2120 = (new_kvar r zs)
in (match (_45_2120) with
| (u, _45_2119) -> begin
(

let k1 = (FStar_Absyn_Syntax.mk_Kind_lam ((xs), (u)) r)
in (

let k2 = (FStar_Absyn_Syntax.mk_Kind_lam ((ys), (u)) r)
in (

let wl = (solve_prob orig None ((UK (((u1), (k1))))::(UK (((u2), (k2))))::[]) wl)
in (solve env wl))))
end)))
end
end)))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, args), _45_2129) -> begin
(flex_rigid problem.relation u args k2)
end
| (_45_2132, FStar_Absyn_Syntax.Kind_uvar (u, args)) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, FStar_Absyn_Syntax.Kind_unknown)) -> begin
(FStar_All.failwith "Impossible")
end
| _45_2159 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end))
end))
and solve_t : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (

let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _45_2167 -> begin
(FStar_All.failwith "Impossible")
end)))
and solve_t' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (

let giveup_or_defer = (fun orig msg -> if wl.defer_ok then begin
(

let _45_2174 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1109 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _142_1109 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
in (

let imitate_t = (fun orig env wl p -> (

let _45_2191 = p
in (match (_45_2191) with
| ((u, k), ps, xs, (h, _45_2188, qs)) -> begin
(

let xs = (sn_binders env xs)
in (

let r = (FStar_Tc_Env.get_range env)
in (

let _45_2197 = (imitation_sub_probs orig env xs ps qs)
in (match (_45_2197) with
| (sub_probs, gs_xs, formula) -> begin
(

let im = (let _142_1121 = (let _142_1120 = (h gs_xs)
in ((xs), (_142_1120)))
in (FStar_Absyn_Syntax.mk_Typ_lam' _142_1121 None r))
in (

let _45_2199 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1126 = (FStar_Absyn_Print.typ_to_string im)
in (let _142_1125 = (FStar_Absyn_Print.tag_of_typ im)
in (let _142_1124 = (let _142_1122 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _142_1122 (FStar_String.concat ", ")))
in (let _142_1123 = (FStar_Tc_Normalize.formula_norm_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _142_1126 _142_1125 _142_1124 _142_1123)))))
end else begin
()
end
in (

let wl = (solve_prob orig (Some (formula)) ((UT (((((u), (k))), (im))))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (

let project_t = (fun orig env wl i p -> (

let _45_2215 = p
in (match (_45_2215) with
| (u, ps, xs, (h, matches, qs)) -> begin
(

let r = (FStar_Tc_Env.get_range env)
in (

let pi = (FStar_List.nth ps i)
in (

let rec gs = (fun k -> (

let _45_2222 = (FStar_Absyn_Util.kind_formals k)
in (match (_45_2222) with
| (bs, k) -> begin
(

let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
(([]), ([]))
end
| (hd)::tl -> begin
(

let _45_2251 = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(

let k_a = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (

let _45_2235 = (new_tvar r xs k_a)
in (match (_45_2235) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_Tc_Normalize.eta_expand env gi_xs)
in (

let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app ((gi), (ps)) (Some (k_a)) r)
in (

let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (gi_xs))))::subst
end
in (let _142_1146 = (FStar_Absyn_Syntax.targ gi_xs)
in (let _142_1145 = (FStar_Absyn_Syntax.targ gi_ps)
in ((_142_1146), (_142_1145), (subst)))))))
end)))
end
| FStar_Util.Inr (x) -> begin
(

let t_x = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (

let _45_2244 = (new_evar r xs t_x)
in (match (_45_2244) with
| (gi_xs, gi) -> begin
(

let gi_xs = (FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (

let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app ((gi), (ps)) (Some (t_x)) r)
in (

let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (gi_xs))))::subst
end
in (let _142_1148 = (FStar_Absyn_Syntax.varg gi_xs)
in (let _142_1147 = (FStar_Absyn_Syntax.varg gi_ps)
in ((_142_1148), (_142_1147), (subst)))))))
end)))
end)
in (match (_45_2251) with
| (gi_xs, gi_ps, subst) -> begin
(

let _45_2254 = (aux subst tl)
in (match (_45_2254) with
| (gi_xs', gi_ps') -> begin
(((gi_xs)::gi_xs'), ((gi_ps)::gi_ps'))
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _142_1150 = (let _142_1149 = (FStar_List.nth xs i)
in (FStar_All.pipe_left Prims.fst _142_1149))
in (((Prims.fst pi)), (_142_1150)))) with
| (FStar_Util.Inl (pi), FStar_Util.Inl (xi)) -> begin
if (let _142_1151 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _142_1151)) then begin
None
end else begin
(

let _45_2263 = (gs xi.FStar_Absyn_Syntax.sort)
in (match (_45_2263) with
| (g_xs, _45_2262) -> begin
(

let xi = (FStar_Absyn_Util.btvar_to_typ xi)
in (

let proj = (let _142_1153 = (let _142_1152 = (FStar_Absyn_Syntax.mk_Typ_app' ((xi), (g_xs)) (Some (FStar_Absyn_Syntax.ktype)) r)
in ((xs), (_142_1152)))
in (FStar_Absyn_Syntax.mk_Typ_lam _142_1153 None r))
in (

let sub = (let _142_1159 = (let _142_1158 = (FStar_Absyn_Syntax.mk_Typ_app' ((proj), (ps)) (Some (FStar_Absyn_Syntax.ktype)) r)
in (let _142_1157 = (let _142_1156 = (FStar_List.map (fun _45_2271 -> (match (_45_2271) with
| (_45_2267, _45_2269, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _142_1156))
in (mk_problem (p_scope orig) orig _142_1158 (p_rel orig) _142_1157 None "projection")))
in (FStar_All.pipe_left (fun _142_1154 -> TProb (_142_1154)) _142_1159))
in (

let _45_2273 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1161 = (FStar_Absyn_Print.typ_to_string proj)
in (let _142_1160 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _142_1161 _142_1160)))
end else begin
()
end
in (

let wl = (let _142_1163 = (let _142_1162 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_142_1162))
in (solve_prob orig _142_1163 ((UT (((u), (proj))))::[]) wl))
in (let _142_1165 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _142_1164 -> Some (_142_1164)) _142_1165)))))))
end))
end
end
| _45_2277 -> begin
None
end))))
end)))
in (

let solve_t_flex_rigid = (fun orig lhs t2 wl -> (

let _45_2289 = lhs
in (match (_45_2289) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(

let subterms = (fun ps -> (

let xs = (let _142_1192 = (FStar_Absyn_Util.kind_formals k)
in (FStar_All.pipe_right _142_1192 Prims.fst))
in (

let xs = (FStar_Absyn_Util.name_binders xs)
in (let _142_1197 = (decompose_typ env t2)
in ((((uv), (k))), (ps), (xs), (_142_1197))))))
in (

let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
if (i = (~- ((Prims.parse_int "1")))) then begin
(match ((imitate_t orig env wl st)) with
| Failed (_45_2299) -> begin
(imitate_or_project n st (i + (Prims.parse_int "1")))
end
| sol -> begin
sol
end)
end else begin
(match ((project_t orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(imitate_or_project n st (i + (Prims.parse_int "1")))
end
| Some (sol) -> begin
sol
end)
end
end)
in (

let check_head = (fun fvs1 t2 -> (

let _45_2315 = (FStar_Absyn_Util.head_and_args t2)
in (match (_45_2315) with
| (hd, _45_2314) -> begin
(match (hd.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _45_2326 -> begin
(

let fvs_hd = (FStar_Absyn_Util.freevars_typ hd)
in if (FStar_Absyn_Util.fvs_included fvs_hd fvs1) then begin
true
end else begin
(

let _45_2328 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1208 = (FStar_Absyn_Print.freevars_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _142_1208))
end else begin
()
end
in false)
end)
end)
end)))
in (

let imitate_ok = (fun t2 -> (

let fvs_hd = (let _142_1212 = (let _142_1211 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _142_1211 Prims.fst))
in (FStar_All.pipe_right _142_1212 FStar_Absyn_Util.freevars_typ))
in if (FStar_Util.set_is_empty fvs_hd.FStar_Absyn_Syntax.ftvs) then begin
(~- ((Prims.parse_int "1")))
end else begin
(Prims.parse_int "0")
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(

let t1 = (sn env t1)
in (

let t2 = (sn env t2)
in (

let fvs1 = (FStar_Absyn_Util.freevars_typ t1)
in (

let fvs2 = (FStar_Absyn_Util.freevars_typ t2)
in (

let _45_2341 = (occurs_check env wl ((uv), (k)) t2)
in (match (_45_2341) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _142_1214 = (let _142_1213 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _142_1213))
in (giveup_or_defer orig _142_1214))
end else begin
if (FStar_Absyn_Util.fvs_included fvs2 fvs1) then begin
if ((FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ)) then begin
(let _142_1215 = (subterms args_lhs)
in (imitate_t orig env wl _142_1215))
end else begin
(

let _45_2342 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1218 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1217 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _142_1216 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _142_1218 _142_1217 _142_1216))))
end else begin
()
end
in (

let sol = (match (vars) with
| [] -> begin
t2
end
| _45_2346 -> begin
(let _142_1220 = (let _142_1219 = (sn_binders env vars)
in ((_142_1219), (t2)))
in (FStar_Absyn_Syntax.mk_Typ_lam _142_1220 None t1.FStar_Absyn_Syntax.pos))
end)
in (

let wl = (solve_prob orig None ((UT (((((uv), (k))), (sol))))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(

let _45_2349 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1223 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1222 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _142_1221 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _142_1223 _142_1222 _142_1221))))
end else begin
()
end
in (let _142_1224 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _142_1224 (~- ((Prims.parse_int "1"))))))
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
if (let _142_1225 = (FStar_Absyn_Util.freevars_typ t1)
in (check_head _142_1225 t2)) then begin
(

let im_ok = (imitate_ok t2)
in (

let _45_2353 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1226 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _142_1226 (if (im_ok < (Prims.parse_int "0")) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _142_1227 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _142_1227 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (

let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(

let force_quasi_pattern = (fun xs_opt _45_2365 -> (match (_45_2365) with
| (t, u, k, args) -> begin
(

let rec aux = (fun binders ys args -> (match (args) with
| [] -> begin
(

let ys = (FStar_List.rev ys)
in (

let binders = (FStar_List.rev binders)
in (

let kk = (FStar_Tc_Recheck.recompute_kind t)
in (

let _45_2377 = (new_tvar t.FStar_Absyn_Syntax.pos ys kk)
in (match (_45_2377) with
| (t', _45_2376) -> begin
(

let _45_2383 = (destruct_flex_t t')
in (match (_45_2383) with
| (u1_ys, u1, k1, _45_2382) -> begin
(

let sol = (let _142_1245 = (let _142_1244 = (FStar_Absyn_Syntax.mk_Typ_lam ((binders), (u1_ys)) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((((u), (k))), (_142_1244)))
in UT (_142_1245))
in ((sol), (((t'), (u), (k1), (ys)))))
end))
end)))))
end
| (hd)::tl -> begin
(

let new_binder = (fun hd -> (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let _142_1249 = (let _142_1248 = (FStar_Tc_Recheck.recompute_kind a)
in (FStar_All.pipe_right _142_1248 (FStar_Absyn_Util.gen_bvar_p a.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _142_1249 FStar_Absyn_Syntax.t_binder))
end
| FStar_Util.Inr (x) -> begin
(let _142_1251 = (let _142_1250 = (FStar_Tc_Recheck.recompute_typ x)
in (FStar_All.pipe_right _142_1250 (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _142_1251 FStar_Absyn_Syntax.v_binder))
end))
in (

let _45_2402 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _142_1252 = (new_binder hd)
in ((_142_1252), (ys)))
end
| Some (y) -> begin
(match (xs_opt) with
| None -> begin
((y), ((y)::ys))
end
| Some (xs) -> begin
if (FStar_All.pipe_right xs (FStar_Util.for_some (FStar_Absyn_Util.eq_binder y))) then begin
((y), ((y)::ys))
end else begin
(let _142_1253 = (new_binder hd)
in ((_142_1253), (ys)))
end
end)
end)
in (match (_45_2402) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (

let solve_both_pats = (fun wl _45_2408 _45_2412 k r -> (match (((_45_2408), (_45_2412))) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _142_1264 = (solve_prob orig None [] wl)
in (solve env _142_1264))
end else begin
(

let xs = (sn_binders env xs)
in (

let ys = (sn_binders env ys)
in (

let zs = (intersect_vars xs ys)
in (

let _45_2421 = (new_tvar r zs k)
in (match (_45_2421) with
| (u_zs, _45_2420) -> begin
(

let sub1 = (FStar_Absyn_Syntax.mk_Typ_lam' ((xs), (u_zs)) (Some (k1)) r)
in (

let _45_2425 = (occurs_check env wl ((u1), (k1)) sub1)
in (match (_45_2425) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(

let sol1 = UT (((((u1), (k1))), (sub1)))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(

let sub2 = (FStar_Absyn_Syntax.mk_Typ_lam' ((ys), (u_zs)) (Some (k2)) r)
in (

let _45_2431 = (occurs_check env wl ((u2), (k2)) sub2)
in (match (_45_2431) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(

let sol2 = UT (((((u2), (k2))), (sub2)))
in (

let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end)))))
end
end))
in (

let solve_one_pat = (fun _45_2439 _45_2444 -> (match (((_45_2439), (_45_2444))) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(

let _45_2445 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1270 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1269 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _142_1270 _142_1269)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(

let sub_probs = (FStar_List.map2 (fun a b -> (

let a = (FStar_Absyn_Util.arg_of_non_null_binder a)
in (match ((((Prims.fst a)), ((Prims.fst b)))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _142_1274 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _142_1274 (fun _142_1273 -> TProb (_142_1273))))
end
| (FStar_Util.Inr (t1), FStar_Util.Inr (t2)) -> begin
(let _142_1276 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _142_1276 (fun _142_1275 -> EProb (_142_1275))))
end
| _45_2461 -> begin
(FStar_All.failwith "Impossible")
end))) xs args2)
in (

let guard = (let _142_1278 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _142_1278))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(

let t2 = (sn env t2)
in (

let rhs_vars = (FStar_Absyn_Util.freevars_typ t2)
in (

let _45_2471 = (occurs_check env wl ((u1), (k1)) t2)
in (match (_45_2471) with
| (occurs_ok, _45_2470) -> begin
(

let lhs_vars = (FStar_Absyn_Syntax.freevars_of_binders xs)
in if (occurs_ok && (FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)) then begin
(

let sol = (let _142_1280 = (let _142_1279 = (FStar_Absyn_Syntax.mk_Typ_lam' ((xs), (t2)) (Some (k1)) t1.FStar_Absyn_Syntax.pos)
in ((((u1), (k1))), (_142_1279)))
in UT (_142_1280))
in (

let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(

let _45_2482 = (force_quasi_pattern (Some (xs)) ((t2), (u2), (k2), (args2)))
in (match (_45_2482) with
| (sol, (_45_2477, u2, k2, ys)) -> begin
(

let wl = (extend_solution sol wl)
in (

let _45_2484 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _142_1281 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _142_1281))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _45_2489 -> begin
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

let _45_2494 = lhs
in (match (_45_2494) with
| (t1, u1, k1, args1) -> begin
(

let _45_2499 = rhs
in (match (_45_2499) with
| (t2, u2, k2, args2) -> begin
(

let maybe_pat_vars1 = (pat_vars env [] args1)
in (

let maybe_pat_vars2 = (pat_vars env [] args2)
in (

let r = t2.FStar_Absyn_Syntax.pos
in (match (((maybe_pat_vars1), (maybe_pat_vars2))) with
| (Some (xs), Some (ys)) -> begin
(let _142_1282 = (FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl ((u1), (k1), (xs)) ((u2), (k2), (ys)) _142_1282 t2.FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat ((t1), (u1), (k1), (xs)) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat ((t2), (u2), (k2), (ys)) lhs)
end
| _45_2517 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(

let _45_2521 = (force_quasi_pattern None ((t1), (u1), (k1), (args1)))
in (match (_45_2521) with
| (sol, _45_2520) -> begin
(

let wl = (extend_solution sol wl)
in (

let _45_2523 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _142_1283 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _142_1283))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _45_2528 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (

let orig = TProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _142_1284 = (solve_prob orig None [] wl)
in (solve env _142_1284))
end else begin
(

let t1 = problem.lhs
in (

let t2 = problem.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _142_1285 = (solve_prob orig None [] wl)
in (solve env _142_1285))
end else begin
(

let _45_2532 = if (FStar_Tc_Env.debug env (FStar_Options.Other ("Rel"))) then begin
(let _142_1288 = (prob_to_string env orig)
in (let _142_1287 = (let _142_1286 = (FStar_List.map (uvi_to_string wl.tcenv) wl.subst)
in (FStar_All.pipe_right _142_1286 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Attempting %s\n\tSubst is %s\n" _142_1288 _142_1287)))
end else begin
()
end
in (

let r = (FStar_Tc_Env.get_range env)
in (

let match_num_binders = (fun _45_2537 _45_2540 -> (match (((_45_2537), (_45_2540))) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(

let curry = (fun n bs mk_cod -> (

let _45_2547 = (FStar_Util.first_N n bs)
in (match (_45_2547) with
| (bs, rest) -> begin
(let _142_1318 = (mk_cod rest)
in ((bs), (_142_1318)))
end)))
in (

let l1 = (FStar_List.length bs1)
in (

let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _142_1322 = (let _142_1319 = (mk_cod1 [])
in ((bs1), (_142_1319)))
in (let _142_1321 = (let _142_1320 = (mk_cod2 [])
in ((bs2), (_142_1320)))
in ((_142_1322), (_142_1321))))
end else begin
if (l1 > l2) then begin
(let _142_1325 = (curry l2 bs1 mk_cod1)
in (let _142_1324 = (let _142_1323 = (mk_cod2 [])
in ((bs2), (_142_1323)))
in ((_142_1325), (_142_1324))))
end else begin
(let _142_1328 = (let _142_1326 = (mk_cod1 [])
in ((bs1), (_142_1326)))
in (let _142_1327 = (curry l1 bs2 mk_cod2)
in ((_142_1328), (_142_1327))))
end
end)))
end))
in (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (FStar_Absyn_Util.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
(let _142_1329 = (solve_prob orig None [] wl)
in (solve env _142_1329))
end else begin
(let _142_1333 = (let _142_1332 = (let _142_1331 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _142_1330 -> Some (_142_1330)) _142_1331))
in (solve_prob orig _142_1332 [] wl))
in (solve env _142_1333))
end
end
| (FStar_Absyn_Syntax.Typ_fun (bs1, c1), FStar_Absyn_Syntax.Typ_fun (bs2, c2)) -> begin
(

let mk_c = (fun c _45_31 -> (match (_45_31) with
| [] -> begin
c
end
| bs -> begin
(let _142_1338 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Total _142_1338))
end))
in (

let _45_2578 = (match_num_binders ((bs1), ((mk_c c1))) ((bs2), ((mk_c c2))))
in (match (_45_2578) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let c1 = (FStar_Absyn_Util.subst_comp subst c1)
in (

let rel = if (FStar_Options.use_eq_at_higher_order ()) then begin
EQ
end else begin
problem.relation
end
in (

let _45_2584 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(let _142_1345 = (let _142_1344 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_right _142_1344 FStar_Range.string_of_range))
in (FStar_Util.print2 "(%s) Using relation %s at higher order\n" _142_1345 (rel_to_string rel)))
end else begin
()
end
in (let _142_1347 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _142_1346 -> CProb (_142_1346)) _142_1347)))))))
end)))
end
| (FStar_Absyn_Syntax.Typ_lam (bs1, t1'), FStar_Absyn_Syntax.Typ_lam (bs2, t2')) -> begin
(

let mk_t = (fun t _45_32 -> (match (_45_32) with
| [] -> begin
t
end
| bs -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t.FStar_Absyn_Syntax.pos)
end))
in (

let _45_2606 = (match_num_binders ((bs1), ((mk_t t1'))) ((bs2), ((mk_t t2'))))
in (match (_45_2606) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (

let t1' = (FStar_Absyn_Util.subst_typ subst t1')
in (let _142_1358 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (FStar_All.pipe_left (fun _142_1357 -> TProb (_142_1357)) _142_1358)))))
end)))
end
| (FStar_Absyn_Syntax.Typ_refine (_45_2612), FStar_Absyn_Syntax.Typ_refine (_45_2615)) -> begin
(

let _45_2620 = (as_refinement env wl t1)
in (match (_45_2620) with
| (x1, phi1) -> begin
(

let _45_2623 = (as_refinement env wl t2)
in (match (_45_2623) with
| (x2, phi2) -> begin
(

let base_prob = (let _142_1360 = (mk_problem (p_scope orig) orig x1.FStar_Absyn_Syntax.sort problem.relation x2.FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (FStar_All.pipe_left (fun _142_1359 -> TProb (_142_1359)) _142_1360))
in (

let x1_for_x2 = (let _142_1362 = (FStar_Absyn_Syntax.v_binder x1)
in (let _142_1361 = (FStar_Absyn_Syntax.v_binder x2)
in (FStar_Absyn_Util.mk_subst_one_binder _142_1362 _142_1361)))
in (

let phi2 = (FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (

let mk_imp = (fun imp phi1 phi2 -> (let _142_1379 = (imp phi1 phi2)
in (FStar_All.pipe_right _142_1379 (guard_on_element problem x1))))
in (

let fallback = (fun _45_2632 -> (match (()) with
| () -> begin
(

let impl = if (problem.relation = EQ) then begin
(mk_imp FStar_Absyn_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Absyn_Util.mk_imp phi1 phi2)
end
in (

let guard = (let _142_1382 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _142_1382 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.relation = EQ) then begin
(

let ref_prob = (let _142_1384 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _142_1383 -> TProb (_142_1383)) _142_1384))
in (match ((solve env (

let _45_2637 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; subst = _45_2637.subst; ctr = _45_2637.ctr; slack_vars = _45_2637.slack_vars; defer_ok = false; smt_ok = _45_2637.smt_ok; tcenv = _45_2637.tcenv}))) with
| Failed (_45_2640) -> begin
(fallback ())
end
| Success (subst, _45_2644) -> begin
(

let guard = (let _142_1387 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _142_1386 = (let _142_1385 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _142_1385 (guard_on_element problem x1)))
in (FStar_Absyn_Util.mk_conj _142_1387 _142_1386)))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (

let wl = (

let _45_2649 = wl
in {attempting = _45_2649.attempting; wl_deferred = _45_2649.wl_deferred; subst = subst; ctr = (wl.ctr + (Prims.parse_int "1")); slack_vars = _45_2649.slack_vars; defer_ok = _45_2649.defer_ok; smt_ok = _45_2649.smt_ok; tcenv = _45_2649.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end)))))
end))
end))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _142_1389 = (destruct_flex_t t1)
in (let _142_1388 = (destruct_flex_t t2)
in (flex_flex orig _142_1389 _142_1388)))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) when (problem.relation = EQ) -> begin
(let _142_1390 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _142_1390 t2 wl))
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(

let new_rel = problem.relation
in if (let _142_1391 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _142_1391)) then begin
(let _142_1394 = (FStar_All.pipe_left (fun _142_1392 -> TProb (_142_1392)) (

let _45_2808 = problem
in {lhs = _45_2808.lhs; relation = new_rel; rhs = _45_2808.rhs; element = _45_2808.element; logical_guard = _45_2808.logical_guard; scope = _45_2808.scope; reason = _45_2808.reason; loc = _45_2808.loc; rank = _45_2808.rank}))
in (let _142_1393 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _142_1394 _142_1393 t2 wl)))
end else begin
(

let _45_2812 = (base_and_refinement env wl t2)
in (match (_45_2812) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _142_1397 = (FStar_All.pipe_left (fun _142_1395 -> TProb (_142_1395)) (

let _45_2814 = problem
in {lhs = _45_2814.lhs; relation = new_rel; rhs = _45_2814.rhs; element = _45_2814.element; logical_guard = _45_2814.logical_guard; scope = _45_2814.scope; reason = _45_2814.reason; loc = _45_2814.loc; rank = _45_2814.rank}))
in (let _142_1396 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _142_1397 _142_1396 t_base wl)))
end
| Some (y, phi) -> begin
(

let y' = (

let _45_2820 = y
in {FStar_Absyn_Syntax.v = _45_2820.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t1; FStar_Absyn_Syntax.p = _45_2820.FStar_Absyn_Syntax.p})
in (

let impl = (guard_on_element problem y' phi)
in (

let base_prob = (let _142_1399 = (mk_problem problem.scope orig t1 new_rel y.FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _142_1398 -> TProb (_142_1398)) _142_1399))
in (

let guard = (let _142_1400 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _142_1400 impl))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
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
(

let _45_2855 = (base_and_refinement env wl t1)
in (match (_45_2855) with
| (t_base, _45_2854) -> begin
(solve_t env (

let _45_2856 = problem
in {lhs = t_base; relation = EQ; rhs = _45_2856.rhs; element = _45_2856.element; logical_guard = _45_2856.logical_guard; scope = _45_2856.scope; reason = _45_2856.reason; loc = _45_2856.loc; rank = _45_2856.rank}) wl)
end))
end
end
| (FStar_Absyn_Syntax.Typ_refine (_45_2859), _45_2862) -> begin
(

let t2 = (let _142_1401 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _142_1401))
in (solve_t env (

let _45_2865 = problem
in {lhs = _45_2865.lhs; relation = _45_2865.relation; rhs = t2; element = _45_2865.element; logical_guard = _45_2865.logical_guard; scope = _45_2865.scope; reason = _45_2865.reason; loc = _45_2865.loc; rank = _45_2865.rank}) wl))
end
| (_45_2868, FStar_Absyn_Syntax.Typ_refine (_45_2870)) -> begin
(

let t1 = (let _142_1402 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _142_1402))
in (solve_t env (

let _45_2874 = problem
in {lhs = t1; relation = _45_2874.relation; rhs = _45_2874.rhs; element = _45_2874.element; logical_guard = _45_2874.logical_guard; scope = _45_2874.scope; reason = _45_2874.reason; loc = _45_2874.loc; rank = _45_2874.rank}) wl))
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) | ((FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, FStar_Absyn_Syntax.Typ_const (_))) | ((_, FStar_Absyn_Syntax.Typ_app (_))) -> begin
(

let _45_2914 = (head_matches_delta env wl t1 t2)
in (match (_45_2914) with
| (m, o) -> begin
(match (((m), (o))) with
| (MisMatch, _45_2917) -> begin
(

let head1 = (let _142_1403 = (FStar_Absyn_Util.head_and_args t1)
in (FStar_All.pipe_right _142_1403 Prims.fst))
in (

let head2 = (let _142_1404 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _142_1404 Prims.fst))
in (

let may_equate = (fun head -> (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_45_2924) -> begin
true
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Tc_Env.is_projector env tc.FStar_Absyn_Syntax.v)
end
| _45_2929 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _142_1410 = (let _142_1409 = (let _142_1408 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _142_1407 -> Some (_142_1407)) _142_1408))
in (solve_prob orig _142_1409 [] wl))
in (solve env _142_1410))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_45_2931, Some (t1, t2)) -> begin
(solve_t env (

let _45_2937 = problem
in {lhs = t1; relation = _45_2937.relation; rhs = t2; element = _45_2937.element; logical_guard = _45_2937.logical_guard; scope = _45_2937.scope; reason = _45_2937.reason; loc = _45_2937.loc; rank = _45_2937.rank}) wl)
end
| (_45_2940, None) -> begin
(

let _45_2943 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1412 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1411 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Head matches: %s and %s\n" _142_1412 _142_1411)))
end else begin
()
end
in (

let _45_2947 = (FStar_Absyn_Util.head_and_args t1)
in (match (_45_2947) with
| (head, args) -> begin
(

let _45_2950 = (FStar_Absyn_Util.head_and_args t2)
in (match (_45_2950) with
| (head', args') -> begin
(

let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _142_1417 = (let _142_1416 = (FStar_Absyn_Print.typ_to_string head)
in (let _142_1415 = (FStar_Absyn_Print.args_to_string args)
in (let _142_1414 = (FStar_Absyn_Print.typ_to_string head')
in (let _142_1413 = (FStar_Absyn_Print.args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _142_1416 _142_1415 _142_1414 _142_1413)))))
in (giveup env _142_1417 orig))
end else begin
if ((nargs = (Prims.parse_int "0")) || (eq_args args args')) then begin
(let _142_1418 = (solve_prob orig None [] wl)
in (solve env _142_1418))
end else begin
(

let _45_2954 = (base_and_refinement env wl t1)
in (match (_45_2954) with
| (base1, refinement1) -> begin
(

let _45_2957 = (base_and_refinement env wl t2)
in (match (_45_2957) with
| (base2, refinement2) -> begin
(match (((refinement1), (refinement2))) with
| (None, None) -> begin
(

let _45_2961 = if ((head_matches head head) <> FullMatch) then begin
(let _142_1421 = (let _142_1420 = (FStar_Absyn_Print.typ_to_string head)
in (let _142_1419 = (FStar_Absyn_Print.typ_to_string head')
in (FStar_Util.format2 "Assertion failed: expected full match of %s and %s\n" _142_1420 _142_1419)))
in (FStar_All.failwith _142_1421))
end else begin
()
end
in (

let subprobs = (FStar_List.map2 (fun a a' -> (match ((((Prims.fst a)), ((Prims.fst a')))) with
| (FStar_Util.Inl (t), FStar_Util.Inl (t')) -> begin
(let _142_1425 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (FStar_All.pipe_left (fun _142_1424 -> TProb (_142_1424)) _142_1425))
end
| (FStar_Util.Inr (v), FStar_Util.Inr (v')) -> begin
(let _142_1427 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (FStar_All.pipe_left (fun _142_1426 -> EProb (_142_1426)) _142_1427))
end
| _45_2976 -> begin
(FStar_All.failwith "Impossible")
end)) args args')
in (

let formula = (let _142_1429 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Absyn_Util.mk_conj_l _142_1429))
in (

let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _45_2982 -> begin
(

let lhs = (force_refinement ((base1), (refinement1)))
in (

let rhs = (force_refinement ((base2), (refinement2)))
in (solve_t env (

let _45_2985 = problem
in {lhs = lhs; relation = _45_2985.relation; rhs = rhs; element = _45_2985.element; logical_guard = _45_2985.logical_guard; scope = _45_2985.scope; reason = _45_2985.reason; loc = _45_2985.loc; rank = _45_2985.rank}) wl)))
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
| _45_3024 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (

let c1 = problem.lhs
in (

let c2 = problem.rhs
in (

let orig = CProb (problem)
in (

let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (

let solve_eq = (fun c1_comp c2_comp -> (

let _45_3041 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (

let sub_probs = (FStar_List.map2 (fun arg1 arg2 -> (match ((((Prims.fst arg1)), ((Prims.fst arg2)))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _142_1444 = (sub_prob t1 EQ t2 "effect arg")
in (FStar_All.pipe_left (fun _142_1443 -> TProb (_142_1443)) _142_1444))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _142_1446 = (sub_prob e1 EQ e2 "effect arg")
in (FStar_All.pipe_left (fun _142_1445 -> EProb (_142_1445)) _142_1446))
end
| _45_3056 -> begin
(FStar_All.failwith "impossible")
end)) c1_comp.FStar_Absyn_Syntax.effect_args c2_comp.FStar_Absyn_Syntax.effect_args)
in (

let guard = (let _142_1448 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _142_1448))
in (

let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _142_1449 = (solve_prob orig None [] wl)
in (solve env _142_1449))
end else begin
(

let _45_3061 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1451 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _142_1450 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _142_1451 (rel_to_string problem.relation) _142_1450)))
end else begin
()
end
in (

let r = (FStar_Tc_Env.get_range env)
in (

let _45_3066 = ((c1), (c2))
in (match (_45_3066) with
| (c1_0, c2_0) -> begin
(match (((c1.FStar_Absyn_Syntax.n), (c2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Total (t1), FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (FStar_Absyn_Syntax.Total (_45_3073), FStar_Absyn_Syntax.Comp (_45_3076)) -> begin
(let _142_1453 = (

let _45_3079 = problem
in (let _142_1452 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _142_1452; relation = _45_3079.relation; rhs = _45_3079.rhs; element = _45_3079.element; logical_guard = _45_3079.logical_guard; scope = _45_3079.scope; reason = _45_3079.reason; loc = _45_3079.loc; rank = _45_3079.rank}))
in (solve_c env _142_1453 wl))
end
| (FStar_Absyn_Syntax.Comp (_45_3082), FStar_Absyn_Syntax.Total (_45_3085)) -> begin
(let _142_1455 = (

let _45_3088 = problem
in (let _142_1454 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _45_3088.lhs; relation = _45_3088.relation; rhs = _142_1454; element = _45_3088.element; logical_guard = _45_3088.logical_guard; scope = _45_3088.scope; reason = _45_3088.reason; loc = _45_3088.loc; rank = _45_3088.rank}))
in (solve_c env _142_1455 wl))
end
| (FStar_Absyn_Syntax.Comp (_45_3091), FStar_Absyn_Syntax.Comp (_45_3094)) -> begin
if (((FStar_Absyn_Util.is_ml_comp c1) && (FStar_Absyn_Util.is_ml_comp c2)) || ((FStar_Absyn_Util.is_total_comp c1) && ((FStar_Absyn_Util.is_total_comp c2) || (FStar_Absyn_Util.is_ml_comp c2)))) then begin
(solve_t env (problem_using_guard orig (FStar_Absyn_Util.comp_result c1) problem.relation (FStar_Absyn_Util.comp_result c2) None "result type") wl)
end else begin
(

let c1_comp = (FStar_Absyn_Util.comp_to_comp_typ c1)
in (

let c2_comp = (FStar_Absyn_Util.comp_to_comp_typ c2)
in if ((problem.relation = EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Absyn_Syntax.effect_name c2_comp.FStar_Absyn_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(

let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (

let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (

let _45_3101 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Absyn_Syntax.effect_name.FStar_Ident.str c2.FStar_Absyn_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_Tc_Env.monad_leq env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _142_1458 = (let _142_1457 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _142_1456 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _142_1457 _142_1456)))
in (giveup env _142_1458 orig))
end
| Some (edge) -> begin
if (problem.relation = EQ) then begin
(

let _45_3121 = (match (c1.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (wp1), _45_3114))::((FStar_Util.Inl (wlp1), _45_3109))::[] -> begin
((wp1), (wlp1))
end
| _45_3118 -> begin
(let _142_1461 = (let _142_1460 = (let _142_1459 = (FStar_Absyn_Syntax.range_of_lid c1.FStar_Absyn_Syntax.effect_name)
in (FStar_Range.string_of_range _142_1459))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _142_1460))
in (FStar_All.failwith _142_1461))
end)
in (match (_45_3121) with
| (wp, wlp) -> begin
(

let c1 = (let _142_1467 = (let _142_1466 = (let _142_1462 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _142_1462))
in (let _142_1465 = (let _142_1464 = (let _142_1463 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _142_1463))
in (_142_1464)::[])
in (_142_1466)::_142_1465))
in {FStar_Absyn_Syntax.effect_name = c2.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _142_1467; FStar_Absyn_Syntax.flags = c1.FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(

let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _45_33 -> (match (_45_33) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.MLEFFECT) | (FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _45_3128 -> begin
false
end))))
in (

let _45_3151 = (match (((c1.FStar_Absyn_Syntax.effect_args), (c2.FStar_Absyn_Syntax.effect_args))) with
| (((FStar_Util.Inl (wp1), _45_3135))::_45_3131, ((FStar_Util.Inl (wp2), _45_3143))::_45_3139) -> begin
((wp1), (wp2))
end
| _45_3148 -> begin
(let _142_1471 = (let _142_1470 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _142_1469 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _142_1470 _142_1469)))
in (FStar_All.failwith _142_1471))
end)
in (match (_45_3151) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(solve_t env (problem_using_guard orig c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ None "result type") wl)
end else begin
(

let c2_decl = (FStar_Tc_Env.get_effect_decl env c2.FStar_Absyn_Syntax.effect_name)
in (

let g = if is_null_wp_2 then begin
(

let _45_3153 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _142_1477 = (let _142_1476 = (let _142_1475 = (FStar_Absyn_Syntax.targ c1.FStar_Absyn_Syntax.result_typ)
in (let _142_1474 = (let _142_1473 = (let _142_1472 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_1472))
in (_142_1473)::[])
in (_142_1475)::_142_1474))
in ((c2_decl.FStar_Absyn_Syntax.trivial), (_142_1476)))
in (FStar_Absyn_Syntax.mk_Typ_app _142_1477 (Some (FStar_Absyn_Syntax.ktype)) r)))
end else begin
(

let wp2_imp_wp1 = (let _142_1489 = (let _142_1488 = (let _142_1487 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _142_1486 = (let _142_1485 = (FStar_Absyn_Syntax.targ wpc2)
in (let _142_1484 = (let _142_1483 = (let _142_1479 = (let _142_1478 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.imp_lid _142_1478))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_1479))
in (let _142_1482 = (let _142_1481 = (let _142_1480 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_1480))
in (_142_1481)::[])
in (_142_1483)::_142_1482))
in (_142_1485)::_142_1484))
in (_142_1487)::_142_1486))
in ((c2_decl.FStar_Absyn_Syntax.wp_binop), (_142_1488)))
in (FStar_Absyn_Syntax.mk_Typ_app _142_1489 None r))
in (let _142_1494 = (let _142_1493 = (let _142_1492 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _142_1491 = (let _142_1490 = (FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_142_1490)::[])
in (_142_1492)::_142_1491))
in ((c2_decl.FStar_Absyn_Syntax.wp_as_type), (_142_1493)))
in (FStar_Absyn_Syntax.mk_Typ_app _142_1494 (Some (FStar_Absyn_Syntax.ktype)) r)))
end
in (

let base_prob = (let _142_1496 = (sub_prob c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _142_1495 -> TProb (_142_1495)) _142_1496))
in (

let wl = (let _142_1500 = (let _142_1499 = (let _142_1498 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _142_1498 g))
in (FStar_All.pipe_left (fun _142_1497 -> Some (_142_1497)) _142_1499))
in (solve_prob orig _142_1500 [] wl))
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
| _45_3165 -> begin
(FStar_All.failwith "Impossible")
end))
and solve_e' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (

let problem = (

let _45_3169 = problem
in {lhs = _45_3169.lhs; relation = EQ; rhs = _45_3169.rhs; element = _45_3169.element; logical_guard = _45_3169.logical_guard; scope = _45_3169.scope; reason = _45_3169.reason; loc = _45_3169.loc; rank = _45_3169.rank})
in (

let e1 = problem.lhs
in (

let e2 = problem.rhs
in (

let orig = EProb (problem)
in (

let sub_prob = (fun lhs rhs reason -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (

let _45_3181 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1510 = (prob_to_string env orig)
in (FStar_Util.print1 "Attempting:\n%s\n" _142_1510))
end else begin
()
end
in (

let flex_rigid = (fun _45_3188 e2 -> (match (_45_3188) with
| (e1, u1, t1, args1) -> begin
(

let maybe_vars1 = (pat_vars env [] args1)
in (

let sub_problems = (fun xs args2 -> (

let _45_3215 = (let _142_1526 = (FStar_All.pipe_right args2 (FStar_List.map (fun _45_34 -> (match (_45_34) with
| (FStar_Util.Inl (t), imp) -> begin
(

let kk = (FStar_Tc_Recheck.recompute_kind t)
in (

let _45_3202 = (new_tvar t.FStar_Absyn_Syntax.pos xs kk)
in (match (_45_3202) with
| (gi_xi, gi) -> begin
(

let gi_pi = (FStar_Absyn_Syntax.mk_Typ_app' ((gi), (args1)) (Some (kk)) t.FStar_Absyn_Syntax.pos)
in (let _142_1522 = (let _142_1521 = (sub_prob gi_pi t "type index")
in (FStar_All.pipe_left (fun _142_1520 -> TProb (_142_1520)) _142_1521))
in ((((FStar_Util.Inl (gi_xi)), (imp))), (_142_1522))))
end)))
end
| (FStar_Util.Inr (v), imp) -> begin
(

let tt = (FStar_Tc_Recheck.recompute_typ v)
in (

let _45_3211 = (new_evar v.FStar_Absyn_Syntax.pos xs tt)
in (match (_45_3211) with
| (gi_xi, gi) -> begin
(

let gi_pi = (FStar_Absyn_Syntax.mk_Exp_app' ((gi), (args1)) (Some (tt)) v.FStar_Absyn_Syntax.pos)
in (let _142_1525 = (let _142_1524 = (sub_prob gi_pi v "expression index")
in (FStar_All.pipe_left (fun _142_1523 -> EProb (_142_1523)) _142_1524))
in ((((FStar_Util.Inr (gi_xi)), (imp))), (_142_1525))))
end)))
end))))
in (FStar_All.pipe_right _142_1526 FStar_List.unzip))
in (match (_45_3215) with
| (gi_xi, gi_pi) -> begin
(

let formula = (let _142_1528 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) gi_pi)
in (FStar_Absyn_Util.mk_conj_l _142_1528))
in ((gi_xi), (gi_pi), (formula)))
end)))
in (

let project_e = (fun head2 args2 -> (

let giveup = (fun reason -> (let _142_1535 = (FStar_Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _142_1535 orig)))
in (match ((let _142_1536 = (FStar_Absyn_Util.compress_exp head2)
in _142_1536.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(

let _45_3232 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
(([]), (t1))
end
| Some (xs, c) -> begin
((xs), ((FStar_Absyn_Util.comp_result c)))
end)
in (match (_45_3232) with
| (all_xs, tres) -> begin
if ((FStar_List.length all_xs) <> (FStar_List.length args1)) then begin
(let _142_1539 = (let _142_1538 = (FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _142_1537 = (FStar_Absyn_Print.args_to_string args2)
in (FStar_Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _142_1538 _142_1537)))
in (giveup _142_1539))
end else begin
(

let rec aux = (fun xs args -> (match (((xs), (args))) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(FStar_All.failwith "impossible")
end
| (((FStar_Util.Inl (_45_3249), _45_3252))::xs, ((FStar_Util.Inl (_45_3257), _45_3260))::args) -> begin
(aux xs args)
end
| (((FStar_Util.Inr (xi), _45_3268))::xs, ((FStar_Util.Inr (arg), _45_3275))::args) -> begin
(match ((let _142_1544 = (FStar_Absyn_Util.compress_exp arg)
in _142_1544.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (z) -> begin
if (FStar_Absyn_Util.bvar_eq y z) then begin
(

let _45_3284 = (sub_problems all_xs args2)
in (match (_45_3284) with
| (gi_xi, gi_pi, f) -> begin
(

let sol = (let _142_1548 = (let _142_1547 = (let _142_1546 = (let _142_1545 = (FStar_Absyn_Util.bvar_to_exp xi)
in ((_142_1545), (gi_xi)))
in (FStar_Absyn_Syntax.mk_Exp_app' _142_1546 None e1.FStar_Absyn_Syntax.pos))
in ((all_xs), (_142_1547)))
in (FStar_Absyn_Syntax.mk_Exp_abs _142_1548 None e1.FStar_Absyn_Syntax.pos))
in (

let _45_3286 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1552 = (FStar_Absyn_Print.uvar_e_to_string ((u1), (t1)))
in (let _142_1551 = (FStar_Absyn_Print.exp_to_string sol)
in (let _142_1550 = (let _142_1549 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _142_1549 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Projected: %s -> %s\nSubprobs=\n%s\n" _142_1552 _142_1551 _142_1550))))
end else begin
()
end
in (let _142_1554 = (let _142_1553 = (solve_prob orig (Some (f)) ((UE (((((u1), (t1))), (sol))))::[]) wl)
in (attempt gi_pi _142_1553))
in (solve env _142_1554))))
end))
end else begin
(aux xs args)
end
end
| _45_3289 -> begin
(aux xs args)
end)
end
| ((x)::xs, (arg)::args) -> begin
(let _142_1557 = (let _142_1556 = (FStar_Absyn_Print.binder_to_string x)
in (let _142_1555 = (FStar_Absyn_Print.arg_to_string arg)
in (FStar_Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _142_1556 _142_1555)))
in (giveup _142_1557))
end))
in (aux (FStar_List.rev all_xs) (FStar_List.rev args1)))
end
end))
end
| _45_3298 -> begin
(giveup "rigid head term is not a variable")
end)))
in (

let imitate_or_project_e = (fun _45_3300 -> (match (()) with
| () -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end else begin
(

let _45_3301 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1561 = (FStar_Absyn_Print.exp_to_string e1)
in (let _142_1560 = (FStar_Absyn_Print.exp_to_string e2)
in (FStar_Util.print2 "Imitating expressions: %s =?= %s\n" _142_1561 _142_1560)))
end else begin
()
end
in (

let _45_3305 = (FStar_Absyn_Util.head_and_args_e e2)
in (match (_45_3305) with
| (head2, args2) -> begin
(

let fvhead = (FStar_Absyn_Util.freevars_exp head2)
in (

let _45_3310 = (occurs_check_e env ((u1), (t1)) head2)
in (match (_45_3310) with
| (occurs_ok, _45_3309) -> begin
if ((FStar_Absyn_Util.fvs_included fvhead FStar_Absyn_Syntax.no_fvs) && occurs_ok) then begin
(

let _45_3318 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
(([]), (t1))
end
| Some (xs, c) -> begin
((xs), ((FStar_Absyn_Util.comp_result c)))
end)
in (match (_45_3318) with
| (xs, tres) -> begin
(

let _45_3322 = (sub_problems xs args2)
in (match (_45_3322) with
| (gi_xi, gi_pi, f) -> begin
(

let sol = (

let body = (FStar_Absyn_Syntax.mk_Exp_app' ((head2), (gi_xi)) None e1.FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _45_3326 -> begin
(let _142_1563 = (let _142_1562 = (FStar_Absyn_Syntax.mk_Exp_app' ((head2), (gi_xi)) None e1.FStar_Absyn_Syntax.pos)
in ((xs), (_142_1562)))
in (FStar_Absyn_Syntax.mk_Exp_abs _142_1563 None e1.FStar_Absyn_Syntax.pos))
end))
in (

let _45_3328 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1567 = (FStar_Absyn_Print.uvar_e_to_string ((u1), (t1)))
in (let _142_1566 = (FStar_Absyn_Print.exp_to_string sol)
in (let _142_1565 = (let _142_1564 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _142_1564 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _142_1567 _142_1566 _142_1565))))
end else begin
()
end
in (let _142_1569 = (let _142_1568 = (solve_prob orig (Some (f)) ((UE (((((u1), (t1))), (sol))))::[]) wl)
in (attempt gi_pi _142_1568))
in (solve env _142_1569))))
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
(

let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (

let fvs2 = (FStar_Absyn_Util.freevars_exp e2)
in (

let _45_3340 = (occurs_check_e env ((u1), (t1)) e2)
in (match (_45_3340) with
| (occurs_ok, _45_3339) -> begin
if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && occurs_ok) then begin
(

let sol = (FStar_Absyn_Syntax.mk_Exp_abs' ((xs), (e2)) None e1.FStar_Absyn_Syntax.pos)
in (let _142_1570 = (solve_prob orig None ((UE (((((u1), (t1))), (sol))))::[]) wl)
in (solve env _142_1570)))
end else begin
(imitate_or_project_e ())
end
end))))
end)))))
end))
in (

let flex_flex = (fun _45_3347 _45_3352 -> (match (((_45_3347), (_45_3352))) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(

let maybe_vars1 = (pat_vars env [] args1)
in (

let maybe_vars2 = (pat_vars env [] args2)
in (match (((maybe_vars1), (maybe_vars2))) with
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
(

let zs = (intersect_vars xs ys)
in (

let tt = (FStar_Tc_Recheck.recompute_typ e2)
in (

let _45_3373 = (let _142_1575 = (FStar_Tc_Env.get_range env)
in (new_evar _142_1575 zs tt))
in (match (_45_3373) with
| (u, _45_3372) -> begin
(

let sub1 = (match (xs) with
| [] -> begin
u
end
| _45_3376 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs ((xs), (u)) (Some (t1)) e1.FStar_Absyn_Syntax.pos)
end)
in (

let sub2 = (match (ys) with
| [] -> begin
u
end
| _45_3380 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs ((ys), (u)) (Some (t2)) e1.FStar_Absyn_Syntax.pos)
end)
in (let _142_1576 = (solve_prob orig None ((UE (((((u1), (t1))), (sub1))))::(UE (((((u2), (t2))), (sub2))))::[]) wl)
in (solve env _142_1576))))
end))))
end
end)))
end))
in (

let smt_fallback = (fun e1 e2 -> if wl.smt_ok then begin
(

let _45_3385 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1581 = (prob_to_string env orig)
in (FStar_Util.print1 "Using SMT to solve:\n%s\n" _142_1581))
end else begin
()
end
in (

let _45_3390 = (let _142_1583 = (FStar_Tc_Env.get_range env)
in (let _142_1582 = (FStar_Tc_Env.binders env)
in (new_tvar _142_1583 _142_1582 FStar_Absyn_Syntax.ktype)))
in (match (_45_3390) with
| (t, _45_3389) -> begin
(let _142_1587 = (let _142_1586 = (let _142_1585 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _142_1584 -> Some (_142_1584)) _142_1585))
in (solve_prob orig _142_1586 [] wl))
in (solve env _142_1587))
end)))
end else begin
(giveup env "no SMT solution permitted" orig)
end)
in (match (((e1.FStar_Absyn_Syntax.n), (e2.FStar_Absyn_Syntax.n))) with
| (FStar_Absyn_Syntax.Exp_ascribed (e1, _45_3393, _45_3395), _45_3399) -> begin
(solve_e env (

let _45_3401 = problem
in {lhs = e1; relation = _45_3401.relation; rhs = _45_3401.rhs; element = _45_3401.element; logical_guard = _45_3401.logical_guard; scope = _45_3401.scope; reason = _45_3401.reason; loc = _45_3401.loc; rank = _45_3401.rank}) wl)
end
| (_45_3404, FStar_Absyn_Syntax.Exp_ascribed (e2, _45_3407, _45_3409)) -> begin
(solve_e env (

let _45_3413 = problem
in {lhs = _45_3413.lhs; relation = _45_3413.relation; rhs = e2; element = _45_3413.element; logical_guard = _45_3413.logical_guard; scope = _45_3413.scope; reason = _45_3413.reason; loc = _45_3413.loc; rank = _45_3413.rank}) wl)
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _142_1589 = (destruct_flex_e e1)
in (let _142_1588 = (destruct_flex_e e2)
in (flex_flex _142_1589 _142_1588)))
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(let _142_1590 = (destruct_flex_e e1)
in (flex_rigid _142_1590 e2))
end
| ((_, FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _142_1591 = (destruct_flex_e e2)
in (flex_rigid _142_1591 e1))
end
| (FStar_Absyn_Syntax.Exp_bvar (x1), FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
if (FStar_Absyn_Util.bvd_eq x1.FStar_Absyn_Syntax.v x1'.FStar_Absyn_Syntax.v) then begin
(let _142_1592 = (solve_prob orig None [] wl)
in (solve env _142_1592))
end else begin
(let _142_1598 = (let _142_1597 = (let _142_1596 = (let _142_1595 = (FStar_Tc_Recheck.recompute_typ e1)
in (let _142_1594 = (FStar_Tc_Recheck.recompute_typ e2)
in (FStar_Absyn_Util.mk_eq _142_1595 _142_1594 e1 e2)))
in (FStar_All.pipe_left (fun _142_1593 -> Some (_142_1593)) _142_1596))
in (solve_prob orig _142_1597 [] wl))
in (solve env _142_1598))
end
end
| (FStar_Absyn_Syntax.Exp_fvar (fv1, _45_3552), FStar_Absyn_Syntax.Exp_fvar (fv1', _45_3557)) -> begin
if (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv1'.FStar_Absyn_Syntax.v) then begin
(let _142_1599 = (solve_prob orig None [] wl)
in (solve env _142_1599))
end else begin
(giveup env "free-variables unequal" orig)
end
end
| (FStar_Absyn_Syntax.Exp_constant (s1), FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(

let const_eq = (fun s1 s2 -> (match (((s1), (s2))) with
| (FStar_Const.Const_bytearray (b1, _45_3571), FStar_Const.Const_bytearray (b2, _45_3576)) -> begin
(b1 = b2)
end
| (FStar_Const.Const_string (b1, _45_3582), FStar_Const.Const_string (b2, _45_3587)) -> begin
(b1 = b2)
end
| _45_3592 -> begin
(s1 = s2)
end))
in if (const_eq s1 s1') then begin
(let _142_1604 = (solve_prob orig None [] wl)
in (solve env _142_1604))
end else begin
(giveup env "constants unequal" orig)
end)
end
| (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_45_3602); FStar_Absyn_Syntax.tk = _45_3600; FStar_Absyn_Syntax.pos = _45_3598; FStar_Absyn_Syntax.fvs = _45_3596; FStar_Absyn_Syntax.uvs = _45_3594}, _45_3606), _45_3610) -> begin
(let _142_1606 = (

let _45_3612 = problem
in (let _142_1605 = (whnf_e env e1)
in {lhs = _142_1605; relation = _45_3612.relation; rhs = _45_3612.rhs; element = _45_3612.element; logical_guard = _45_3612.logical_guard; scope = _45_3612.scope; reason = _45_3612.reason; loc = _45_3612.loc; rank = _45_3612.rank}))
in (solve_e env _142_1606 wl))
end
| (_45_3615, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_45_3625); FStar_Absyn_Syntax.tk = _45_3623; FStar_Absyn_Syntax.pos = _45_3621; FStar_Absyn_Syntax.fvs = _45_3619; FStar_Absyn_Syntax.uvs = _45_3617}, _45_3629)) -> begin
(let _142_1608 = (

let _45_3633 = problem
in (let _142_1607 = (whnf_e env e2)
in {lhs = _45_3633.lhs; relation = _45_3633.relation; rhs = _142_1607; element = _45_3633.element; logical_guard = _45_3633.logical_guard; scope = _45_3633.scope; reason = _45_3633.reason; loc = _45_3633.loc; rank = _45_3633.rank}))
in (solve_e env _142_1608 wl))
end
| (FStar_Absyn_Syntax.Exp_app (head1, args1), FStar_Absyn_Syntax.Exp_app (head2, args2)) -> begin
(

let orig_wl = wl
in (

let rec solve_args = (fun sub_probs wl args1 args2 -> (match (((args1), (args2))) with
| ([], []) -> begin
(

let guard = (let _142_1618 = (let _142_1617 = (FStar_List.map p_guard sub_probs)
in (FStar_All.pipe_right _142_1617 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Util.mk_conj_l _142_1618))
in (

let g = (simplify_formula env guard)
in (

let g = (FStar_Absyn_Util.compress_typ g)
in (match (g.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
(let _142_1619 = (solve_prob orig None wl.subst (

let _45_3658 = orig_wl
in {attempting = _45_3658.attempting; wl_deferred = _45_3658.wl_deferred; subst = []; ctr = _45_3658.ctr; slack_vars = _45_3658.slack_vars; defer_ok = _45_3658.defer_ok; smt_ok = _45_3658.smt_ok; tcenv = _45_3658.tcenv}))
in (solve env _142_1619))
end
| _45_3661 -> begin
(

let _45_3665 = (let _142_1621 = (FStar_Tc_Env.get_range env)
in (let _142_1620 = (FStar_Tc_Env.binders env)
in (new_tvar _142_1621 _142_1620 FStar_Absyn_Syntax.ktype)))
in (match (_45_3665) with
| (t, _45_3664) -> begin
(

let guard = (let _142_1622 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_Absyn_Util.mk_disj g _142_1622))
in (let _142_1623 = (solve_prob orig (Some (guard)) wl.subst (

let _45_3667 = orig_wl
in {attempting = _45_3667.attempting; wl_deferred = _45_3667.wl_deferred; subst = []; ctr = _45_3667.ctr; slack_vars = _45_3667.slack_vars; defer_ok = _45_3667.defer_ok; smt_ok = _45_3667.smt_ok; tcenv = _45_3667.tcenv}))
in (solve env _142_1623)))
end))
end))))
end
| ((arg1)::rest1, (arg2)::rest2) -> begin
(

let prob = (match ((((Prims.fst arg1)), ((Prims.fst arg2)))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _142_1625 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (FStar_All.pipe_left (fun _142_1624 -> TProb (_142_1624)) _142_1625))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _142_1627 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (FStar_All.pipe_left (fun _142_1626 -> EProb (_142_1626)) _142_1627))
end
| _45_3687 -> begin
(FStar_All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (

let _45_3689 = wl
in {attempting = (prob)::[]; wl_deferred = []; subst = _45_3689.subst; ctr = _45_3689.ctr; slack_vars = _45_3689.slack_vars; defer_ok = false; smt_ok = false; tcenv = _45_3689.tcenv}))) with
| Failed (_45_3692) -> begin
(smt_fallback e1 e2)
end
| Success (subst, _45_3696) -> begin
(solve_args ((prob)::sub_probs) (

let _45_3699 = wl
in {attempting = _45_3699.attempting; wl_deferred = _45_3699.wl_deferred; subst = subst; ctr = _45_3699.ctr; slack_vars = _45_3699.slack_vars; defer_ok = _45_3699.defer_ok; smt_ok = _45_3699.smt_ok; tcenv = _45_3699.tcenv}) rest1 rest2)
end))
end
| _45_3702 -> begin
(FStar_All.failwith "Impossible: lengths defer")
end))
in (

let rec match_head_and_args = (fun head1 head2 -> (match ((let _142_1635 = (let _142_1632 = (FStar_Absyn_Util.compress_exp head1)
in _142_1632.FStar_Absyn_Syntax.n)
in (let _142_1634 = (let _142_1633 = (FStar_Absyn_Util.compress_exp head2)
in _142_1633.FStar_Absyn_Syntax.n)
in ((_142_1635), (_142_1634))))) with
| (FStar_Absyn_Syntax.Exp_bvar (x), FStar_Absyn_Syntax.Exp_bvar (y)) when ((FStar_Absyn_Util.bvar_eq x y) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _45_3713), FStar_Absyn_Syntax.Exp_fvar (g, _45_3718)) when (((FStar_Absyn_Util.fvar_eq f g) && (not ((FStar_Absyn_Util.is_interpreted f.FStar_Absyn_Syntax.v)))) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_ascribed (e, _45_3724, _45_3726), _45_3730) -> begin
(match_head_and_args e head2)
end
| (_45_3733, FStar_Absyn_Syntax.Exp_ascribed (e, _45_3736, _45_3738)) -> begin
(match_head_and_args head1 e)
end
| (FStar_Absyn_Syntax.Exp_abs (_45_3743), _45_3746) -> begin
(let _142_1637 = (

let _45_3748 = problem
in (let _142_1636 = (whnf_e env e1)
in {lhs = _142_1636; relation = _45_3748.relation; rhs = _45_3748.rhs; element = _45_3748.element; logical_guard = _45_3748.logical_guard; scope = _45_3748.scope; reason = _45_3748.reason; loc = _45_3748.loc; rank = _45_3748.rank}))
in (solve_e env _142_1637 wl))
end
| (_45_3751, FStar_Absyn_Syntax.Exp_abs (_45_3753)) -> begin
(let _142_1639 = (

let _45_3756 = problem
in (let _142_1638 = (whnf_e env e2)
in {lhs = _45_3756.lhs; relation = _45_3756.relation; rhs = _142_1638; element = _45_3756.element; logical_guard = _45_3756.logical_guard; scope = _45_3756.scope; reason = _45_3756.reason; loc = _45_3756.loc; rank = _45_3756.rank}))
in (solve_e env _142_1639 wl))
end
| _45_3759 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _45_3761 -> begin
(

let _45_3765 = (let _142_1641 = (FStar_Tc_Env.get_range env)
in (let _142_1640 = (FStar_Tc_Env.binders env)
in (new_tvar _142_1641 _142_1640 FStar_Absyn_Syntax.ktype)))
in (match (_45_3765) with
| (t, _45_3764) -> begin
(

let guard = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (

let _45_3767 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1642 = (FStar_Absyn_Print.typ_to_string guard)
in (FStar_Util.print1 "Emitting guard %s\n" _142_1642))
end else begin
()
end
in (let _142_1646 = (let _142_1645 = (let _142_1644 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _142_1643 -> Some (_142_1643)) _142_1644))
in (solve_prob orig _142_1645 [] wl))
in (solve env _142_1646))))
end))
end)))))))))))


let guard_to_string : FStar_Tc_Env.env  ->  guard_t  ->  Prims.string = (fun env g -> (

let form = (match (g.guard_f) with
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
in (

let carry = (let _142_1652 = (FStar_List.map (fun _45_3778 -> (match (_45_3778) with
| (_45_3776, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (FStar_All.pipe_right _142_1652 (FStar_String.concat ",\n")))
in (FStar_Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))


let guard_of_guard_formula : guard_formula  ->  guard_t = (fun g -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})


let guard_form : guard_t  ->  guard_formula = (fun g -> g.guard_f)


let is_trivial : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _45_3784} -> begin
true
end
| _45_3791 -> begin
false
end))


let trivial_guard : guard_t = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}


let abstract_guard : FStar_Absyn_Syntax.bvvar  ->  guard_t Prims.option  ->  guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(

let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _45_3807 -> begin
(FStar_All.failwith "impossible")
end)
in (let _142_1669 = (

let _45_3809 = g
in (let _142_1668 = (let _142_1667 = (let _142_1666 = (let _142_1665 = (let _142_1664 = (FStar_Absyn_Syntax.v_binder x)
in (_142_1664)::[])
in ((_142_1665), (f)))
in (FStar_Absyn_Syntax.mk_Typ_lam _142_1666 None f.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (fun _142_1663 -> NonTrivial (_142_1663)) _142_1667))
in {guard_f = _142_1668; deferred = _45_3809.deferred; implicits = _45_3809.implicits}))
in Some (_142_1669)))
end))


let apply_guard : guard_t  ->  FStar_Absyn_Syntax.exp  ->  guard_t = (fun g e -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(

let _45_3816 = g
in (let _142_1681 = (let _142_1680 = (let _142_1679 = (let _142_1678 = (let _142_1677 = (let _142_1676 = (FStar_Absyn_Syntax.varg e)
in (_142_1676)::[])
in ((f), (_142_1677)))
in (FStar_Absyn_Syntax.mk_Typ_app _142_1678))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn f.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _142_1679))
in NonTrivial (_142_1680))
in {guard_f = _142_1681; deferred = _45_3816.deferred; implicits = _45_3816.implicits}))
end))


let trivial : guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_45_3821) -> begin
(FStar_All.failwith "impossible")
end))


let conj_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _142_1688 = (FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_142_1688))
end))


let check_trivial : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  guard_formula = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _45_3839 -> begin
NonTrivial (t)
end))


let imp_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match (((g1), (g2))) with
| (Trivial, g) -> begin
g
end
| (g, Trivial) -> begin
Trivial
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(

let imp = (FStar_Absyn_Util.mk_imp f1 f2)
in (check_trivial imp))
end))


let binop_guard : (guard_formula  ->  guard_formula  ->  guard_formula)  ->  guard_t  ->  guard_t  ->  guard_t = (fun f g1 g2 -> (let _142_1711 = (f g1.guard_f g2.guard_f)
in {guard_f = _142_1711; deferred = {carry = (FStar_List.append g1.deferred.carry g2.deferred.carry); slack = (FStar_List.append g1.deferred.slack g2.deferred.slack)}; implicits = (FStar_List.append g1.implicits g2.implicits)}))


let conj_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))


let imp_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))


let close_guard : FStar_Absyn_Syntax.binders  ->  guard_t  ->  guard_t = (fun binders g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(

let _45_3866 = g
in (let _142_1726 = (let _142_1725 = (FStar_Absyn_Util.close_forall binders f)
in (FStar_All.pipe_right _142_1725 (fun _142_1724 -> NonTrivial (_142_1724))))
in {guard_f = _142_1726; deferred = _45_3866.deferred; implicits = _45_3866.implicits}))
end))


let mk_guard = (fun g ps slack locs -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})


let new_t_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _142_1738 = (FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _142_1737 = (FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _142_1738 (rel_to_string rel) _142_1737)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let new_t_prob : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  rel  ->  FStar_Absyn_Syntax.typ  ->  (prob * ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) = (fun env t1 rel t2 -> (

let x = (let _142_1747 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.gen_bvar_p _142_1747 t1))
in (

let env = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var (((x.FStar_Absyn_Syntax.v), (x.FStar_Absyn_Syntax.sort)))))
in (

let p = (let _142_1751 = (let _142_1749 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left (fun _142_1748 -> Some (_142_1748)) _142_1749))
in (let _142_1750 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _142_1751 _142_1750)))
in ((TProb (p)), (x))))))


let new_k_problem = (fun env lhs rel rhs elt loc -> (

let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _142_1759 = (FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _142_1758 = (FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _142_1759 (rel_to_string rel) _142_1758)))
end else begin
"TOP"
end
in (

let p = (new_problem env lhs rel rhs elt loc reason)
in p)))


let simplify_guard : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(

let _45_3900 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _142_1764 = (FStar_Absyn_Print.typ_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _142_1764))
end else begin
()
end
in (

let f = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f)
in (

let f = (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _45_3906 -> begin
NonTrivial (f)
end)
in (

let _45_3908 = g
in {guard_f = f; deferred = _45_3908.deferred; implicits = _45_3908.implicits}))))
end))


let solve_and_commit : FStar_Tc_Env.env  ->  worklist  ->  ((prob * Prims.string)  ->  deferred Prims.option)  ->  deferred Prims.option = (fun env probs err -> (

let probs = if (FStar_Options.eager_inference ()) then begin
(

let _45_3913 = probs
in {attempting = _45_3913.attempting; wl_deferred = _45_3913.wl_deferred; subst = _45_3913.subst; ctr = _45_3913.ctr; slack_vars = _45_3913.slack_vars; defer_ok = false; smt_ok = _45_3913.smt_ok; tcenv = _45_3913.tcenv})
end else begin
probs
end
in (

let sol = (solve env probs)
in (match (sol) with
| Success (s, deferred) -> begin
(

let _45_3921 = (commit env s)
in Some (deferred))
end
| Failed (d, s) -> begin
(

let _45_3927 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _142_1776 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _142_1776))
end else begin
()
end
in (err ((d), (s))))
end))))


let with_guard : FStar_Tc_Env.env  ->  prob  ->  deferred Prims.option  ->  guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _142_1788 = (let _142_1787 = (let _142_1786 = (let _142_1785 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _142_1785 (fun _142_1784 -> NonTrivial (_142_1784))))
in {guard_f = _142_1786; deferred = d; implicits = []})
in (simplify_guard env _142_1787))
in (FStar_All.pipe_left (fun _142_1783 -> Some (_142_1783)) _142_1788))
end))


let try_keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t Prims.option = (fun env k1 k2 -> (

let _45_3938 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1796 = (FStar_Absyn_Print.kind_to_string k1)
in (let _142_1795 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print2 "try_keq of %s and %s\n" _142_1796 _142_1795)))
end else begin
()
end
in (

let prob = (let _142_1801 = (let _142_1800 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _142_1799 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _142_1798 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _142_1800 EQ _142_1799 None _142_1798))))
in (FStar_All.pipe_left (fun _142_1797 -> KProb (_142_1797)) _142_1801))
in (let _142_1803 = (solve_and_commit env (singleton env prob) (fun _45_3941 -> None))
in (FStar_All.pipe_left (with_guard env prob) _142_1803)))))


let keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env t k1 k2 -> (match ((try_keq env k1 k2)) with
| None -> begin
(

let r = (match (t) with
| None -> begin
(FStar_Tc_Env.get_range env)
end
| Some (t) -> begin
t.FStar_Absyn_Syntax.pos
end)
in (match (t) with
| None -> begin
(let _142_1814 = (let _142_1813 = (let _142_1812 = (FStar_Tc_Errors.incompatible_kinds env k2 k1)
in ((_142_1812), (r)))
in FStar_Absyn_Syntax.Error (_142_1813))
in (Prims.raise _142_1814))
end
| Some (t) -> begin
(let _142_1817 = (let _142_1816 = (let _142_1815 = (FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in ((_142_1815), (r)))
in FStar_Absyn_Syntax.Error (_142_1816))
in (Prims.raise _142_1817))
end))
end
| Some (g) -> begin
g
end))


let subkind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env k1 k2 -> (

let _45_3960 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1827 = (let _142_1824 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _142_1824))
in (let _142_1826 = (FStar_Absyn_Print.kind_to_string k1)
in (let _142_1825 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print3 "(%s) subkind of %s and %s\n" _142_1827 _142_1826 _142_1825))))
end else begin
()
end
in (

let prob = (let _142_1832 = (let _142_1831 = (whnf_k env k1)
in (let _142_1830 = (whnf_k env k2)
in (let _142_1829 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _142_1831 SUB _142_1830 None _142_1829))))
in (FStar_All.pipe_left (fun _142_1828 -> KProb (_142_1828)) _142_1832))
in (

let res = (let _142_1839 = (let _142_1838 = (solve_and_commit env (singleton env prob) (fun _45_3963 -> (let _142_1837 = (let _142_1836 = (let _142_1835 = (FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _142_1834 = (FStar_Tc_Env.get_range env)
in ((_142_1835), (_142_1834))))
in FStar_Absyn_Syntax.Error (_142_1836))
in (Prims.raise _142_1837))))
in (FStar_All.pipe_left (with_guard env prob) _142_1838))
in (FStar_Util.must _142_1839))
in res))))


let try_teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (

let _45_3969 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1847 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1846 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _142_1847 _142_1846)))
end else begin
()
end
in (

let prob = (let _142_1850 = (let _142_1849 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _142_1849))
in (FStar_All.pipe_left (fun _142_1848 -> TProb (_142_1848)) _142_1850))
in (

let g = (let _142_1852 = (solve_and_commit env (singleton env prob) (fun _45_3972 -> None))
in (FStar_All.pipe_left (with_guard env prob) _142_1852))
in g))))


let teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _142_1862 = (let _142_1861 = (let _142_1860 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _142_1859 = (FStar_Tc_Env.get_range env)
in ((_142_1860), (_142_1859))))
in FStar_Absyn_Syntax.Error (_142_1861))
in (Prims.raise _142_1862))
end
| Some (g) -> begin
(

let _45_3981 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1865 = (FStar_Absyn_Print.typ_to_string t1)
in (let _142_1864 = (FStar_Absyn_Print.typ_to_string t2)
in (let _142_1863 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _142_1865 _142_1864 _142_1863))))
end else begin
()
end
in g)
end))


let try_subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (

let kopt = (fun _45_35 -> (match (_45_35) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.kind_to_string t)
end))
in (

let k = (fun t1 -> (match ((let _142_1876 = (FStar_Absyn_Util.compress_typ t1)
in _142_1876.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (x) -> begin
(let _142_1880 = (FStar_Absyn_Print.kind_to_string x.FStar_Absyn_Syntax.sort)
in (let _142_1879 = (let _142_1878 = (let _142_1877 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _142_1877))
in (Prims.strcat " ... " _142_1878))
in (Prims.strcat _142_1880 _142_1879)))
end
| _45_3996 -> begin
(let _142_1881 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _142_1881))
end))
in (

let _45_3997 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1885 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _142_1884 = (k t1)
in (let _142_1883 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _142_1882 = (k t2)
in (FStar_Util.print4 "try_subtype of %s : %s and %s : %s\n" _142_1885 _142_1884 _142_1883 _142_1882)))))
end else begin
()
end
in (

let _45_4001 = (new_t_prob env t1 SUB t2)
in (match (_45_4001) with
| (prob, x) -> begin
(

let g = (let _142_1887 = (solve_and_commit env (singleton env prob) (fun _45_4002 -> None))
in (FStar_All.pipe_left (with_guard env prob) _142_1887))
in (

let _45_4005 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _142_1891 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _142_1890 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _142_1889 = (let _142_1888 = (FStar_Util.must g)
in (guard_to_string env _142_1888))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _142_1891 _142_1890 _142_1889))))
end else begin
()
end
in (abstract_guard x g)))
end))))))


let subtype_fail = (fun env t1 t2 -> (let _142_1898 = (let _142_1897 = (let _142_1896 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _142_1895 = (FStar_Tc_Env.get_range env)
in ((_142_1896), (_142_1895))))
in FStar_Absyn_Syntax.Error (_142_1897))
in (Prims.raise _142_1898)))


let subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))


let sub_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  guard_t Prims.option = (fun env c1 c2 -> (

let _45_4019 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1912 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _142_1911 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _142_1912 _142_1911)))
end else begin
()
end
in (

let rel = if env.FStar_Tc_Env.use_eq then begin
EQ
end else begin
SUB
end
in (

let prob = (let _142_1915 = (let _142_1914 = (FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _142_1914 "sub_comp"))
in (FStar_All.pipe_left (fun _142_1913 -> CProb (_142_1913)) _142_1915))
in (let _142_1917 = (solve_and_commit env (singleton env prob) (fun _45_4023 -> None))
in (FStar_All.pipe_left (with_guard env prob) _142_1917))))))


let solve_deferred_constraints : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (

let fail = (fun _45_4030 -> (match (_45_4030) with
| (d, s) -> begin
(

let msg = (explain env d s)
in (Prims.raise (FStar_Absyn_Syntax.Error (((msg), ((p_loc d)))))))
end))
in (

let _45_4035 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && ((FStar_List.length g.deferred.carry) <> (Prims.parse_int "0"))) then begin
(let _142_1930 = (let _142_1929 = (FStar_All.pipe_right g.deferred.carry (FStar_List.map (fun _45_4034 -> (match (_45_4034) with
| (msg, x) -> begin
(let _142_1928 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc x))
in (let _142_1927 = (prob_to_string env x)
in (let _142_1926 = (let _142_1925 = (FStar_All.pipe_right (p_guard x) Prims.fst)
in (FStar_Tc_Normalize.formula_norm_to_string env _142_1925))
in (FStar_Util.format4 "(At %s) %s\n%s\nguard is %s\n" _142_1928 msg _142_1927 _142_1926))))
end))))
in (FStar_All.pipe_right _142_1929 (FStar_String.concat "\n")))
in (FStar_All.pipe_left (FStar_Util.print1 "Trying to solve carried problems: begin\n%s\nend\n") _142_1930))
end else begin
()
end
in (

let gopt = (let _142_1931 = (wl_of_guard env g.deferred)
in (solve_and_commit env _142_1931 fail))
in (match (gopt) with
| Some ({carry = _45_4040; slack = slack}) -> begin
(

let _45_4043 = (fix_slack_vars slack)
in (

let _45_4045 = g
in {guard_f = _45_4045.guard_f; deferred = no_deferred; implicits = _45_4045.implicits}))
end
| _45_4048 -> begin
(FStar_All.failwith "impossible")
end)))))


let try_discharge_guard : FStar_Tc_Env.env  ->  guard_t  ->  Prims.unit = (fun env g -> (

let g = (solve_deferred_constraints env g)
in if (not ((FStar_Options.should_verify env.FStar_Tc_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.guard_f) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(

let vc = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(

let _45_4059 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _142_1938 = (FStar_Tc_Env.get_range env)
in (let _142_1937 = (let _142_1936 = (FStar_Absyn_Print.formula_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _142_1936))
in (FStar_Tc_Errors.diag _142_1938 _142_1937)))
end else begin
()
end
in (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env vc))
end))
end)
end))





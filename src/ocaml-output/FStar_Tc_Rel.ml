
open Prims
# 34 "FStar.Tc.Rel.fst"
type rel =
| EQ
| SUB
| SUBINV

# 40 "FStar.Tc.Rel.fst"
let is_EQ = (fun _discr_ -> (match (_discr_) with
| EQ (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "FStar.Tc.Rel.fst"
let is_SUB = (fun _discr_ -> (match (_discr_) with
| SUB (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Tc.Rel.fst"
let is_SUBINV = (fun _discr_ -> (match (_discr_) with
| SUBINV (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.Tc.Rel.fst"
type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

# 45 "FStar.Tc.Rel.fst"
let is_COVARIANT = (fun _discr_ -> (match (_discr_) with
| COVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Tc.Rel.fst"
let is_CONTRAVARIANT = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Tc.Rel.fst"
let is_INVARIANT = (fun _discr_ -> (match (_discr_) with
| INVARIANT (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Tc.Rel.fst"
type ('a, 'b) problem =
{lhs : 'a; relation : rel; rhs : 'a; element : 'b Prims.option; logical_guard : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); scope : FStar_Absyn_Syntax.binders; reason : Prims.string Prims.list; loc : FStar_Range.range; rank : Prims.int Prims.option}

# 49 "FStar.Tc.Rel.fst"
let is_Mkproblem = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkproblem"))))

# 59 "FStar.Tc.Rel.fst"
type ('a, 'b) problem_t =
('a, 'b) problem

# 60 "FStar.Tc.Rel.fst"
type prob =
| KProb of (FStar_Absyn_Syntax.knd, Prims.unit) problem
| TProb of (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem
| EProb of (FStar_Absyn_Syntax.exp, Prims.unit) problem
| CProb of (FStar_Absyn_Syntax.comp, Prims.unit) problem

# 63 "FStar.Tc.Rel.fst"
let is_KProb = (fun _discr_ -> (match (_discr_) with
| KProb (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.Tc.Rel.fst"
let is_TProb = (fun _discr_ -> (match (_discr_) with
| TProb (_) -> begin
true
end
| _ -> begin
false
end))

# 65 "FStar.Tc.Rel.fst"
let is_EProb = (fun _discr_ -> (match (_discr_) with
| EProb (_) -> begin
true
end
| _ -> begin
false
end))

# 66 "FStar.Tc.Rel.fst"
let is_CProb = (fun _discr_ -> (match (_discr_) with
| CProb (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.Tc.Rel.fst"
let ___KProb____0 = (fun projectee -> (match (projectee) with
| KProb (_44_52) -> begin
_44_52
end))

# 64 "FStar.Tc.Rel.fst"
let ___TProb____0 = (fun projectee -> (match (projectee) with
| TProb (_44_55) -> begin
_44_55
end))

# 65 "FStar.Tc.Rel.fst"
let ___EProb____0 = (fun projectee -> (match (projectee) with
| EProb (_44_58) -> begin
_44_58
end))

# 66 "FStar.Tc.Rel.fst"
let ___CProb____0 = (fun projectee -> (match (projectee) with
| CProb (_44_61) -> begin
_44_61
end))

# 66 "FStar.Tc.Rel.fst"
type probs =
prob Prims.list

# 68 "FStar.Tc.Rel.fst"
type uvi =
| UK of (FStar_Absyn_Syntax.uvar_k * FStar_Absyn_Syntax.knd)
| UT of ((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.typ)
| UE of ((FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.exp)

# 72 "FStar.Tc.Rel.fst"
let is_UK = (fun _discr_ -> (match (_discr_) with
| UK (_) -> begin
true
end
| _ -> begin
false
end))

# 73 "FStar.Tc.Rel.fst"
let is_UT = (fun _discr_ -> (match (_discr_) with
| UT (_) -> begin
true
end
| _ -> begin
false
end))

# 74 "FStar.Tc.Rel.fst"
let is_UE = (fun _discr_ -> (match (_discr_) with
| UE (_) -> begin
true
end
| _ -> begin
false
end))

# 72 "FStar.Tc.Rel.fst"
let ___UK____0 = (fun projectee -> (match (projectee) with
| UK (_44_64) -> begin
_44_64
end))

# 73 "FStar.Tc.Rel.fst"
let ___UT____0 = (fun projectee -> (match (projectee) with
| UT (_44_67) -> begin
_44_67
end))

# 74 "FStar.Tc.Rel.fst"
let ___UE____0 = (fun projectee -> (match (projectee) with
| UE (_44_70) -> begin
_44_70
end))

# 74 "FStar.Tc.Rel.fst"
type worklist =
{attempting : probs; wl_deferred : (Prims.int * Prims.string * prob) Prims.list; subst : uvi Prims.list; ctr : Prims.int; slack_vars : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_Tc_Env.env}

# 77 "FStar.Tc.Rel.fst"
let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

# 86 "FStar.Tc.Rel.fst"
type deferred =
{carry : (Prims.string * prob) Prims.list; slack : (Prims.bool * FStar_Absyn_Syntax.typ) Prims.list}

# 89 "FStar.Tc.Rel.fst"
let is_Mkdeferred : deferred  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkdeferred"))))

# 92 "FStar.Tc.Rel.fst"
let no_deferred : deferred = {carry = []; slack = []}

# 96 "FStar.Tc.Rel.fst"
type solution =
| Success of (uvi Prims.list * deferred)
| Failed of (prob * Prims.string)

# 98 "FStar.Tc.Rel.fst"
let is_Success = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

# 99 "FStar.Tc.Rel.fst"
let is_Failed = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

# 98 "FStar.Tc.Rel.fst"
let ___Success____0 = (fun projectee -> (match (projectee) with
| Success (_44_85) -> begin
_44_85
end))

# 99 "FStar.Tc.Rel.fst"
let ___Failed____0 = (fun projectee -> (match (projectee) with
| Failed (_44_88) -> begin
_44_88
end))

# 99 "FStar.Tc.Rel.fst"
type guard_formula =
| Trivial
| NonTrivial of FStar_Absyn_Syntax.formula

# 102 "FStar.Tc.Rel.fst"
let is_Trivial = (fun _discr_ -> (match (_discr_) with
| Trivial (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.Tc.Rel.fst"
let is_NonTrivial = (fun _discr_ -> (match (_discr_) with
| NonTrivial (_) -> begin
true
end
| _ -> begin
false
end))

# 103 "FStar.Tc.Rel.fst"
let ___NonTrivial____0 = (fun projectee -> (match (projectee) with
| NonTrivial (_44_91) -> begin
_44_91
end))

# 103 "FStar.Tc.Rel.fst"
type implicits =
((FStar_Absyn_Syntax.uvar_t * FStar_Range.range), (FStar_Absyn_Syntax.uvar_e * FStar_Range.range)) FStar_Util.either Prims.list

# 105 "FStar.Tc.Rel.fst"
type guard_t =
{guard_f : guard_formula; deferred : deferred; implicits : implicits}

# 106 "FStar.Tc.Rel.fst"
let is_Mkguard_t : guard_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkguard_t"))))

# 140 "FStar.Tc.Rel.fst"
let new_kvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  (FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.uvar_k) = (fun r binders -> (
# 146 "FStar.Tc.Rel.fst"
let u = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (let _133_226 = (let _133_225 = (let _133_224 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (u, _133_224))
in (FStar_Absyn_Syntax.mk_Kind_uvar _133_225 r))
in (_133_226, u))))

# 147 "FStar.Tc.Rel.fst"
let new_tvar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun r binders k -> (
# 150 "FStar.Tc.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _133_234 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _133_234 Prims.op_Negation)))))
in (
# 151 "FStar.Tc.Rel.fst"
let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(
# 154 "FStar.Tc.Rel.fst"
let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k) None r)
in (uv, uv))
end
| _44_109 -> begin
(
# 157 "FStar.Tc.Rel.fst"
let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (
# 158 "FStar.Tc.Rel.fst"
let k' = (FStar_Absyn_Syntax.mk_Kind_arrow (binders, k) r)
in (
# 159 "FStar.Tc.Rel.fst"
let uv = (FStar_Absyn_Syntax.mk_Typ_uvar' (uv, k') None r)
in (let _133_235 = (FStar_Absyn_Syntax.mk_Typ_app (uv, args) None r)
in (_133_235, uv)))))
end))))

# 160 "FStar.Tc.Rel.fst"
let new_evar : FStar_Range.range  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.exp) = (fun r binders t -> (
# 163 "FStar.Tc.Rel.fst"
let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _133_243 = (FStar_Absyn_Syntax.is_null_binder x)
in (FStar_All.pipe_right _133_243 Prims.op_Negation)))))
in (
# 164 "FStar.Tc.Rel.fst"
let uv = (FStar_Unionfind.fresh FStar_Absyn_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(
# 167 "FStar.Tc.Rel.fst"
let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t) None r)
in (uv, uv))
end
| _44_122 -> begin
(
# 170 "FStar.Tc.Rel.fst"
let args = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (
# 171 "FStar.Tc.Rel.fst"
let t' = (let _133_245 = (let _133_244 = (FStar_Absyn_Syntax.mk_Total t)
in (binders, _133_244))
in (FStar_Absyn_Syntax.mk_Typ_fun _133_245 None r))
in (
# 172 "FStar.Tc.Rel.fst"
let uv = (FStar_Absyn_Syntax.mk_Exp_uvar' (uv, t') None r)
in (match (args) with
| [] -> begin
(uv, uv)
end
| _44_128 -> begin
(let _133_246 = (FStar_Absyn_Syntax.mk_Exp_app (uv, args) None r)
in (_133_246, uv))
end))))
end))))

# 175 "FStar.Tc.Rel.fst"
let rel_to_string : rel  ->  Prims.string = (fun _44_1 -> (match (_44_1) with
| EQ -> begin
"="
end
| SUB -> begin
"<:"
end
| SUBINV -> begin
":>"
end))

# 187 "FStar.Tc.Rel.fst"
let prob_to_string : FStar_Tc_Env.env  ->  prob  ->  Prims.string = (fun env _44_2 -> (match (_44_2) with
| KProb (p) -> begin
(let _133_254 = (FStar_Absyn_Print.kind_to_string p.lhs)
in (let _133_253 = (FStar_Absyn_Print.kind_to_string p.rhs)
in (FStar_Util.format3 "\t%s\n\t\t%s\n\t%s" _133_254 (rel_to_string p.relation) _133_253)))
end
| TProb (p) -> begin
(let _133_267 = (let _133_266 = (FStar_Tc_Normalize.typ_norm_to_string env p.lhs)
in (let _133_265 = (let _133_264 = (FStar_Absyn_Print.tag_of_typ p.lhs)
in (let _133_263 = (let _133_262 = (let _133_261 = (FStar_All.pipe_right p.reason FStar_List.hd)
in (let _133_260 = (let _133_259 = (FStar_Tc_Normalize.typ_norm_to_string env p.rhs)
in (let _133_258 = (let _133_257 = (FStar_Absyn_Print.tag_of_typ p.rhs)
in (let _133_256 = (let _133_255 = (FStar_Tc_Normalize.formula_norm_to_string env (Prims.fst p.logical_guard))
in (_133_255)::[])
in (_133_257)::_133_256))
in (_133_259)::_133_258))
in (_133_261)::_133_260))
in ((rel_to_string p.relation))::_133_262)
in (_133_264)::_133_263))
in (_133_266)::_133_265))
in (FStar_Util.format "\t%s (%s) \n\t\t%s(%s)\n\t%s (%s) (guard %s)" _133_267))
end
| EProb (p) -> begin
(let _133_269 = (FStar_Tc_Normalize.exp_norm_to_string env p.lhs)
in (let _133_268 = (FStar_Tc_Normalize.exp_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _133_269 (rel_to_string p.relation) _133_268)))
end
| CProb (p) -> begin
(let _133_271 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.lhs)
in (let _133_270 = (FStar_Tc_Normalize.comp_typ_norm_to_string env p.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _133_271 (rel_to_string p.relation) _133_270)))
end))

# 201 "FStar.Tc.Rel.fst"
let uvi_to_string : FStar_Tc_Env.env  ->  uvi  ->  Prims.string = (fun env uvi -> (
# 205 "FStar.Tc.Rel.fst"
let str = (fun u -> if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _133_277 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _133_277 FStar_Util.string_of_int))
end)
in (match (uvi) with
| UK (u, _44_150) -> begin
(let _133_278 = (str u)
in (FStar_All.pipe_right _133_278 (FStar_Util.format1 "UK %s")))
end
| UT ((u, _44_155), t) -> begin
(let _133_281 = (str u)
in (FStar_All.pipe_right _133_281 (fun x -> (let _133_280 = (FStar_Tc_Normalize.typ_norm_to_string env t)
in (FStar_Util.format2 "UT %s %s" x _133_280)))))
end
| UE ((u, _44_163), _44_166) -> begin
(let _133_282 = (str u)
in (FStar_All.pipe_right _133_282 (FStar_Util.format1 "UE %s")))
end)))

# 209 "FStar.Tc.Rel.fst"
let invert_rel : rel  ->  rel = (fun _44_3 -> (match (_44_3) with
| EQ -> begin
EQ
end
| SUB -> begin
SUBINV
end
| SUBINV -> begin
SUB
end))

# 221 "FStar.Tc.Rel.fst"
let invert = (fun p -> (
# 222 "FStar.Tc.Rel.fst"
let _44_174 = p
in {lhs = p.rhs; relation = (invert_rel p.relation); rhs = p.lhs; element = _44_174.element; logical_guard = _44_174.logical_guard; scope = _44_174.scope; reason = _44_174.reason; loc = _44_174.loc; rank = _44_174.rank}))

# 222 "FStar.Tc.Rel.fst"
let maybe_invert = (fun p -> if (p.relation = SUBINV) then begin
(invert p)
end else begin
p
end)

# 223 "FStar.Tc.Rel.fst"
let maybe_invert_p : prob  ->  prob = (fun _44_4 -> (match (_44_4) with
| KProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _133_289 -> KProb (_133_289)))
end
| TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _133_290 -> TProb (_133_290)))
end
| EProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _133_291 -> EProb (_133_291)))
end
| CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _133_292 -> CProb (_133_292)))
end))

# 228 "FStar.Tc.Rel.fst"
let vary_rel : rel  ->  variance  ->  rel = (fun rel _44_5 -> (match (_44_5) with
| INVARIANT -> begin
EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

# 232 "FStar.Tc.Rel.fst"
let p_rel : prob  ->  rel = (fun _44_6 -> (match (_44_6) with
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

# 237 "FStar.Tc.Rel.fst"
let p_reason : prob  ->  Prims.string Prims.list = (fun _44_7 -> (match (_44_7) with
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

# 242 "FStar.Tc.Rel.fst"
let p_loc : prob  ->  FStar_Range.range = (fun _44_8 -> (match (_44_8) with
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

# 247 "FStar.Tc.Rel.fst"
let p_context : prob  ->  FStar_Absyn_Syntax.binders = (fun _44_9 -> (match (_44_9) with
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

# 252 "FStar.Tc.Rel.fst"
let p_guard : prob  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) = (fun _44_10 -> (match (_44_10) with
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

# 257 "FStar.Tc.Rel.fst"
let p_scope : prob  ->  FStar_Absyn_Syntax.binders = (fun _44_11 -> (match (_44_11) with
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

# 262 "FStar.Tc.Rel.fst"
let p_invert : prob  ->  prob = (fun _44_12 -> (match (_44_12) with
| KProb (p) -> begin
(FStar_All.pipe_left (fun _133_311 -> KProb (_133_311)) (invert p))
end
| TProb (p) -> begin
(FStar_All.pipe_left (fun _133_312 -> TProb (_133_312)) (invert p))
end
| EProb (p) -> begin
(FStar_All.pipe_left (fun _133_313 -> EProb (_133_313)) (invert p))
end
| CProb (p) -> begin
(FStar_All.pipe_left (fun _133_314 -> CProb (_133_314)) (invert p))
end))

# 267 "FStar.Tc.Rel.fst"
let is_top_level_prob : prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

# 268 "FStar.Tc.Rel.fst"
let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _133_324 = (new_tvar (p_loc orig) scope FStar_Absyn_Syntax.ktype)
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _133_324; scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None}))

# 280 "FStar.Tc.Rel.fst"
let new_problem = (fun env lhs rel rhs elt loc reason -> (let _133_334 = (let _133_333 = (FStar_Tc_Env.get_range env)
in (let _133_332 = (FStar_Tc_Env.binders env)
in (new_tvar _133_333 _133_332 FStar_Absyn_Syntax.ktype)))
in {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = _133_334; scope = []; reason = (reason)::[]; loc = loc; rank = None}))

# 291 "FStar.Tc.Rel.fst"
let problem_using_guard = (fun orig lhs rel rhs elt reason -> {lhs = lhs; relation = rel; rhs = rhs; element = elt; logical_guard = (p_guard orig); scope = []; reason = (reason)::(p_reason orig); loc = (p_loc orig); rank = None})

# 302 "FStar.Tc.Rel.fst"
let guard_on_element = (fun problem x phi -> (match (problem.element) with
| None -> begin
(let _133_345 = (let _133_344 = (FStar_Absyn_Syntax.v_binder x)
in (_133_344)::[])
in (FStar_Absyn_Util.close_forall _133_345 phi))
end
| Some (e) -> begin
(FStar_Absyn_Util.subst_typ ((FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, e)))::[]) phi)
end))

# 306 "FStar.Tc.Rel.fst"
let solve_prob' : Prims.bool  ->  prob  ->  FStar_Absyn_Syntax.typ Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (
# 308 "FStar.Tc.Rel.fst"
let phi = (match (logical_guard) with
| None -> begin
FStar_Absyn_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (
# 311 "FStar.Tc.Rel.fst"
let _44_293 = (p_guard prob)
in (match (_44_293) with
| (_44_291, uv) -> begin
(
# 312 "FStar.Tc.Rel.fst"
let _44_301 = (match ((let _133_356 = (FStar_Absyn_Util.compress_typ uv)
in _133_356.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uvar, k) -> begin
(
# 314 "FStar.Tc.Rel.fst"
let phi = (FStar_Absyn_Util.close_for_kind phi k)
in (FStar_Absyn_Util.unchecked_unify uvar phi))
end
| _44_300 -> begin
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
| _44_305 -> begin
(
# 320 "FStar.Tc.Rel.fst"
let _44_306 = if (FStar_All.pipe_left (FStar_Tc_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _133_358 = (let _133_357 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _133_357 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Extending solution: %s\n" _133_358))
end else begin
()
end
in (
# 322 "FStar.Tc.Rel.fst"
let _44_308 = wl
in {attempting = _44_308.attempting; wl_deferred = _44_308.wl_deferred; subst = (FStar_List.append uvis wl.subst); ctr = (wl.ctr + 1); slack_vars = _44_308.slack_vars; defer_ok = _44_308.defer_ok; smt_ok = _44_308.smt_ok; tcenv = _44_308.tcenv}))
end))
end))))

# 322 "FStar.Tc.Rel.fst"
let extend_solution : uvi  ->  worklist  ->  worklist = (fun sol wl -> (
# 324 "FStar.Tc.Rel.fst"
let _44_312 = wl
in {attempting = _44_312.attempting; wl_deferred = _44_312.wl_deferred; subst = (sol)::wl.subst; ctr = (wl.ctr + 1); slack_vars = _44_312.slack_vars; defer_ok = _44_312.defer_ok; smt_ok = _44_312.smt_ok; tcenv = _44_312.tcenv}))

# 324 "FStar.Tc.Rel.fst"
let solve_prob : prob  ->  FStar_Absyn_Syntax.typ Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (solve_prob' false prob logical_guard uvis wl))

# 325 "FStar.Tc.Rel.fst"
let explain : FStar_Tc_Env.env  ->  prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _133_379 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _133_378 = (prob_to_string env d)
in (let _133_377 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _133_379 _133_378 _133_377 s)))))

# 331 "FStar.Tc.Rel.fst"
let empty_worklist : FStar_Tc_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; subst = []; ctr = 0; slack_vars = []; defer_ok = true; smt_ok = true; tcenv = env})

# 350 "FStar.Tc.Rel.fst"
let singleton : FStar_Tc_Env.env  ->  prob  ->  worklist = (fun env prob -> (
# 351 "FStar.Tc.Rel.fst"
let _44_324 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _44_324.wl_deferred; subst = _44_324.subst; ctr = _44_324.ctr; slack_vars = _44_324.slack_vars; defer_ok = _44_324.defer_ok; smt_ok = _44_324.smt_ok; tcenv = _44_324.tcenv}))

# 351 "FStar.Tc.Rel.fst"
let wl_of_guard : FStar_Tc_Env.env  ->  deferred  ->  worklist = (fun env g -> (
# 352 "FStar.Tc.Rel.fst"
let _44_328 = (empty_worklist env)
in (let _133_390 = (FStar_List.map Prims.snd g.carry)
in {attempting = _133_390; wl_deferred = _44_328.wl_deferred; subst = _44_328.subst; ctr = _44_328.ctr; slack_vars = g.slack; defer_ok = false; smt_ok = _44_328.smt_ok; tcenv = _44_328.tcenv})))

# 352 "FStar.Tc.Rel.fst"
let defer : Prims.string  ->  prob  ->  worklist  ->  worklist = (fun reason prob wl -> (
# 353 "FStar.Tc.Rel.fst"
let _44_333 = wl
in {attempting = _44_333.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; subst = _44_333.subst; ctr = _44_333.ctr; slack_vars = _44_333.slack_vars; defer_ok = _44_333.defer_ok; smt_ok = _44_333.smt_ok; tcenv = _44_333.tcenv}))

# 353 "FStar.Tc.Rel.fst"
let attempt : prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (
# 354 "FStar.Tc.Rel.fst"
let _44_337 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _44_337.wl_deferred; subst = _44_337.subst; ctr = _44_337.ctr; slack_vars = _44_337.slack_vars; defer_ok = _44_337.defer_ok; smt_ok = _44_337.smt_ok; tcenv = _44_337.tcenv}))

# 354 "FStar.Tc.Rel.fst"
let add_slack_mul : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (
# 355 "FStar.Tc.Rel.fst"
let _44_341 = wl
in {attempting = _44_341.attempting; wl_deferred = _44_341.wl_deferred; subst = _44_341.subst; ctr = _44_341.ctr; slack_vars = ((true, slack))::wl.slack_vars; defer_ok = _44_341.defer_ok; smt_ok = _44_341.smt_ok; tcenv = _44_341.tcenv}))

# 355 "FStar.Tc.Rel.fst"
let add_slack_add : FStar_Absyn_Syntax.typ  ->  worklist  ->  worklist = (fun slack wl -> (
# 356 "FStar.Tc.Rel.fst"
let _44_345 = wl
in {attempting = _44_345.attempting; wl_deferred = _44_345.wl_deferred; subst = _44_345.subst; ctr = _44_345.ctr; slack_vars = ((false, slack))::wl.slack_vars; defer_ok = _44_345.defer_ok; smt_ok = _44_345.smt_ok; tcenv = _44_345.tcenv}))

# 356 "FStar.Tc.Rel.fst"
let giveup : FStar_Tc_Env.env  ->  Prims.string  ->  prob  ->  solution = (fun env reason prob -> (
# 359 "FStar.Tc.Rel.fst"
let _44_350 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_415 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _133_415))
end else begin
()
end
in Failed ((prob, reason))))

# 361 "FStar.Tc.Rel.fst"
let commit = (fun env uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _44_13 -> (match (_44_13) with
| UK (u, k) -> begin
(FStar_Absyn_Util.unchecked_unify u k)
end
| UT ((u, k), t) -> begin
(FStar_Absyn_Util.unchecked_unify u t)
end
| UE ((u, _44_367), e) -> begin
(FStar_Absyn_Util.unchecked_unify u e)
end)))))

# 373 "FStar.Tc.Rel.fst"
let find_uvar_k : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.knd Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _44_14 -> (match (_44_14) with
| UK (u, t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _44_380 -> begin
None
end))))

# 375 "FStar.Tc.Rel.fst"
let find_uvar_t : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.typ Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _44_15 -> (match (_44_15) with
| UT ((u, _44_386), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _44_392 -> begin
None
end))))

# 376 "FStar.Tc.Rel.fst"
let find_uvar_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Absyn_Syntax.exp Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _44_16 -> (match (_44_16) with
| UE ((u, _44_398), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end
| _44_404 -> begin
None
end))))

# 377 "FStar.Tc.Rel.fst"
let simplify_formula : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env f -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f))

# 386 "FStar.Tc.Rel.fst"
let norm_targ : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env t))

# 387 "FStar.Tc.Rel.fst"
let norm_arg = (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _133_446 = (let _133_445 = (norm_targ env t)
in (FStar_All.pipe_left (fun _133_444 -> FStar_Util.Inl (_133_444)) _133_445))
in (_133_446, (Prims.snd a)))
end
| FStar_Util.Inr (v) -> begin
(let _133_449 = (let _133_448 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::[]) env v)
in (FStar_All.pipe_left (fun _133_447 -> FStar_Util.Inr (_133_447)) _133_448))
in (_133_449, (Prims.snd a)))
end))

# 390 "FStar.Tc.Rel.fst"
let whnf : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _133_454 = (FStar_Tc_Normalize.whnf env t)
in (FStar_All.pipe_right _133_454 FStar_Absyn_Util.compress_typ)))

# 391 "FStar.Tc.Rel.fst"
let sn : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> (let _133_459 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::[]) env t)
in (FStar_All.pipe_right _133_459 FStar_Absyn_Util.compress_typ)))

# 392 "FStar.Tc.Rel.fst"
let sn_binders = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _44_17 -> (match (_44_17) with
| (FStar_Util.Inl (a), imp) -> begin
(let _133_465 = (let _133_464 = (
# 396 "FStar.Tc.Rel.fst"
let _44_426 = a
in (let _133_463 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _44_426.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _133_463; FStar_Absyn_Syntax.p = _44_426.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_133_464))
in (_133_465, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _133_468 = (let _133_467 = (
# 398 "FStar.Tc.Rel.fst"
let _44_432 = x
in (let _133_466 = (norm_targ env x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _44_432.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _133_466; FStar_Absyn_Syntax.p = _44_432.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_133_467))
in (_133_468, imp))
end)))))

# 398 "FStar.Tc.Rel.fst"
let whnf_k : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env k -> (let _133_473 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env k)
in (FStar_All.pipe_right _133_473 FStar_Absyn_Util.compress_kind)))

# 399 "FStar.Tc.Rel.fst"
let whnf_e : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.exp  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env e -> (let _133_478 = (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.WHNF)::[]) env e)
in (FStar_All.pipe_right _133_478 FStar_Absyn_Util.compress_exp)))

# 400 "FStar.Tc.Rel.fst"
let rec compress_k : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun env wl k -> (
# 403 "FStar.Tc.Rel.fst"
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
# 411 "FStar.Tc.Rel.fst"
let k = (let _133_485 = (FStar_Absyn_Util.subst_of_list formals actuals)
in (FStar_Absyn_Util.subst_kind _133_485 body))
in (compress_k env wl k))
end
| _44_455 -> begin
if ((FStar_List.length actuals) = 0) then begin
(compress_k env wl k')
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end)
end
| _44_457 -> begin
k
end)))

# 416 "FStar.Tc.Rel.fst"
let rec compress : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl t -> (
# 419 "FStar.Tc.Rel.fst"
let t = (let _133_492 = (FStar_Absyn_Util.unmeta_typ t)
in (whnf env _133_492))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _44_464) -> begin
(match ((find_uvar_t uv wl.subst)) with
| None -> begin
t
end
| Some (t) -> begin
(compress env wl t)
end)
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, _44_480); FStar_Absyn_Syntax.tk = _44_477; FStar_Absyn_Syntax.pos = _44_475; FStar_Absyn_Syntax.fvs = _44_473; FStar_Absyn_Syntax.uvs = _44_471}, args) -> begin
(match ((find_uvar_t uv wl.subst)) with
| Some (t') -> begin
(
# 428 "FStar.Tc.Rel.fst"
let t = (FStar_Absyn_Syntax.mk_Typ_app (t', args) None t.FStar_Absyn_Syntax.pos)
in (compress env wl t))
end
| _44_491 -> begin
t
end)
end
| _44_493 -> begin
t
end)))

# 431 "FStar.Tc.Rel.fst"
let rec compress_e : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env wl e -> (
# 434 "FStar.Tc.Rel.fst"
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
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, _44_515); FStar_Absyn_Syntax.tk = _44_512; FStar_Absyn_Syntax.pos = _44_510; FStar_Absyn_Syntax.fvs = _44_508; FStar_Absyn_Syntax.uvs = _44_506}, args) -> begin
(match ((find_uvar_e uv wl.subst)) with
| None -> begin
e
end
| Some (e') -> begin
(
# 445 "FStar.Tc.Rel.fst"
let e' = (compress_e env wl e')
in (FStar_Absyn_Syntax.mk_Exp_app (e', args) None e.FStar_Absyn_Syntax.pos))
end)
end
| _44_527 -> begin
e
end)))

# 448 "FStar.Tc.Rel.fst"
let normalize_refinement : FStar_Tc_Normalize.steps  ->  FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun steps env wl t0 -> (let _133_507 = (compress env wl t0)
in (FStar_Tc_Normalize.normalize_refinement steps env _133_507)))

# 450 "FStar.Tc.Rel.fst"
let base_and_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.bvvar * FStar_Absyn_Syntax.typ) Prims.option) = (fun env wl t1 -> (
# 453 "FStar.Tc.Rel.fst"
let rec aux = (fun norm t1 -> (match (t1.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, phi) -> begin
if norm then begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, phi); FStar_Absyn_Syntax.tk = _44_549; FStar_Absyn_Syntax.pos = _44_547; FStar_Absyn_Syntax.fvs = _44_545; FStar_Absyn_Syntax.uvs = _44_543} -> begin
(x.FStar_Absyn_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _133_520 = (let _133_519 = (FStar_Absyn_Print.typ_to_string tt)
in (let _133_518 = (FStar_Absyn_Print.tag_of_typ tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _133_519 _133_518)))
in (FStar_All.failwith _133_520))
end)
end
end
| (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(
# 467 "FStar.Tc.Rel.fst"
let _44_564 = (let _133_521 = (normalize_refinement [] env wl t1)
in (aux true _133_521))
in (match (_44_564) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _44_567 -> begin
(t2', refinement)
end)
end))
end
end
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
(t1, None)
end
| (FStar_Absyn_Syntax.Typ_ascribed (_)) | (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_meta (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _133_524 = (let _133_523 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_522 = (FStar_Absyn_Print.tag_of_typ t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _133_523 _133_522)))
in (FStar_All.failwith _133_524))
end))
in (let _133_525 = (compress env wl t1)
in (aux false _133_525))))

# 482 "FStar.Tc.Rel.fst"
let unrefine : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (let _133_530 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _133_530 Prims.fst)))

# 484 "FStar.Tc.Rel.fst"
let trivial_refinement = (fun t -> (let _133_532 = (FStar_Absyn_Util.gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in (_133_532, FStar_Absyn_Util.t_true)))

# 486 "FStar.Tc.Rel.fst"
let as_refinement : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * FStar_Absyn_Syntax.typ) = (fun env wl t -> (
# 489 "FStar.Tc.Rel.fst"
let _44_598 = (base_and_refinement env wl t)
in (match (_44_598) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

# 494 "FStar.Tc.Rel.fst"
let force_refinement : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t * FStar_Absyn_Syntax.typ) Prims.option)  ->  FStar_Absyn_Syntax.typ = (fun _44_606 -> (match (_44_606) with
| (t_base, refopt) -> begin
(
# 497 "FStar.Tc.Rel.fst"
let _44_614 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_44_614) with
| (y, phi) -> begin
(FStar_Absyn_Syntax.mk_Typ_refine (y, phi) None t_base.FStar_Absyn_Syntax.pos)
end))
end))

# 500 "FStar.Tc.Rel.fst"
let rec occurs = (fun env wl uk t -> (
# 510 "FStar.Tc.Rel.fst"
let uvs = (FStar_Absyn_Util.uvars_in_typ t)
in (let _133_552 = (FStar_All.pipe_right uvs.FStar_Absyn_Syntax.uvars_t FStar_Util.set_elements)
in (FStar_All.pipe_right _133_552 (FStar_Util.for_some (fun _44_625 -> (match (_44_625) with
| (uvt, _44_624) -> begin
(match ((find_uvar_t uvt wl.subst)) with
| None -> begin
(FStar_Unionfind.equivalent uvt (Prims.fst uk))
end
| Some (t) -> begin
(
# 515 "FStar.Tc.Rel.fst"
let t = (match ((FStar_Absyn_Util.compress_typ t)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (_44_638, t); FStar_Absyn_Syntax.tk = _44_636; FStar_Absyn_Syntax.pos = _44_634; FStar_Absyn_Syntax.fvs = _44_632; FStar_Absyn_Syntax.uvs = _44_630} -> begin
t
end
| t -> begin
t
end)
in (occurs env wl uk t))
end)
end)))))))

# 518 "FStar.Tc.Rel.fst"
let occurs_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.string Prims.option) = (fun env wl uk t -> (
# 521 "FStar.Tc.Rel.fst"
let occurs_ok = (not ((occurs env wl uk t)))
in (
# 522 "FStar.Tc.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _133_565 = (let _133_564 = (FStar_Absyn_Print.uvar_t_to_string uk)
in (let _133_563 = (FStar_Absyn_Print.typ_to_string t)
in (let _133_562 = (let _133_561 = (FStar_All.pipe_right wl.subst (FStar_List.map (uvi_to_string env)))
in (FStar_All.pipe_right _133_561 (FStar_String.concat ", ")))
in (FStar_Util.format3 "occurs-check failed (%s occurs in %s) (with substitution %s)" _133_564 _133_563 _133_562))))
in Some (_133_565))
end
in (occurs_ok, msg))))

# 528 "FStar.Tc.Rel.fst"
let occurs_and_freevars_check : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd)  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.typ  ->  (Prims.bool * Prims.bool * (Prims.string Prims.option * FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.freevars)) = (fun env wl uk fvs t -> (
# 531 "FStar.Tc.Rel.fst"
let fvs_t = (FStar_Absyn_Util.freevars_typ t)
in (
# 532 "FStar.Tc.Rel.fst"
let _44_659 = (occurs_check env wl uk t)
in (match (_44_659) with
| (occurs_ok, msg) -> begin
(let _133_576 = (FStar_Absyn_Util.fvs_included fvs_t fvs)
in (occurs_ok, _133_576, (msg, fvs, fvs_t)))
end))))

# 533 "FStar.Tc.Rel.fst"
let occurs_check_e : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.uvar_e * FStar_Absyn_Syntax.typ)  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (Prims.bool * Prims.string Prims.option) = (fun env ut e -> (
# 536 "FStar.Tc.Rel.fst"
let uvs = (FStar_Absyn_Util.uvars_in_exp e)
in (
# 537 "FStar.Tc.Rel.fst"
let occurs_ok = (not ((FStar_Util.set_mem ut uvs.FStar_Absyn_Syntax.uvars_e)))
in (
# 538 "FStar.Tc.Rel.fst"
let msg = if occurs_ok then begin
None
end else begin
(let _133_588 = (let _133_587 = (FStar_Absyn_Print.uvar_e_to_string ut)
in (let _133_586 = (let _133_584 = (let _133_583 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _133_583 (FStar_List.map FStar_Absyn_Print.uvar_e_to_string)))
in (FStar_All.pipe_right _133_584 (FStar_String.concat ", ")))
in (let _133_585 = (FStar_Tc_Normalize.exp_norm_to_string env e)
in (FStar_Util.format3 "occurs-check failed (%s occurs in {%s} uvars of %s)" _133_587 _133_586 _133_585))))
in Some (_133_588))
end
in (occurs_ok, msg)))))

# 544 "FStar.Tc.Rel.fst"
let intersect_vars : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders = (fun v1 v2 -> (
# 548 "FStar.Tc.Rel.fst"
let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders v1)
in (
# 549 "FStar.Tc.Rel.fst"
let fvs2 = (FStar_Absyn_Syntax.freevars_of_binders v2)
in (let _133_595 = (let _133_594 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _133_593 = (FStar_Util.set_intersect fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _133_594; FStar_Absyn_Syntax.fxvs = _133_593}))
in (FStar_Absyn_Syntax.binders_of_freevars _133_595)))))

# 550 "FStar.Tc.Rel.fst"
let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun ax1 ax2 -> (match (((Prims.fst ax1), (Prims.fst ax2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Util.bvar_eq x y)
end
| _44_685 -> begin
false
end)) v1 v2)))

# 557 "FStar.Tc.Rel.fst"
let pat_var_opt = (fun env seen arg -> (
# 560 "FStar.Tc.Rel.fst"
let hd = (norm_arg env arg)
in (match ((FStar_All.pipe_left Prims.fst hd)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_btvar (a); FStar_Absyn_Syntax.tk = _44_697; FStar_Absyn_Syntax.pos = _44_695; FStar_Absyn_Syntax.fvs = _44_693; FStar_Absyn_Syntax.uvs = _44_691}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _44_18 -> (match (_44_18) with
| (FStar_Util.Inl (b), _44_706) -> begin
(FStar_Absyn_Syntax.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v)
end
| _44_709 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inl (a), (Prims.snd hd)))
end
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_bvar (x); FStar_Absyn_Syntax.tk = _44_717; FStar_Absyn_Syntax.pos = _44_715; FStar_Absyn_Syntax.fvs = _44_713; FStar_Absyn_Syntax.uvs = _44_711}) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _44_19 -> (match (_44_19) with
| (FStar_Util.Inr (y), _44_726) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _44_729 -> begin
false
end)))) then begin
None
end else begin
Some ((FStar_Util.Inr (x), (Prims.snd hd)))
end
end
| _44_731 -> begin
None
end)))

# 576 "FStar.Tc.Rel.fst"
let rec pat_vars : FStar_Tc_Env.env  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(
# 582 "FStar.Tc.Rel.fst"
let _44_740 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_611 = (FStar_Absyn_Print.arg_to_string hd)
in (FStar_Util.print1 "Not a pattern: %s\n" _133_611))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

# 584 "FStar.Tc.Rel.fst"
let destruct_flex_t = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (uv, k); FStar_Absyn_Syntax.tk = _44_756; FStar_Absyn_Syntax.pos = _44_754; FStar_Absyn_Syntax.fvs = _44_752; FStar_Absyn_Syntax.uvs = _44_750}, args) -> begin
(t, uv, k, args)
end
| _44_766 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 589 "FStar.Tc.Rel.fst"
let destruct_flex_e = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_uvar (uv, k) -> begin
(e, uv, k, [])
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (uv, k); FStar_Absyn_Syntax.tk = _44_779; FStar_Absyn_Syntax.pos = _44_777; FStar_Absyn_Syntax.fvs = _44_775; FStar_Absyn_Syntax.uvs = _44_773}, args) -> begin
(e, uv, k, args)
end
| _44_789 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

# 594 "FStar.Tc.Rel.fst"
let destruct_flex_pattern = (fun env t -> (
# 597 "FStar.Tc.Rel.fst"
let _44_796 = (destruct_flex_t t)
in (match (_44_796) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _44_800 -> begin
((t, uv, k, args), None)
end)
end)))

# 600 "FStar.Tc.Rel.fst"
type match_result =
| MisMatch
| HeadMatch
| FullMatch

# 658 "FStar.Tc.Rel.fst"
let is_MisMatch = (fun _discr_ -> (match (_discr_) with
| MisMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 659 "FStar.Tc.Rel.fst"
let is_HeadMatch = (fun _discr_ -> (match (_discr_) with
| HeadMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 660 "FStar.Tc.Rel.fst"
let is_FullMatch = (fun _discr_ -> (match (_discr_) with
| FullMatch (_) -> begin
true
end
| _ -> begin
false
end))

# 660 "FStar.Tc.Rel.fst"
let head_match : match_result  ->  match_result = (fun _44_20 -> (match (_44_20) with
| MisMatch -> begin
MisMatch
end
| _44_804 -> begin
HeadMatch
end))

# 664 "FStar.Tc.Rel.fst"
let rec head_matches : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  match_result = (fun t1 t2 -> (match ((let _133_628 = (let _133_625 = (FStar_Absyn_Util.unmeta_typ t1)
in _133_625.FStar_Absyn_Syntax.n)
in (let _133_627 = (let _133_626 = (FStar_Absyn_Util.unmeta_typ t2)
in _133_626.FStar_Absyn_Syntax.n)
in (_133_628, _133_627)))) with
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
| (FStar_Absyn_Syntax.Typ_refine (x, _44_833), FStar_Absyn_Syntax.Typ_refine (y, _44_838)) -> begin
(let _133_629 = (head_matches x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _133_629 head_match))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _44_844), _44_848) -> begin
(let _133_630 = (head_matches x.FStar_Absyn_Syntax.sort t2)
in (FStar_All.pipe_right _133_630 head_match))
end
| (_44_851, FStar_Absyn_Syntax.Typ_refine (x, _44_854)) -> begin
(let _133_631 = (head_matches t1 x.FStar_Absyn_Syntax.sort)
in (FStar_All.pipe_right _133_631 head_match))
end
| (FStar_Absyn_Syntax.Typ_fun (_44_859), FStar_Absyn_Syntax.Typ_fun (_44_862)) -> begin
HeadMatch
end
| (FStar_Absyn_Syntax.Typ_app (head, _44_867), FStar_Absyn_Syntax.Typ_app (head', _44_872)) -> begin
(head_matches head head')
end
| (FStar_Absyn_Syntax.Typ_app (head, _44_878), _44_882) -> begin
(head_matches head t2)
end
| (_44_885, FStar_Absyn_Syntax.Typ_app (head, _44_888)) -> begin
(head_matches t1 head)
end
| (FStar_Absyn_Syntax.Typ_uvar (uv, _44_894), FStar_Absyn_Syntax.Typ_uvar (uv', _44_899)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (_44_904, FStar_Absyn_Syntax.Typ_lam (_44_906)) -> begin
HeadMatch
end
| _44_910 -> begin
MisMatch
end))

# 689 "FStar.Tc.Rel.fst"
let head_matches_delta : FStar_Tc_Env.env  ->  worklist  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (match_result * ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.option) = (fun env wl t1 t2 -> (
# 693 "FStar.Tc.Rel.fst"
let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (
# 694 "FStar.Tc.Rel.fst"
let fail = (fun _44_921 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (
# 695 "FStar.Tc.Rel.fst"
let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 2) then begin
(fail ())
end else begin
if (d = 1) then begin
(
# 700 "FStar.Tc.Rel.fst"
let t1' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t1)
in (
# 701 "FStar.Tc.Rel.fst"
let t2' = (normalize_refinement ((FStar_Tc_Normalize.UnfoldOpaque)::[]) env wl t2)
in (aux 2 t1' t2')))
end else begin
(
# 703 "FStar.Tc.Rel.fst"
let t1 = (normalize_refinement [] env wl t1)
in (
# 704 "FStar.Tc.Rel.fst"
let t2 = (normalize_refinement [] env wl t2)
in (aux (d + 1) t1 t2)))
end
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux 0 t1 t2)))))

# 707 "FStar.Tc.Rel.fst"
let decompose_binder = (fun bs v_ktec rebuild_base -> (
# 711 "FStar.Tc.Rel.fst"
let fail = (fun _44_937 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 712 "FStar.Tc.Rel.fst"
let rebuild = (fun ktecs -> (
# 713 "FStar.Tc.Rel.fst"
let rec aux = (fun new_bs bs ktecs -> (match ((bs, ktecs)) with
| ([], ktec::[]) -> begin
(rebuild_base (FStar_List.rev new_bs) ktec)
end
| ((FStar_Util.Inl (a), imp)::rest, FStar_Absyn_Syntax.K (k)::rest') -> begin
(aux (((FStar_Util.Inl ((
# 715 "FStar.Tc.Rel.fst"
let _44_959 = a
in {FStar_Absyn_Syntax.v = _44_959.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _44_959.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| ((FStar_Util.Inr (x), imp)::rest, FStar_Absyn_Syntax.T (t, _44_970)::rest') -> begin
(aux (((FStar_Util.Inr ((
# 716 "FStar.Tc.Rel.fst"
let _44_975 = x
in {FStar_Absyn_Syntax.v = _44_975.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _44_975.FStar_Absyn_Syntax.p})), imp))::new_bs) rest rest')
end
| _44_978 -> begin
(fail ())
end))
in (aux [] bs ktecs)))
in (
# 720 "FStar.Tc.Rel.fst"
let rec mk_b_ktecs = (fun _44_982 _44_21 -> (match (_44_982) with
| (binders, b_ktecs) -> begin
(match (_44_21) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, v_ktec))::b_ktecs))
end
| hd::rest -> begin
(
# 723 "FStar.Tc.Rel.fst"
let bopt = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (
# 724 "FStar.Tc.Rel.fst"
let b_ktec = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(bopt, CONTRAVARIANT, FStar_Absyn_Syntax.K (a.FStar_Absyn_Syntax.sort))
end
| FStar_Util.Inr (x) -> begin
(bopt, CONTRAVARIANT, FStar_Absyn_Syntax.T ((x.FStar_Absyn_Syntax.sort, Some (FStar_Absyn_Syntax.ktype))))
end)
in (
# 727 "FStar.Tc.Rel.fst"
let binders' = (match (bopt) with
| None -> begin
binders
end
| Some (hd) -> begin
(FStar_List.append binders ((hd)::[]))
end)
in (mk_b_ktecs (binders', (b_ktec)::b_ktecs) rest))))
end)
end))
in (let _133_685 = (mk_b_ktecs ([], []) bs)
in (rebuild, _133_685))))))

# 730 "FStar.Tc.Rel.fst"
let rec decompose_kind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.knd) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list) = (fun env k -> (
# 733 "FStar.Tc.Rel.fst"
let fail = (fun _44_1001 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (
# 734 "FStar.Tc.Rel.fst"
let k0 = k
in (
# 735 "FStar.Tc.Rel.fst"
let k = (FStar_Absyn_Util.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(
# 739 "FStar.Tc.Rel.fst"
let rebuild = (fun _44_22 -> (match (_44_22) with
| [] -> begin
k
end
| _44_1009 -> begin
(fail ())
end))
in (rebuild, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(decompose_binder bs (FStar_Absyn_Syntax.K (k)) (fun bs _44_23 -> (match (_44_23) with
| FStar_Absyn_Syntax.K (k) -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow (bs, k) k0.FStar_Absyn_Syntax.pos)
end
| _44_1020 -> begin
(fail ())
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_44_1022, k) -> begin
(decompose_kind env k)
end
| _44_1027 -> begin
(FStar_All.failwith "Impossible")
end)))))

# 752 "FStar.Tc.Rel.fst"
let rec decompose_typ = (fun env t -> (
# 756 "FStar.Tc.Rel.fst"
let t = (FStar_Absyn_Util.unmeta_typ t)
in (
# 757 "FStar.Tc.Rel.fst"
let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (hd, args) -> begin
(
# 760 "FStar.Tc.Rel.fst"
let rebuild = (fun args' -> (
# 761 "FStar.Tc.Rel.fst"
let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((FStar_Util.Inl (_44_1042), imp), FStar_Absyn_Syntax.T (t, _44_1048)) -> begin
(FStar_Util.Inl (t), imp)
end
| ((FStar_Util.Inr (_44_1053), imp), FStar_Absyn_Syntax.E (e)) -> begin
(FStar_Util.Inr (e), imp)
end
| _44_1061 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Absyn_Syntax.mk_Typ_app (hd, args) None t.FStar_Absyn_Syntax.pos)))
in (
# 767 "FStar.Tc.Rel.fst"
let b_ktecs = (FStar_All.pipe_right args (FStar_List.map (fun _44_24 -> (match (_44_24) with
| (FStar_Util.Inl (t), _44_1067) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _44_1072) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (rebuild, matches, b_ktecs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(
# 773 "FStar.Tc.Rel.fst"
let _44_1087 = (decompose_binder bs (FStar_Absyn_Syntax.C (c)) (fun bs _44_25 -> (match (_44_25) with
| FStar_Absyn_Syntax.C (c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end
| _44_1084 -> begin
(FStar_All.failwith "Bad reconstruction")
end)))
in (match (_44_1087) with
| (rebuild, b_ktecs) -> begin
(rebuild, matches, b_ktecs)
end))
end
| _44_1089 -> begin
(
# 781 "FStar.Tc.Rel.fst"
let rebuild = (fun _44_26 -> (match (_44_26) with
| [] -> begin
t
end
| _44_1093 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

# 785 "FStar.Tc.Rel.fst"
let un_T : FStar_Absyn_Syntax.ktec  ->  FStar_Absyn_Syntax.typ = (fun _44_27 -> (match (_44_27) with
| FStar_Absyn_Syntax.T (x, _44_1099) -> begin
x
end
| _44_1103 -> begin
(FStar_All.failwith "impossible")
end))

# 789 "FStar.Tc.Rel.fst"
let arg_of_ktec : FStar_Absyn_Syntax.ktec  ->  FStar_Absyn_Syntax.arg = (fun _44_28 -> (match (_44_28) with
| FStar_Absyn_Syntax.T (t, _44_1107) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Absyn_Syntax.E (e) -> begin
(FStar_Absyn_Syntax.varg e)
end
| _44_1113 -> begin
(FStar_All.failwith "Impossible")
end))

# 793 "FStar.Tc.Rel.fst"
let imitation_sub_probs = (fun orig env scope ps qs -> (
# 800 "FStar.Tc.Rel.fst"
let r = (p_loc orig)
in (
# 801 "FStar.Tc.Rel.fst"
let rel = (p_rel orig)
in (
# 802 "FStar.Tc.Rel.fst"
let sub_prob = (fun scope args q -> (match (q) with
| (_44_1126, variance, FStar_Absyn_Syntax.K (ki)) -> begin
(
# 805 "FStar.Tc.Rel.fst"
let _44_1133 = (new_kvar r scope)
in (match (_44_1133) with
| (gi_xs, gi) -> begin
(
# 806 "FStar.Tc.Rel.fst"
let gi_ps = (FStar_Absyn_Syntax.mk_Kind_uvar (gi, args) r)
in (let _133_768 = (let _133_767 = (mk_problem scope orig gi_ps (vary_rel rel variance) ki None "kind subterm")
in (FStar_All.pipe_left (fun _133_766 -> KProb (_133_766)) _133_767))
in (FStar_Absyn_Syntax.K (gi_xs), _133_768)))
end))
end
| (_44_1136, variance, FStar_Absyn_Syntax.T (ti, kopt)) -> begin
(
# 811 "FStar.Tc.Rel.fst"
let k = (match (kopt) with
| Some (k) -> begin
k
end
| None -> begin
(FStar_Tc_Recheck.recompute_kind ti)
end)
in (
# 814 "FStar.Tc.Rel.fst"
let _44_1149 = (new_tvar r scope k)
in (match (_44_1149) with
| (gi_xs, gi) -> begin
(
# 815 "FStar.Tc.Rel.fst"
let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args) None r)
in (let _133_771 = (let _133_770 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _133_769 -> TProb (_133_769)) _133_770))
in (FStar_Absyn_Syntax.T ((gi_xs, Some (k))), _133_771)))
end)))
end
| (_44_1152, variance, FStar_Absyn_Syntax.E (ei)) -> begin
(
# 820 "FStar.Tc.Rel.fst"
let t = (FStar_Tc_Recheck.recompute_typ ei)
in (
# 821 "FStar.Tc.Rel.fst"
let _44_1160 = (new_evar r scope t)
in (match (_44_1160) with
| (gi_xs, gi) -> begin
(
# 822 "FStar.Tc.Rel.fst"
let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args) (Some (t)) r)
in (let _133_774 = (let _133_773 = (mk_problem scope orig gi_ps (vary_rel rel variance) ei None "expression subterm")
in (FStar_All.pipe_left (fun _133_772 -> EProb (_133_772)) _133_773))
in (FStar_Absyn_Syntax.E (gi_xs), _133_774)))
end)))
end
| (_44_1163, _44_1165, FStar_Absyn_Syntax.C (_44_1167)) -> begin
(FStar_All.failwith "impos")
end))
in (
# 828 "FStar.Tc.Rel.fst"
let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Absyn_Util.t_true)
end
| q::qs -> begin
(
# 832 "FStar.Tc.Rel.fst"
let _44_1243 = (match (q) with
| (bopt, variance, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Total (ti); FStar_Absyn_Syntax.tk = _44_1187; FStar_Absyn_Syntax.pos = _44_1185; FStar_Absyn_Syntax.fvs = _44_1183; FStar_Absyn_Syntax.uvs = _44_1181})) -> begin
(match ((sub_prob scope args (bopt, variance, FStar_Absyn_Syntax.T ((ti, Some (FStar_Absyn_Syntax.ktype)))))) with
| (FStar_Absyn_Syntax.T (gi_xs, _44_1195), prob) -> begin
(let _133_783 = (let _133_782 = (FStar_Absyn_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _133_781 -> FStar_Absyn_Syntax.C (_133_781)) _133_782))
in (_133_783, (prob)::[]))
end
| _44_1201 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_44_1203, _44_1205, FStar_Absyn_Syntax.C ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (c); FStar_Absyn_Syntax.tk = _44_1213; FStar_Absyn_Syntax.pos = _44_1211; FStar_Absyn_Syntax.fvs = _44_1209; FStar_Absyn_Syntax.uvs = _44_1207})) -> begin
(
# 840 "FStar.Tc.Rel.fst"
let components = (FStar_All.pipe_right c.FStar_Absyn_Syntax.effect_args (FStar_List.map (fun _44_29 -> (match (_44_29) with
| (FStar_Util.Inl (t), _44_1223) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.T ((t, None)))
end
| (FStar_Util.Inr (e), _44_1228) -> begin
(None, INVARIANT, FStar_Absyn_Syntax.E (e))
end))))
in (
# 843 "FStar.Tc.Rel.fst"
let components = ((None, COVARIANT, FStar_Absyn_Syntax.T ((c.FStar_Absyn_Syntax.result_typ, Some (FStar_Absyn_Syntax.ktype)))))::components
in (
# 844 "FStar.Tc.Rel.fst"
let _44_1234 = (let _133_785 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _133_785 FStar_List.unzip))
in (match (_44_1234) with
| (ktecs, sub_probs) -> begin
(
# 845 "FStar.Tc.Rel.fst"
let gi_xs = (let _133_790 = (let _133_789 = (let _133_786 = (FStar_List.hd ktecs)
in (FStar_All.pipe_right _133_786 un_T))
in (let _133_788 = (let _133_787 = (FStar_List.tl ktecs)
in (FStar_All.pipe_right _133_787 (FStar_List.map arg_of_ktec)))
in {FStar_Absyn_Syntax.effect_name = c.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _133_789; FStar_Absyn_Syntax.effect_args = _133_788; FStar_Absyn_Syntax.flags = c.FStar_Absyn_Syntax.flags}))
in (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp _133_790))
in (FStar_Absyn_Syntax.C (gi_xs), sub_probs))
end))))
end
| _44_1237 -> begin
(
# 854 "FStar.Tc.Rel.fst"
let _44_1240 = (sub_prob scope args q)
in (match (_44_1240) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_44_1243) with
| (ktec, probs) -> begin
(
# 857 "FStar.Tc.Rel.fst"
let _44_1256 = (match (q) with
| (Some (b), _44_1247, _44_1249) -> begin
(let _133_792 = (let _133_791 = (FStar_Absyn_Util.arg_of_non_null_binder b)
in (_133_791)::args)
in (Some (b), (b)::scope, _133_792))
end
| _44_1252 -> begin
(None, scope, args)
end)
in (match (_44_1256) with
| (bopt, scope, args) -> begin
(
# 861 "FStar.Tc.Rel.fst"
let _44_1260 = (aux scope args qs)
in (match (_44_1260) with
| (sub_probs, ktecs, f) -> begin
(
# 862 "FStar.Tc.Rel.fst"
let f = (match (bopt) with
| None -> begin
(let _133_795 = (let _133_794 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_133_794)
in (FStar_Absyn_Util.mk_conj_l _133_795))
end
| Some (b) -> begin
(let _133_799 = (let _133_798 = (FStar_Absyn_Util.close_forall ((b)::[]) f)
in (let _133_797 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_133_798)::_133_797))
in (FStar_Absyn_Util.mk_conj_l _133_799))
end)
in ((FStar_List.append probs sub_probs), (ktec)::ktecs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

# 867 "FStar.Tc.Rel.fst"
type slack =
{lower : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); upper : (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ); flag : Prims.bool FStar_ST.ref}

# 1066 "FStar.Tc.Rel.fst"
let is_Mkslack : slack  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkslack"))))

# 1068 "FStar.Tc.Rel.fst"
let fix_slack_uv : (FStar_Absyn_Syntax.typ FStar_Absyn_Syntax.uvar_basis FStar_Unionfind.uvar * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax)  ->  Prims.bool  ->  Prims.unit = (fun _44_1273 mul -> (match (_44_1273) with
| (uv, k) -> begin
(
# 1072 "FStar.Tc.Rel.fst"
let inst = if mul then begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_true k)
end else begin
(FStar_Absyn_Util.close_for_kind FStar_Absyn_Util.t_false k)
end
in (FStar_Absyn_Util.unchecked_unify uv inst))
end))

# 1075 "FStar.Tc.Rel.fst"
let fix_slack_vars : (Prims.bool * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) Prims.list  ->  Prims.unit = (fun slack -> (FStar_All.pipe_right slack (FStar_List.iter (fun _44_1279 -> (match (_44_1279) with
| (mul, s) -> begin
(match ((let _133_817 = (FStar_Absyn_Util.compress_typ s)
in _133_817.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(fix_slack_uv (uv, k) mul)
end
| _44_1285 -> begin
()
end)
end)))))

# 1080 "FStar.Tc.Rel.fst"
let fix_slack : slack  ->  FStar_Absyn_Syntax.typ = (fun slack -> (
# 1083 "FStar.Tc.Rel.fst"
let _44_1293 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.lower))
in (match (_44_1293) with
| (_44_1288, ul, kl, _44_1292) -> begin
(
# 1084 "FStar.Tc.Rel.fst"
let _44_1300 = (FStar_All.pipe_left destruct_flex_t (Prims.snd slack.upper))
in (match (_44_1300) with
| (_44_1295, uh, kh, _44_1299) -> begin
(
# 1085 "FStar.Tc.Rel.fst"
let _44_1301 = (fix_slack_uv (ul, kl) false)
in (
# 1086 "FStar.Tc.Rel.fst"
let _44_1303 = (fix_slack_uv (uh, kh) true)
in (
# 1087 "FStar.Tc.Rel.fst"
let _44_1305 = (FStar_ST.op_Colon_Equals slack.flag true)
in (FStar_Absyn_Util.mk_conj (Prims.fst slack.lower) (Prims.fst slack.upper)))))
end))
end)))

# 1088 "FStar.Tc.Rel.fst"
let new_slack_var : FStar_Tc_Env.env  ->  slack  ->  ((FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.typ) * FStar_Absyn_Syntax.binders) = (fun env slack -> (
# 1091 "FStar.Tc.Rel.fst"
let xs = (let _133_825 = (let _133_824 = (destruct_flex_pattern env (Prims.snd slack.lower))
in (FStar_All.pipe_right _133_824 Prims.snd))
in (FStar_All.pipe_right _133_825 FStar_Util.must))
in (let _133_826 = (new_tvar (Prims.fst slack.lower).FStar_Absyn_Syntax.pos xs FStar_Absyn_Syntax.ktype)
in (_133_826, xs))))

# 1092 "FStar.Tc.Rel.fst"
let new_slack_formula = (fun p env wl xs low high -> (
# 1095 "FStar.Tc.Rel.fst"
let _44_1318 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_44_1318) with
| (low_var, uv1) -> begin
(
# 1096 "FStar.Tc.Rel.fst"
let wl = (add_slack_add uv1 wl)
in (
# 1097 "FStar.Tc.Rel.fst"
let _44_1322 = (new_tvar p xs FStar_Absyn_Syntax.ktype)
in (match (_44_1322) with
| (high_var, uv2) -> begin
(
# 1098 "FStar.Tc.Rel.fst"
let wl = (add_slack_mul uv2 wl)
in (
# 1099 "FStar.Tc.Rel.fst"
let low = (match (low) with
| None -> begin
(FStar_Absyn_Util.mk_disj FStar_Absyn_Util.t_false low_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_disj f low_var)
end)
in (
# 1102 "FStar.Tc.Rel.fst"
let high = (match (high) with
| None -> begin
(FStar_Absyn_Util.mk_conj FStar_Absyn_Util.t_true high_var)
end
| Some (f) -> begin
(FStar_Absyn_Util.mk_conj f high_var)
end)
in (let _133_836 = (let _133_835 = (let _133_834 = (let _133_833 = (FStar_Util.mk_ref false)
in (low, high, _133_833))
in FStar_Absyn_Syntax.Meta_slack_formula (_133_834))
in (FStar_Absyn_Syntax.mk_Typ_meta _133_835))
in (_133_836, wl)))))
end)))
end)))

# 1105 "FStar.Tc.Rel.fst"
let destruct_slack : FStar_Tc_Env.env  ->  worklist  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ, slack) FStar_Util.either = (fun env wl phi -> (
# 1119 "FStar.Tc.Rel.fst"
let rec destruct = (fun conn_lid mk_conn phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _44_1346; FStar_Absyn_Syntax.pos = _44_1344; FStar_Absyn_Syntax.fvs = _44_1342; FStar_Absyn_Syntax.uvs = _44_1340}, (FStar_Util.Inl (lhs), _44_1358)::(FStar_Util.Inl (rhs), _44_1353)::[]) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v conn_lid) -> begin
(
# 1123 "FStar.Tc.Rel.fst"
let rhs = (compress env wl rhs)
in (match (rhs.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
Some ((lhs, rhs))
end
| _44_1384 -> begin
(match ((destruct conn_lid mk_conn rhs)) with
| None -> begin
None
end
| Some (rest, uvar) -> begin
(let _133_860 = (let _133_859 = (mk_conn lhs rest)
in (_133_859, uvar))
in Some (_133_860))
end)
end))
end
| _44_1391 -> begin
None
end))
in (
# 1136 "FStar.Tc.Rel.fst"
let phi = (FStar_Absyn_Util.compress_typ phi)
in (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (phi1, phi2, flag)) -> begin
if (FStar_ST.read flag) then begin
(let _133_861 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_133_861))
end else begin
(
# 1141 "FStar.Tc.Rel.fst"
let low = (let _133_862 = (compress env wl phi1)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.or_lid FStar_Absyn_Util.mk_disj) _133_862))
in (
# 1142 "FStar.Tc.Rel.fst"
let hi = (let _133_863 = (compress env wl phi2)
in (FStar_All.pipe_left (destruct FStar_Absyn_Const.and_lid FStar_Absyn_Util.mk_disj) _133_863))
in (match ((low, hi)) with
| (None, None) -> begin
(
# 1144 "FStar.Tc.Rel.fst"
let _44_1404 = (FStar_ST.op_Colon_Equals flag true)
in (let _133_864 = (FStar_Absyn_Util.unmeta_typ phi)
in FStar_Util.Inl (_133_864)))
end
| ((Some (_), None)) | ((None, Some (_))) -> begin
(FStar_All.failwith "Impossible")
end
| (Some (l), Some (u)) -> begin
FStar_Util.Inr ({lower = l; upper = u; flag = flag})
end)))
end
end
| _44_1422 -> begin
FStar_Util.Inl (phi)
end))))

# 1150 "FStar.Tc.Rel.fst"
let rec eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (
# 1159 "FStar.Tc.Rel.fst"
let t1 = (FStar_Absyn_Util.compress_typ t1)
in (
# 1160 "FStar.Tc.Rel.fst"
let t2 = (FStar_Absyn_Util.compress_typ t2)
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Typ_const (f), FStar_Absyn_Syntax.Typ_const (g)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Typ_uvar (u1, _44_1439), FStar_Absyn_Syntax.Typ_uvar (u2, _44_1444)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Absyn_Syntax.Typ_app (h1, args1), FStar_Absyn_Syntax.Typ_app (h2, args2)) -> begin
((eq_typ h1 h2) && (eq_args args1 args2))
end
| _44_1458 -> begin
false
end))))
and eq_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  Prims.bool = (fun e1 e2 -> (
# 1169 "FStar.Tc.Rel.fst"
let e1 = (FStar_Absyn_Util.compress_exp e1)
in (
# 1170 "FStar.Tc.Rel.fst"
let e2 = (FStar_Absyn_Util.compress_exp e2)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (a), FStar_Absyn_Syntax.Exp_bvar (b)) -> begin
(FStar_Absyn_Util.bvar_eq a b)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _44_1470), FStar_Absyn_Syntax.Exp_fvar (g, _44_1475)) -> begin
(FStar_Absyn_Util.fvar_eq f g)
end
| (FStar_Absyn_Syntax.Exp_constant (c), FStar_Absyn_Syntax.Exp_constant (d)) -> begin
(c = d)
end
| (FStar_Absyn_Syntax.Exp_app (h1, args1), FStar_Absyn_Syntax.Exp_app (h2, args2)) -> begin
((eq_exp h1 h2) && (eq_args args1 args2))
end
| _44_1494 -> begin
false
end))))
and eq_args : FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.args  ->  Prims.bool = (fun a1 a2 -> if ((FStar_List.length a1) = (FStar_List.length a2)) then begin
(FStar_List.forall2 (fun a1 a2 -> (match ((a1, a2)) with
| ((FStar_Util.Inl (t), _44_1502), (FStar_Util.Inl (s), _44_1507)) -> begin
(eq_typ t s)
end
| ((FStar_Util.Inr (e), _44_1513), (FStar_Util.Inr (f), _44_1518)) -> begin
(eq_exp e f)
end
| _44_1522 -> begin
false
end)) a1 a2)
end else begin
false
end)

# 1183 "FStar.Tc.Rel.fst"
type flex_t =
(FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.args)

# 1187 "FStar.Tc.Rel.fst"
type im_or_proj_t =
((FStar_Absyn_Syntax.uvar_t * FStar_Absyn_Syntax.knd) * FStar_Absyn_Syntax.arg Prims.list * FStar_Absyn_Syntax.binders * ((FStar_Absyn_Syntax.ktec Prims.list  ->  FStar_Absyn_Syntax.typ) * (FStar_Absyn_Syntax.typ  ->  Prims.bool) * (FStar_Absyn_Syntax.binder Prims.option * variance * FStar_Absyn_Syntax.ktec) Prims.list))

# 1188 "FStar.Tc.Rel.fst"
let rigid_rigid : Prims.int = 0

# 1190 "FStar.Tc.Rel.fst"
let flex_rigid_eq : Prims.int = 1

# 1191 "FStar.Tc.Rel.fst"
let flex_refine_inner : Prims.int = 2

# 1192 "FStar.Tc.Rel.fst"
let flex_refine : Prims.int = 3

# 1193 "FStar.Tc.Rel.fst"
let flex_rigid : Prims.int = 4

# 1194 "FStar.Tc.Rel.fst"
let rigid_flex : Prims.int = 5

# 1195 "FStar.Tc.Rel.fst"
let refine_flex : Prims.int = 6

# 1196 "FStar.Tc.Rel.fst"
let flex_flex : Prims.int = 7

# 1197 "FStar.Tc.Rel.fst"
let compress_prob : worklist  ->  prob  ->  prob = (fun wl p -> (match (p) with
| KProb (p) -> begin
(let _133_894 = (
# 1199 "FStar.Tc.Rel.fst"
let _44_1527 = p
in (let _133_892 = (compress_k wl.tcenv wl p.lhs)
in (let _133_891 = (compress_k wl.tcenv wl p.rhs)
in {lhs = _133_892; relation = _44_1527.relation; rhs = _133_891; element = _44_1527.element; logical_guard = _44_1527.logical_guard; scope = _44_1527.scope; reason = _44_1527.reason; loc = _44_1527.loc; rank = _44_1527.rank})))
in (FStar_All.pipe_right _133_894 (fun _133_893 -> KProb (_133_893))))
end
| TProb (p) -> begin
(let _133_898 = (
# 1200 "FStar.Tc.Rel.fst"
let _44_1531 = p
in (let _133_896 = (compress wl.tcenv wl p.lhs)
in (let _133_895 = (compress wl.tcenv wl p.rhs)
in {lhs = _133_896; relation = _44_1531.relation; rhs = _133_895; element = _44_1531.element; logical_guard = _44_1531.logical_guard; scope = _44_1531.scope; reason = _44_1531.reason; loc = _44_1531.loc; rank = _44_1531.rank})))
in (FStar_All.pipe_right _133_898 (fun _133_897 -> TProb (_133_897))))
end
| EProb (p) -> begin
(let _133_902 = (
# 1201 "FStar.Tc.Rel.fst"
let _44_1535 = p
in (let _133_900 = (compress_e wl.tcenv wl p.lhs)
in (let _133_899 = (compress_e wl.tcenv wl p.rhs)
in {lhs = _133_900; relation = _44_1535.relation; rhs = _133_899; element = _44_1535.element; logical_guard = _44_1535.logical_guard; scope = _44_1535.scope; reason = _44_1535.reason; loc = _44_1535.loc; rank = _44_1535.rank})))
in (FStar_All.pipe_right _133_902 (fun _133_901 -> EProb (_133_901))))
end
| CProb (_44_1538) -> begin
p
end))

# 1202 "FStar.Tc.Rel.fst"
let rank : worklist  ->  prob  ->  (Prims.int * prob) = (fun wl prob -> (
# 1205 "FStar.Tc.Rel.fst"
let prob = (let _133_907 = (compress_prob wl prob)
in (FStar_All.pipe_right _133_907 maybe_invert_p))
in (match (prob) with
| KProb (kp) -> begin
(
# 1208 "FStar.Tc.Rel.fst"
let rank = (match ((kp.lhs.FStar_Absyn_Syntax.n, kp.rhs.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Kind_uvar (_44_1546), FStar_Absyn_Syntax.Kind_uvar (_44_1549)) -> begin
flex_flex
end
| (FStar_Absyn_Syntax.Kind_uvar (_44_1553), _44_1556) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
flex_rigid
end
end
| (_44_1559, FStar_Absyn_Syntax.Kind_uvar (_44_1561)) -> begin
if (kp.relation = EQ) then begin
flex_rigid_eq
end else begin
rigid_flex
end
end
| (_44_1565, _44_1567) -> begin
rigid_rigid
end)
in (let _133_909 = (FStar_All.pipe_right (
# 1214 "FStar.Tc.Rel.fst"
let _44_1570 = kp
in {lhs = _44_1570.lhs; relation = _44_1570.relation; rhs = _44_1570.rhs; element = _44_1570.element; logical_guard = _44_1570.logical_guard; scope = _44_1570.scope; reason = _44_1570.reason; loc = _44_1570.loc; rank = Some (rank)}) (fun _133_908 -> KProb (_133_908)))
in (rank, _133_909)))
end
| TProb (tp) -> begin
(
# 1217 "FStar.Tc.Rel.fst"
let _44_1577 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_44_1577) with
| (lh, _44_1576) -> begin
(
# 1218 "FStar.Tc.Rel.fst"
let _44_1581 = (FStar_Absyn_Util.head_and_args tp.rhs)
in (match (_44_1581) with
| (rh, _44_1580) -> begin
(
# 1219 "FStar.Tc.Rel.fst"
let _44_1637 = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_uvar (_44_1583), FStar_Absyn_Syntax.Typ_uvar (_44_1586)) -> begin
(flex_flex, tp)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Typ_uvar (_))) when (tp.relation = EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Absyn_Syntax.Typ_uvar (_44_1602), _44_1605) -> begin
(
# 1226 "FStar.Tc.Rel.fst"
let _44_1609 = (base_and_refinement wl.tcenv wl tp.rhs)
in (match (_44_1609) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _44_1612 -> begin
(
# 1230 "FStar.Tc.Rel.fst"
let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _133_911 = (
# 1234 "FStar.Tc.Rel.fst"
let _44_1614 = tp
in (let _133_910 = (force_refinement (b, ref_opt))
in {lhs = _44_1614.lhs; relation = _44_1614.relation; rhs = _133_910; element = _44_1614.element; logical_guard = _44_1614.logical_guard; scope = _44_1614.scope; reason = _44_1614.reason; loc = _44_1614.loc; rank = _44_1614.rank}))
in (rank, _133_911)))
end)
end))
end
| (_44_1617, FStar_Absyn_Syntax.Typ_uvar (_44_1619)) -> begin
(
# 1238 "FStar.Tc.Rel.fst"
let _44_1624 = (base_and_refinement wl.tcenv wl tp.lhs)
in (match (_44_1624) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _44_1627 -> begin
(let _133_913 = (
# 1241 "FStar.Tc.Rel.fst"
let _44_1628 = tp
in (let _133_912 = (force_refinement (b, ref_opt))
in {lhs = _133_912; relation = _44_1628.relation; rhs = _44_1628.rhs; element = _44_1628.element; logical_guard = _44_1628.logical_guard; scope = _44_1628.scope; reason = _44_1628.reason; loc = _44_1628.loc; rank = _44_1628.rank}))
in (refine_flex, _133_913))
end)
end))
end
| (_44_1631, _44_1633) -> begin
(rigid_rigid, tp)
end)
in (match (_44_1637) with
| (rank, tp) -> begin
(let _133_915 = (FStar_All.pipe_right (
# 1246 "FStar.Tc.Rel.fst"
let _44_1638 = tp
in {lhs = _44_1638.lhs; relation = _44_1638.relation; rhs = _44_1638.rhs; element = _44_1638.element; logical_guard = _44_1638.logical_guard; scope = _44_1638.scope; reason = _44_1638.reason; loc = _44_1638.loc; rank = Some (rank)}) (fun _133_914 -> TProb (_133_914)))
in (rank, _133_915))
end))
end))
end))
end
| EProb (ep) -> begin
(
# 1249 "FStar.Tc.Rel.fst"
let _44_1645 = (FStar_Absyn_Util.head_and_args_e ep.lhs)
in (match (_44_1645) with
| (lh, _44_1644) -> begin
(
# 1250 "FStar.Tc.Rel.fst"
let _44_1649 = (FStar_Absyn_Util.head_and_args_e ep.rhs)
in (match (_44_1649) with
| (rh, _44_1648) -> begin
(
# 1251 "FStar.Tc.Rel.fst"
let rank = (match ((lh.FStar_Absyn_Syntax.n, rh.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_uvar (_44_1651), FStar_Absyn_Syntax.Exp_uvar (_44_1654)) -> begin
flex_flex
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((_, FStar_Absyn_Syntax.Exp_uvar (_))) -> begin
flex_rigid_eq
end
| (_44_1670, _44_1672) -> begin
rigid_rigid
end)
in (let _133_917 = (FStar_All.pipe_right (
# 1256 "FStar.Tc.Rel.fst"
let _44_1675 = ep
in {lhs = _44_1675.lhs; relation = _44_1675.relation; rhs = _44_1675.rhs; element = _44_1675.element; logical_guard = _44_1675.logical_guard; scope = _44_1675.scope; reason = _44_1675.reason; loc = _44_1675.loc; rank = Some (rank)}) (fun _133_916 -> EProb (_133_916)))
in (rank, _133_917)))
end))
end))
end
| CProb (cp) -> begin
(let _133_919 = (FStar_All.pipe_right (
# 1258 "FStar.Tc.Rel.fst"
let _44_1679 = cp
in {lhs = _44_1679.lhs; relation = _44_1679.relation; rhs = _44_1679.rhs; element = _44_1679.element; logical_guard = _44_1679.logical_guard; scope = _44_1679.scope; reason = _44_1679.reason; loc = _44_1679.loc; rank = Some (rigid_rigid)}) (fun _133_918 -> CProb (_133_918)))
in (rigid_rigid, _133_919))
end)))

# 1258 "FStar.Tc.Rel.fst"
let next_prob : worklist  ->  (prob Prims.option * prob Prims.list * Prims.int) = (fun wl -> (
# 1264 "FStar.Tc.Rel.fst"
let rec aux = (fun _44_1686 probs -> (match (_44_1686) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(
# 1267 "FStar.Tc.Rel.fst"
let _44_1694 = (rank wl hd)
in (match (_44_1694) with
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

# 1278 "FStar.Tc.Rel.fst"
let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

# 1280 "FStar.Tc.Rel.fst"
let rec solve_flex_rigid_join : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (
# 1282 "FStar.Tc.Rel.fst"
let _44_1705 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_969 = (prob_to_string env (TProb (tp)))
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _133_969))
end else begin
()
end
in (
# 1284 "FStar.Tc.Rel.fst"
let _44_1709 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_44_1709) with
| (u, args) -> begin
(
# 1285 "FStar.Tc.Rel.fst"
let _44_1715 = (0, 1, 2, 3, 4)
in (match (_44_1715) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(
# 1286 "FStar.Tc.Rel.fst"
let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (
# 1288 "FStar.Tc.Rel.fst"
let base_types_match = (fun t1 t2 -> (
# 1289 "FStar.Tc.Rel.fst"
let _44_1724 = (FStar_Absyn_Util.head_and_args t1)
in (match (_44_1724) with
| (h1, args1) -> begin
(
# 1290 "FStar.Tc.Rel.fst"
let _44_1728 = (FStar_Absyn_Util.head_and_args t2)
in (match (_44_1728) with
| (h2, _44_1727) -> begin
(match ((h1.FStar_Absyn_Syntax.n, h2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_const (tc1), FStar_Absyn_Syntax.Typ_const (tc2)) -> begin
if (FStar_Ident.lid_equals tc1.FStar_Absyn_Syntax.v tc2.FStar_Absyn_Syntax.v) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _133_981 = (let _133_980 = (let _133_979 = (new_problem env t1 EQ t2 None t1.FStar_Absyn_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _133_978 -> TProb (_133_978)) _133_979))
in (_133_980)::[])
in Some (_133_981))
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
| _44_1740 -> begin
None
end)
end))
end)))
in (
# 1306 "FStar.Tc.Rel.fst"
let conjoin = (fun t1 t2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_refine (x, phi1), FStar_Absyn_Syntax.Typ_refine (y, phi2)) -> begin
(
# 1308 "FStar.Tc.Rel.fst"
let m = (base_types_match x.FStar_Absyn_Syntax.sort y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(
# 1312 "FStar.Tc.Rel.fst"
let phi2 = (let _133_988 = (let _133_987 = (FStar_Absyn_Syntax.v_binder x)
in (let _133_986 = (FStar_Absyn_Syntax.v_binder y)
in (FStar_Absyn_Util.mk_subst_one_binder _133_987 _133_986)))
in (FStar_Absyn_Util.subst_typ _133_988 phi2))
in (let _133_992 = (let _133_991 = (let _133_990 = (let _133_989 = (FStar_Absyn_Util.mk_conj phi1 phi2)
in (x, _133_989))
in (FStar_Absyn_Syntax.mk_Typ_refine _133_990 (Some (FStar_Absyn_Syntax.ktype)) t1.FStar_Absyn_Syntax.pos))
in (_133_991, m))
in Some (_133_992)))
end))
end
| (_44_1759, FStar_Absyn_Syntax.Typ_refine (y, _44_1762)) -> begin
(
# 1317 "FStar.Tc.Rel.fst"
let m = (base_types_match t1 y.FStar_Absyn_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Absyn_Syntax.Typ_refine (x, _44_1772), _44_1776) -> begin
(
# 1324 "FStar.Tc.Rel.fst"
let m = (base_types_match x.FStar_Absyn_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _44_1783 -> begin
(
# 1331 "FStar.Tc.Rel.fst"
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
# 1337 "FStar.Tc.Rel.fst"
let tt = u
in (match (tt.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_uvar (uv, _44_1791) -> begin
(
# 1341 "FStar.Tc.Rel.fst"
let _44_1816 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _44_30 -> (match (_44_30) with
| TProb (tp) -> begin
(match (tp.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(
# 1345 "FStar.Tc.Rel.fst"
let _44_1802 = (FStar_Absyn_Util.head_and_args tp.lhs)
in (match (_44_1802) with
| (u', _44_1801) -> begin
(match ((let _133_994 = (compress env wl u')
in _133_994.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_uvar (uv', _44_1805) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _44_1809 -> begin
false
end)
end))
end
| _44_1811 -> begin
false
end)
end
| _44_1813 -> begin
false
end))))
in (match (_44_1816) with
| (upper_bounds, rest) -> begin
(
# 1354 "FStar.Tc.Rel.fst"
let rec make_upper_bound = (fun _44_1820 tps -> (match (_44_1820) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| TProb (hd)::tl -> begin
(match ((let _133_999 = (compress env wl hd.rhs)
in (conjoin bound _133_999))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _44_1833 -> begin
None
end)
end))
in (match ((let _133_1001 = (let _133_1000 = (compress env wl tp.rhs)
in (_133_1000, []))
in (make_upper_bound _133_1001 upper_bounds))) with
| None -> begin
(
# 1365 "FStar.Tc.Rel.fst"
let _44_1835 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(
# 1378 "FStar.Tc.Rel.fst"
let eq_prob = (new_problem env tp.lhs EQ rhs_bound None tp.loc "joining refinements")
in (match ((solve_t env eq_prob (
# 1379 "FStar.Tc.Rel.fst"
let _44_1842 = wl
in {attempting = sub_probs; wl_deferred = _44_1842.wl_deferred; subst = _44_1842.subst; ctr = _44_1842.ctr; slack_vars = _44_1842.slack_vars; defer_ok = _44_1842.defer_ok; smt_ok = _44_1842.smt_ok; tcenv = _44_1842.tcenv}))) with
| Success (subst, _44_1846) -> begin
(
# 1381 "FStar.Tc.Rel.fst"
let wl = (
# 1381 "FStar.Tc.Rel.fst"
let _44_1849 = wl
in {attempting = rest; wl_deferred = _44_1849.wl_deferred; subst = []; ctr = _44_1849.ctr; slack_vars = _44_1849.slack_vars; defer_ok = _44_1849.defer_ok; smt_ok = _44_1849.smt_ok; tcenv = _44_1849.tcenv})
in (
# 1382 "FStar.Tc.Rel.fst"
let wl = (solve_prob (TProb (tp)) None subst wl)
in (
# 1383 "FStar.Tc.Rel.fst"
let _44_1855 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _44_1858 -> begin
None
end))
end))
end))
end
| _44_1860 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve : FStar_Tc_Env.env  ->  worklist  ->  solution = (fun env probs -> (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(
# 1394 "FStar.Tc.Rel.fst"
let probs = (
# 1394 "FStar.Tc.Rel.fst"
let _44_1868 = probs
in {attempting = tl; wl_deferred = _44_1868.wl_deferred; subst = _44_1868.subst; ctr = _44_1868.ctr; slack_vars = _44_1868.slack_vars; defer_ok = _44_1868.defer_ok; smt_ok = _44_1868.smt_ok; tcenv = _44_1868.tcenv})
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
| (None, _44_1884, _44_1886) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ((probs.subst, {carry = []; slack = probs.slack_vars}))
end
| _44_1890 -> begin
(
# 1412 "FStar.Tc.Rel.fst"
let _44_1899 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _44_1896 -> (match (_44_1896) with
| (c, _44_1893, _44_1895) -> begin
(c < probs.ctr)
end))))
in (match (_44_1899) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _133_1010 = (let _133_1009 = (let _133_1008 = (FStar_List.map (fun _44_1905 -> (match (_44_1905) with
| (_44_1902, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in {carry = _133_1008; slack = probs.slack_vars})
in (probs.subst, _133_1009))
in Success (_133_1010))
end
| _44_1907 -> begin
(let _133_1013 = (
# 1415 "FStar.Tc.Rel.fst"
let _44_1908 = probs
in (let _133_1012 = (FStar_All.pipe_right attempt (FStar_List.map (fun _44_1915 -> (match (_44_1915) with
| (_44_1911, _44_1913, y) -> begin
y
end))))
in {attempting = _133_1012; wl_deferred = rest; subst = _44_1908.subst; ctr = _44_1908.ctr; slack_vars = _44_1908.slack_vars; defer_ok = _44_1908.defer_ok; smt_ok = _44_1908.smt_ok; tcenv = _44_1908.tcenv}))
in (solve env _133_1013))
end)
end))
end)
end))
and solve_binders : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.binders  ->  prob  ->  worklist  ->  (FStar_Absyn_Syntax.binders  ->  FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.subst_elt Prims.list  ->  prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (
# 1421 "FStar.Tc.Rel.fst"
let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(
# 1424 "FStar.Tc.Rel.fst"
let rhs_prob = (rhs scope env subst)
in (
# 1425 "FStar.Tc.Rel.fst"
let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula))))
end
| (((FStar_Util.Inl (_), _)::_, (FStar_Util.Inr (_), _)::_)) | (((FStar_Util.Inr (_), _)::_, (FStar_Util.Inl (_), _)::_)) -> begin
FStar_Util.Inr ("sort mismatch")
end
| (hd1::xs, hd2::ys) -> begin
(
# 1432 "FStar.Tc.Rel.fst"
let subst = (let _133_1039 = (FStar_Absyn_Util.mk_subst_one_binder hd2 hd1)
in (FStar_List.append _133_1039 subst))
in (
# 1433 "FStar.Tc.Rel.fst"
let env = (let _133_1040 = (FStar_Tc_Env.binding_of_binder hd2)
in (FStar_Tc_Env.push_local_binding env _133_1040))
in (
# 1434 "FStar.Tc.Rel.fst"
let prob = (match (((Prims.fst hd1), (Prims.fst hd2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _133_1044 = (let _133_1043 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (let _133_1042 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _133_1043 _133_1042 b.FStar_Absyn_Syntax.sort None "Formal type parameter")))
in (FStar_All.pipe_left (fun _133_1041 -> KProb (_133_1041)) _133_1044))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _133_1048 = (let _133_1047 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (let _133_1046 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem ((hd2)::scope) orig _133_1047 _133_1046 y.FStar_Absyn_Syntax.sort None "Formal value parameter")))
in (FStar_All.pipe_left (fun _133_1045 -> TProb (_133_1045)) _133_1048))
end
| _44_1991 -> begin
(FStar_All.failwith "impos")
end)
in (match ((aux ((hd2)::scope) env subst xs ys)) with
| FStar_Util.Inr (msg) -> begin
FStar_Util.Inr (msg)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1443 "FStar.Tc.Rel.fst"
let phi = (let _133_1050 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _133_1049 = (FStar_Absyn_Util.close_forall ((hd2)::[]) phi)
in (FStar_Absyn_Util.mk_conj _133_1050 _133_1049)))
in FStar_Util.Inl (((prob)::sub_probs, phi)))
end))))
end
| _44_2001 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (
# 1449 "FStar.Tc.Rel.fst"
let scope = (FStar_Tc_Env.binders env)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(
# 1453 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_k : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (match ((compress_prob wl (KProb (problem)))) with
| KProb (p) -> begin
(solve_k' env p wl)
end
| _44_2016 -> begin
(FStar_All.failwith "impossible")
end))
and solve_k' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.knd, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1462 "FStar.Tc.Rel.fst"
let orig = KProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _133_1057 = (solve_prob orig None [] wl)
in (solve env _133_1057))
end else begin
(
# 1464 "FStar.Tc.Rel.fst"
let k1 = problem.lhs
in (
# 1465 "FStar.Tc.Rel.fst"
let k2 = problem.rhs
in if (FStar_Util.physical_equality k1 k2) then begin
(let _133_1058 = (solve_prob orig None [] wl)
in (solve env _133_1058))
end else begin
(
# 1467 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 1469 "FStar.Tc.Rel.fst"
let imitate_k = (fun _44_2032 -> (match (_44_2032) with
| (rel, u, ps, xs, (h, qs)) -> begin
(
# 1473 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 1474 "FStar.Tc.Rel.fst"
let _44_2037 = (imitation_sub_probs orig env xs ps qs)
in (match (_44_2037) with
| (sub_probs, gs_xs, f) -> begin
(
# 1475 "FStar.Tc.Rel.fst"
let im = (let _133_1074 = (let _133_1073 = (h gs_xs)
in (xs, _133_1073))
in (FStar_Absyn_Syntax.mk_Kind_lam _133_1074 r))
in (
# 1476 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (f)) ((UK ((u, im)))::[]) wl)
in (solve env (attempt sub_probs wl))))
end)))
end))
in (
# 1479 "FStar.Tc.Rel.fst"
let flex_rigid = (fun rel u args k -> (
# 1480 "FStar.Tc.Rel.fst"
let maybe_vars1 = (pat_vars env [] args)
in (match (maybe_vars1) with
| Some (xs) -> begin
(
# 1483 "FStar.Tc.Rel.fst"
let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (
# 1484 "FStar.Tc.Rel.fst"
let fvs2 = (FStar_Absyn_Util.freevars_kind k2)
in (
# 1485 "FStar.Tc.Rel.fst"
let uvs2 = (FStar_Absyn_Util.uvars_in_kind k2)
in if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && (not ((FStar_Util.set_mem u uvs2.FStar_Absyn_Syntax.uvars_k)))) then begin
(
# 1489 "FStar.Tc.Rel.fst"
let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, k2) r)
in (let _133_1083 = (solve_prob orig None ((UK ((u, k1)))::[]) wl)
in (solve env _133_1083)))
end else begin
(let _133_1088 = (let _133_1087 = (FStar_All.pipe_right xs FStar_Absyn_Util.args_of_non_null_binders)
in (let _133_1086 = (decompose_kind env k)
in (rel, u, _133_1087, xs, _133_1086)))
in (imitate_k _133_1088))
end)))
end
| None -> begin
(giveup env "flex-rigid: not a pattern" (KProb (problem)))
end)))
in (match ((k1.FStar_Absyn_Syntax.n, k2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Kind_type, FStar_Absyn_Syntax.Kind_type)) | ((FStar_Absyn_Syntax.Kind_effect, FStar_Absyn_Syntax.Kind_effect)) -> begin
(let _133_1089 = (solve_prob orig None [] wl)
in (FStar_All.pipe_left (solve env) _133_1089))
end
| (FStar_Absyn_Syntax.Kind_abbrev (_44_2060, k1), _44_2065) -> begin
(solve_k env (
# 1500 "FStar.Tc.Rel.fst"
let _44_2067 = problem
in {lhs = k1; relation = _44_2067.relation; rhs = _44_2067.rhs; element = _44_2067.element; logical_guard = _44_2067.logical_guard; scope = _44_2067.scope; reason = _44_2067.reason; loc = _44_2067.loc; rank = _44_2067.rank}) wl)
end
| (_44_2070, FStar_Absyn_Syntax.Kind_abbrev (_44_2072, k2)) -> begin
(solve_k env (
# 1501 "FStar.Tc.Rel.fst"
let _44_2077 = problem
in {lhs = _44_2077.lhs; relation = _44_2077.relation; rhs = k2; element = _44_2077.element; logical_guard = _44_2077.logical_guard; scope = _44_2077.scope; reason = _44_2077.reason; loc = _44_2077.loc; rank = _44_2077.rank}) wl)
end
| (FStar_Absyn_Syntax.Kind_arrow (bs1, k1'), FStar_Absyn_Syntax.Kind_arrow (bs2, k2')) -> begin
(
# 1504 "FStar.Tc.Rel.fst"
let sub_prob = (fun scope env subst -> (let _133_1098 = (let _133_1097 = (FStar_Absyn_Util.subst_kind subst k1')
in (mk_problem scope orig _133_1097 problem.relation k2' None "Arrow-kind result"))
in (FStar_All.pipe_left (fun _133_1096 -> KProb (_133_1096)) _133_1098)))
in (solve_binders env bs1 bs2 orig wl sub_prob))
end
| (FStar_Absyn_Syntax.Kind_uvar (u1, args1), FStar_Absyn_Syntax.Kind_uvar (u2, args2)) -> begin
(
# 1509 "FStar.Tc.Rel.fst"
let maybe_vars1 = (pat_vars env [] args1)
in (
# 1510 "FStar.Tc.Rel.fst"
let maybe_vars2 = (pat_vars env [] args2)
in (match ((maybe_vars1, maybe_vars2)) with
| ((None, _)) | ((_, None)) -> begin
(giveup env "flex-flex: non patterns" (KProb (problem)))
end
| (Some (xs), Some (ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(solve env wl)
end else begin
(
# 1521 "FStar.Tc.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1522 "FStar.Tc.Rel.fst"
let _44_2120 = (new_kvar r zs)
in (match (_44_2120) with
| (u, _44_2119) -> begin
(
# 1523 "FStar.Tc.Rel.fst"
let k1 = (FStar_Absyn_Syntax.mk_Kind_lam (xs, u) r)
in (
# 1524 "FStar.Tc.Rel.fst"
let k2 = (FStar_Absyn_Syntax.mk_Kind_lam (ys, u) r)
in (
# 1525 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig None ((UK ((u1, k1)))::(UK ((u2, k2)))::[]) wl)
in (solve env wl))))
end)))
end
end)))
end
| (FStar_Absyn_Syntax.Kind_uvar (u, args), _44_2129) -> begin
(flex_rigid problem.relation u args k2)
end
| (_44_2132, FStar_Absyn_Syntax.Kind_uvar (u, args)) -> begin
(flex_rigid (invert_rel problem.relation) u args k1)
end
| ((FStar_Absyn_Syntax.Kind_delayed (_), _)) | ((FStar_Absyn_Syntax.Kind_unknown, _)) | ((_, FStar_Absyn_Syntax.Kind_delayed (_))) | ((_, FStar_Absyn_Syntax.Kind_unknown)) -> begin
(FStar_All.failwith "Impossible")
end
| _44_2159 -> begin
(giveup env "head mismatch (k-1)" (KProb (problem)))
end))))
end))
end))
and solve_t : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1543 "FStar.Tc.Rel.fst"
let p = (compress_prob wl (TProb (problem)))
in (match (p) with
| TProb (p) -> begin
(solve_t' env p wl)
end
| _44_2167 -> begin
(FStar_All.failwith "Impossible")
end)))
and solve_t' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 1549 "FStar.Tc.Rel.fst"
let giveup_or_defer = (fun orig msg -> if wl.defer_ok then begin
(
# 1552 "FStar.Tc.Rel.fst"
let _44_2174 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1109 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _133_1109 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
in (
# 1559 "FStar.Tc.Rel.fst"
let imitate_t = (fun orig env wl p -> (
# 1560 "FStar.Tc.Rel.fst"
let _44_2191 = p
in (match (_44_2191) with
| ((u, k), ps, xs, (h, _44_2188, qs)) -> begin
(
# 1561 "FStar.Tc.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1566 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 1567 "FStar.Tc.Rel.fst"
let _44_2197 = (imitation_sub_probs orig env xs ps qs)
in (match (_44_2197) with
| (sub_probs, gs_xs, formula) -> begin
(
# 1568 "FStar.Tc.Rel.fst"
let im = (let _133_1121 = (let _133_1120 = (h gs_xs)
in (xs, _133_1120))
in (FStar_Absyn_Syntax.mk_Typ_lam' _133_1121 None r))
in (
# 1569 "FStar.Tc.Rel.fst"
let _44_2199 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1126 = (FStar_Absyn_Print.typ_to_string im)
in (let _133_1125 = (FStar_Absyn_Print.tag_of_typ im)
in (let _133_1124 = (let _133_1122 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _133_1122 (FStar_String.concat ", ")))
in (let _133_1123 = (FStar_Tc_Normalize.formula_norm_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _133_1126 _133_1125 _133_1124 _133_1123)))))
end else begin
()
end
in (
# 1574 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (formula)) ((UT (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (
# 1579 "FStar.Tc.Rel.fst"
let project_t = (fun orig env wl i p -> (
# 1580 "FStar.Tc.Rel.fst"
let _44_2215 = p
in (match (_44_2215) with
| (u, ps, xs, (h, matches, qs)) -> begin
(
# 1584 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 1585 "FStar.Tc.Rel.fst"
let pi = (FStar_List.nth ps i)
in (
# 1586 "FStar.Tc.Rel.fst"
let rec gs = (fun k -> (
# 1587 "FStar.Tc.Rel.fst"
let _44_2222 = (FStar_Absyn_Util.kind_formals k)
in (match (_44_2222) with
| (bs, k) -> begin
(
# 1588 "FStar.Tc.Rel.fst"
let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| hd::tl -> begin
(
# 1591 "FStar.Tc.Rel.fst"
let _44_2251 = (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(
# 1593 "FStar.Tc.Rel.fst"
let k_a = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (
# 1594 "FStar.Tc.Rel.fst"
let _44_2235 = (new_tvar r xs k_a)
in (match (_44_2235) with
| (gi_xs, gi) -> begin
(
# 1595 "FStar.Tc.Rel.fst"
let gi_xs = (FStar_Tc_Normalize.eta_expand env gi_xs)
in (
# 1596 "FStar.Tc.Rel.fst"
let gi_ps = (FStar_Absyn_Syntax.mk_Typ_app (gi, ps) (Some (k_a)) r)
in (
# 1597 "FStar.Tc.Rel.fst"
let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in (let _133_1146 = (FStar_Absyn_Syntax.targ gi_xs)
in (let _133_1145 = (FStar_Absyn_Syntax.targ gi_ps)
in (_133_1146, _133_1145, subst))))))
end)))
end
| FStar_Util.Inr (x) -> begin
(
# 1601 "FStar.Tc.Rel.fst"
let t_x = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (
# 1602 "FStar.Tc.Rel.fst"
let _44_2244 = (new_evar r xs t_x)
in (match (_44_2244) with
| (gi_xs, gi) -> begin
(
# 1603 "FStar.Tc.Rel.fst"
let gi_xs = (FStar_Tc_Normalize.eta_expand_exp env gi_xs)
in (
# 1604 "FStar.Tc.Rel.fst"
let gi_ps = (FStar_Absyn_Syntax.mk_Exp_app (gi, ps) (Some (t_x)) r)
in (
# 1605 "FStar.Tc.Rel.fst"
let subst = if (FStar_Absyn_Syntax.is_null_binder hd) then begin
subst
end else begin
(FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, gi_xs)))::subst
end
in (let _133_1148 = (FStar_Absyn_Syntax.varg gi_xs)
in (let _133_1147 = (FStar_Absyn_Syntax.varg gi_ps)
in (_133_1148, _133_1147, subst))))))
end)))
end)
in (match (_44_2251) with
| (gi_xs, gi_ps, subst) -> begin
(
# 1607 "FStar.Tc.Rel.fst"
let _44_2254 = (aux subst tl)
in (match (_44_2254) with
| (gi_xs', gi_ps') -> begin
((gi_xs)::gi_xs', (gi_ps)::gi_ps')
end))
end))
end))
in (aux [] bs))
end)))
in (match ((let _133_1150 = (let _133_1149 = (FStar_List.nth xs i)
in (FStar_All.pipe_left Prims.fst _133_1149))
in ((Prims.fst pi), _133_1150))) with
| (FStar_Util.Inl (pi), FStar_Util.Inl (xi)) -> begin
if (let _133_1151 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _133_1151)) then begin
None
end else begin
(
# 1615 "FStar.Tc.Rel.fst"
let _44_2263 = (gs xi.FStar_Absyn_Syntax.sort)
in (match (_44_2263) with
| (g_xs, _44_2262) -> begin
(
# 1616 "FStar.Tc.Rel.fst"
let xi = (FStar_Absyn_Util.btvar_to_typ xi)
in (
# 1617 "FStar.Tc.Rel.fst"
let proj = (let _133_1153 = (let _133_1152 = (FStar_Absyn_Syntax.mk_Typ_app' (xi, g_xs) (Some (FStar_Absyn_Syntax.ktype)) r)
in (xs, _133_1152))
in (FStar_Absyn_Syntax.mk_Typ_lam _133_1153 None r))
in (
# 1618 "FStar.Tc.Rel.fst"
let sub = (let _133_1159 = (let _133_1158 = (FStar_Absyn_Syntax.mk_Typ_app' (proj, ps) (Some (FStar_Absyn_Syntax.ktype)) r)
in (let _133_1157 = (let _133_1156 = (FStar_List.map (fun _44_2271 -> (match (_44_2271) with
| (_44_2267, _44_2269, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _133_1156))
in (mk_problem (p_scope orig) orig _133_1158 (p_rel orig) _133_1157 None "projection")))
in (FStar_All.pipe_left (fun _133_1154 -> TProb (_133_1154)) _133_1159))
in (
# 1620 "FStar.Tc.Rel.fst"
let _44_2273 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1161 = (FStar_Absyn_Print.typ_to_string proj)
in (let _133_1160 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _133_1161 _133_1160)))
end else begin
()
end
in (
# 1621 "FStar.Tc.Rel.fst"
let wl = (let _133_1163 = (let _133_1162 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_133_1162))
in (solve_prob orig _133_1163 ((UT ((u, proj)))::[]) wl))
in (let _133_1165 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _133_1164 -> Some (_133_1164)) _133_1165)))))))
end))
end
end
| _44_2277 -> begin
None
end))))
end)))
in (
# 1627 "FStar.Tc.Rel.fst"
let solve_t_flex_rigid = (fun orig lhs t2 wl -> (
# 1628 "FStar.Tc.Rel.fst"
let _44_2289 = lhs
in (match (_44_2289) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(
# 1629 "FStar.Tc.Rel.fst"
let subterms = (fun ps -> (
# 1630 "FStar.Tc.Rel.fst"
let xs = (let _133_1192 = (FStar_Absyn_Util.kind_formals k)
in (FStar_All.pipe_right _133_1192 Prims.fst))
in (
# 1631 "FStar.Tc.Rel.fst"
let xs = (FStar_Absyn_Util.name_binders xs)
in (let _133_1197 = (decompose_typ env t2)
in ((uv, k), ps, xs, _133_1197)))))
in (
# 1634 "FStar.Tc.Rel.fst"
let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
if (i = (- (1))) then begin
(match ((imitate_t orig env wl st)) with
| Failed (_44_2299) -> begin
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
in (
# 1645 "FStar.Tc.Rel.fst"
let check_head = (fun fvs1 t2 -> (
# 1646 "FStar.Tc.Rel.fst"
let _44_2315 = (FStar_Absyn_Util.head_and_args t2)
in (match (_44_2315) with
| (hd, _44_2314) -> begin
(match (hd.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| _44_2326 -> begin
(
# 1652 "FStar.Tc.Rel.fst"
let fvs_hd = (FStar_Absyn_Util.freevars_typ hd)
in if (FStar_Absyn_Util.fvs_included fvs_hd fvs1) then begin
true
end else begin
(
# 1655 "FStar.Tc.Rel.fst"
let _44_2328 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1208 = (FStar_Absyn_Print.freevars_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _133_1208))
end else begin
()
end
in false)
end)
end)
end)))
in (
# 1657 "FStar.Tc.Rel.fst"
let imitate_ok = (fun t2 -> (
# 1658 "FStar.Tc.Rel.fst"
let fvs_hd = (let _133_1212 = (let _133_1211 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _133_1211 Prims.fst))
in (FStar_All.pipe_right _133_1212 FStar_Absyn_Util.freevars_typ))
in if (FStar_Util.set_is_empty fvs_hd.FStar_Absyn_Syntax.ftvs) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(
# 1665 "FStar.Tc.Rel.fst"
let t1 = (sn env t1)
in (
# 1666 "FStar.Tc.Rel.fst"
let t2 = (sn env t2)
in (
# 1667 "FStar.Tc.Rel.fst"
let fvs1 = (FStar_Absyn_Util.freevars_typ t1)
in (
# 1668 "FStar.Tc.Rel.fst"
let fvs2 = (FStar_Absyn_Util.freevars_typ t2)
in (
# 1669 "FStar.Tc.Rel.fst"
let _44_2341 = (occurs_check env wl (uv, k) t2)
in (match (_44_2341) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _133_1214 = (let _133_1213 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _133_1213))
in (giveup_or_defer orig _133_1214))
end else begin
if (FStar_Absyn_Util.fvs_included fvs2 fvs1) then begin
if ((FStar_Absyn_Util.is_function_typ t2) && ((p_rel orig) <> EQ)) then begin
(let _133_1215 = (subterms args_lhs)
in (imitate_t orig env wl _133_1215))
end else begin
(
# 1676 "FStar.Tc.Rel.fst"
let _44_2342 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1218 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1217 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _133_1216 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _133_1218 _133_1217 _133_1216))))
end else begin
()
end
in (
# 1678 "FStar.Tc.Rel.fst"
let sol = (match (vars) with
| [] -> begin
t2
end
| _44_2346 -> begin
(let _133_1220 = (let _133_1219 = (sn_binders env vars)
in (_133_1219, t2))
in (FStar_Absyn_Syntax.mk_Typ_lam _133_1220 None t1.FStar_Absyn_Syntax.pos))
end)
in (
# 1681 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig None ((UT (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(
# 1686 "FStar.Tc.Rel.fst"
let _44_2349 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1223 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1222 = (FStar_Absyn_Print.freevars_to_string fvs1)
in (let _133_1221 = (FStar_Absyn_Print.freevars_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _133_1223 _133_1222 _133_1221))))
end else begin
()
end
in (let _133_1224 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _133_1224 (- (1)))))
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
if (let _133_1225 = (FStar_Absyn_Util.freevars_typ t1)
in (check_head _133_1225 t2)) then begin
(
# 1697 "FStar.Tc.Rel.fst"
let im_ok = (imitate_ok t2)
in (
# 1698 "FStar.Tc.Rel.fst"
let _44_2353 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1226 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _133_1226 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _133_1227 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _133_1227 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (
# 1722 "FStar.Tc.Rel.fst"
let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(
# 1725 "FStar.Tc.Rel.fst"
let force_quasi_pattern = (fun xs_opt _44_2365 -> (match (_44_2365) with
| (t, u, k, args) -> begin
(
# 1726 "FStar.Tc.Rel.fst"
let rec aux = (fun binders ys args -> (match (args) with
| [] -> begin
(
# 1728 "FStar.Tc.Rel.fst"
let ys = (FStar_List.rev ys)
in (
# 1729 "FStar.Tc.Rel.fst"
let binders = (FStar_List.rev binders)
in (
# 1730 "FStar.Tc.Rel.fst"
let kk = (FStar_Tc_Recheck.recompute_kind t)
in (
# 1731 "FStar.Tc.Rel.fst"
let _44_2377 = (new_tvar t.FStar_Absyn_Syntax.pos ys kk)
in (match (_44_2377) with
| (t', _44_2376) -> begin
(
# 1732 "FStar.Tc.Rel.fst"
let _44_2383 = (destruct_flex_t t')
in (match (_44_2383) with
| (u1_ys, u1, k1, _44_2382) -> begin
(
# 1733 "FStar.Tc.Rel.fst"
let sol = (let _133_1245 = (let _133_1244 = (FStar_Absyn_Syntax.mk_Typ_lam (binders, u1_ys) (Some (k)) t.FStar_Absyn_Syntax.pos)
in ((u, k), _133_1244))
in UT (_133_1245))
in (sol, (t', u, k1, ys)))
end))
end)))))
end
| hd::tl -> begin
(
# 1737 "FStar.Tc.Rel.fst"
let new_binder = (fun hd -> (match ((Prims.fst hd)) with
| FStar_Util.Inl (a) -> begin
(let _133_1249 = (let _133_1248 = (FStar_Tc_Recheck.recompute_kind a)
in (FStar_All.pipe_right _133_1248 (FStar_Absyn_Util.gen_bvar_p a.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _133_1249 FStar_Absyn_Syntax.t_binder))
end
| FStar_Util.Inr (x) -> begin
(let _133_1251 = (let _133_1250 = (FStar_Tc_Recheck.recompute_typ x)
in (FStar_All.pipe_right _133_1250 (FStar_Absyn_Util.gen_bvar_p x.FStar_Absyn_Syntax.pos)))
in (FStar_All.pipe_right _133_1251 FStar_Absyn_Syntax.v_binder))
end))
in (
# 1741 "FStar.Tc.Rel.fst"
let _44_2402 = (match ((pat_var_opt env ys hd)) with
| None -> begin
(let _133_1252 = (new_binder hd)
in (_133_1252, ys))
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
(let _133_1253 = (new_binder hd)
in (_133_1253, ys))
end
end)
end)
in (match (_44_2402) with
| (binder, ys) -> begin
(aux ((binder)::binders) ys tl)
end)))
end))
in (aux [] [] args))
end))
in (
# 1759 "FStar.Tc.Rel.fst"
let solve_both_pats = (fun wl _44_2408 _44_2412 k r -> (match ((_44_2408, _44_2412)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _133_1264 = (solve_prob orig None [] wl)
in (solve env _133_1264))
end else begin
(
# 1766 "FStar.Tc.Rel.fst"
let xs = (sn_binders env xs)
in (
# 1767 "FStar.Tc.Rel.fst"
let ys = (sn_binders env ys)
in (
# 1768 "FStar.Tc.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 1769 "FStar.Tc.Rel.fst"
let _44_2421 = (new_tvar r zs k)
in (match (_44_2421) with
| (u_zs, _44_2420) -> begin
(
# 1770 "FStar.Tc.Rel.fst"
let sub1 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, u_zs) (Some (k1)) r)
in (
# 1771 "FStar.Tc.Rel.fst"
let _44_2425 = (occurs_check env wl (u1, k1) sub1)
in (match (_44_2425) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(
# 1774 "FStar.Tc.Rel.fst"
let sol1 = UT (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1776 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(
# 1778 "FStar.Tc.Rel.fst"
let sub2 = (FStar_Absyn_Syntax.mk_Typ_lam' (ys, u_zs) (Some (k2)) r)
in (
# 1779 "FStar.Tc.Rel.fst"
let _44_2431 = (occurs_check env wl (u2, k2) sub2)
in (match (_44_2431) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(
# 1782 "FStar.Tc.Rel.fst"
let sol2 = UT (((u2, k2), sub2))
in (
# 1783 "FStar.Tc.Rel.fst"
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
# 1786 "FStar.Tc.Rel.fst"
let solve_one_pat = (fun _44_2439 _44_2444 -> (match ((_44_2439, _44_2444)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(
# 1788 "FStar.Tc.Rel.fst"
let _44_2445 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1270 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1269 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _133_1270 _133_1269)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(
# 1791 "FStar.Tc.Rel.fst"
let sub_probs = (FStar_List.map2 (fun a b -> (
# 1792 "FStar.Tc.Rel.fst"
let a = (FStar_Absyn_Util.arg_of_non_null_binder a)
in (match (((Prims.fst a), (Prims.fst b))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _133_1274 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _133_1274 (fun _133_1273 -> TProb (_133_1273))))
end
| (FStar_Util.Inr (t1), FStar_Util.Inr (t2)) -> begin
(let _133_1276 = (mk_problem (p_scope orig) orig t1 EQ t2 None "flex-flex index")
in (FStar_All.pipe_right _133_1276 (fun _133_1275 -> EProb (_133_1275))))
end
| _44_2461 -> begin
(FStar_All.failwith "Impossible")
end))) xs args2)
in (
# 1797 "FStar.Tc.Rel.fst"
let guard = (let _133_1278 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _133_1278))
in (
# 1798 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(
# 1801 "FStar.Tc.Rel.fst"
let t2 = (sn env t2)
in (
# 1802 "FStar.Tc.Rel.fst"
let rhs_vars = (FStar_Absyn_Util.freevars_typ t2)
in (
# 1803 "FStar.Tc.Rel.fst"
let _44_2471 = (occurs_check env wl (u1, k1) t2)
in (match (_44_2471) with
| (occurs_ok, _44_2470) -> begin
(
# 1804 "FStar.Tc.Rel.fst"
let lhs_vars = (FStar_Absyn_Syntax.freevars_of_binders xs)
in if (occurs_ok && (FStar_Absyn_Util.fvs_included rhs_vars lhs_vars)) then begin
(
# 1806 "FStar.Tc.Rel.fst"
let sol = (let _133_1280 = (let _133_1279 = (FStar_Absyn_Syntax.mk_Typ_lam' (xs, t2) (Some (k1)) t1.FStar_Absyn_Syntax.pos)
in ((u1, k1), _133_1279))
in UT (_133_1280))
in (
# 1807 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(
# 1810 "FStar.Tc.Rel.fst"
let _44_2482 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_44_2482) with
| (sol, (_44_2477, u2, k2, ys)) -> begin
(
# 1811 "FStar.Tc.Rel.fst"
let wl = (extend_solution sol wl)
in (
# 1812 "FStar.Tc.Rel.fst"
let _44_2484 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _133_1281 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _133_1281))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _44_2489 -> begin
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
# 1819 "FStar.Tc.Rel.fst"
let _44_2494 = lhs
in (match (_44_2494) with
| (t1, u1, k1, args1) -> begin
(
# 1820 "FStar.Tc.Rel.fst"
let _44_2499 = rhs
in (match (_44_2499) with
| (t2, u2, k2, args2) -> begin
(
# 1821 "FStar.Tc.Rel.fst"
let maybe_pat_vars1 = (pat_vars env [] args1)
in (
# 1822 "FStar.Tc.Rel.fst"
let maybe_pat_vars2 = (pat_vars env [] args2)
in (
# 1823 "FStar.Tc.Rel.fst"
let r = t2.FStar_Absyn_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(let _133_1282 = (FStar_Tc_Recheck.recompute_kind t2)
in (solve_both_pats wl (u1, k1, xs) (u2, k2, ys) _133_1282 t2.FStar_Absyn_Syntax.pos))
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _44_2517 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(
# 1831 "FStar.Tc.Rel.fst"
let _44_2521 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_44_2521) with
| (sol, _44_2520) -> begin
(
# 1832 "FStar.Tc.Rel.fst"
let wl = (extend_solution sol wl)
in (
# 1833 "FStar.Tc.Rel.fst"
let _44_2523 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _133_1283 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _133_1283))
end else begin
()
end
in (match (orig) with
| TProb (p) -> begin
(solve_t env p wl)
end
| _44_2528 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (
# 1839 "FStar.Tc.Rel.fst"
let orig = TProb (problem)
in if (FStar_Util.physical_equality problem.lhs problem.rhs) then begin
(let _133_1284 = (solve_prob orig None [] wl)
in (solve env _133_1284))
end else begin
(
# 1841 "FStar.Tc.Rel.fst"
let t1 = problem.lhs
in (
# 1842 "FStar.Tc.Rel.fst"
let t2 = problem.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _133_1285 = (solve_prob orig None [] wl)
in (solve env _133_1285))
end else begin
(
# 1844 "FStar.Tc.Rel.fst"
let _44_2532 = if (FStar_Tc_Env.debug env (FStar_Options.Other ("Rel"))) then begin
(let _133_1288 = (prob_to_string env orig)
in (let _133_1287 = (let _133_1286 = (FStar_List.map (uvi_to_string wl.tcenv) wl.subst)
in (FStar_All.pipe_right _133_1286 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Attempting %s\n\tSubst is %s\n" _133_1288 _133_1287)))
end else begin
()
end
in (
# 1847 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 1849 "FStar.Tc.Rel.fst"
let match_num_binders = (fun _44_2537 _44_2540 -> (match ((_44_2537, _44_2540)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(
# 1851 "FStar.Tc.Rel.fst"
let curry = (fun n bs mk_cod -> (
# 1852 "FStar.Tc.Rel.fst"
let _44_2547 = (FStar_Util.first_N n bs)
in (match (_44_2547) with
| (bs, rest) -> begin
(let _133_1318 = (mk_cod rest)
in (bs, _133_1318))
end)))
in (
# 1855 "FStar.Tc.Rel.fst"
let l1 = (FStar_List.length bs1)
in (
# 1856 "FStar.Tc.Rel.fst"
let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _133_1322 = (let _133_1319 = (mk_cod1 [])
in (bs1, _133_1319))
in (let _133_1321 = (let _133_1320 = (mk_cod2 [])
in (bs2, _133_1320))
in (_133_1322, _133_1321)))
end else begin
if (l1 > l2) then begin
(let _133_1325 = (curry l2 bs1 mk_cod1)
in (let _133_1324 = (let _133_1323 = (mk_cod2 [])
in (bs2, _133_1323))
in (_133_1325, _133_1324)))
end else begin
(let _133_1328 = (let _133_1326 = (mk_cod1 [])
in (bs1, _133_1326))
in (let _133_1327 = (curry l1 bs2 mk_cod2)
in (_133_1328, _133_1327)))
end
end)))
end))
in (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Typ_btvar (a), FStar_Absyn_Syntax.Typ_btvar (b)) -> begin
if (FStar_Absyn_Util.bvd_eq a.FStar_Absyn_Syntax.v b.FStar_Absyn_Syntax.v) then begin
(let _133_1329 = (solve_prob orig None [] wl)
in (solve env _133_1329))
end else begin
(let _133_1333 = (let _133_1332 = (let _133_1331 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _133_1330 -> Some (_133_1330)) _133_1331))
in (solve_prob orig _133_1332 [] wl))
in (solve env _133_1333))
end
end
| (FStar_Absyn_Syntax.Typ_fun (bs1, c1), FStar_Absyn_Syntax.Typ_fun (bs2, c2)) -> begin
(
# 1873 "FStar.Tc.Rel.fst"
let mk_c = (fun c _44_31 -> (match (_44_31) with
| [] -> begin
c
end
| bs -> begin
(let _133_1338 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None c.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Total _133_1338))
end))
in (
# 1876 "FStar.Tc.Rel.fst"
let _44_2578 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_44_2578) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1880 "FStar.Tc.Rel.fst"
let c1 = (FStar_Absyn_Util.subst_comp subst c1)
in (
# 1881 "FStar.Tc.Rel.fst"
let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
EQ
end else begin
problem.relation
end
in (
# 1882 "FStar.Tc.Rel.fst"
let _44_2584 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(let _133_1345 = (let _133_1344 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_right _133_1344 FStar_Range.string_of_range))
in (FStar_Util.print2 "(%s) Using relation %s at higher order\n" _133_1345 (rel_to_string rel)))
end else begin
()
end
in (let _133_1347 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _133_1346 -> CProb (_133_1346)) _133_1347)))))))
end)))
end
| (FStar_Absyn_Syntax.Typ_lam (bs1, t1'), FStar_Absyn_Syntax.Typ_lam (bs2, t2')) -> begin
(
# 1887 "FStar.Tc.Rel.fst"
let mk_t = (fun t _44_32 -> (match (_44_32) with
| [] -> begin
t
end
| bs -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end))
in (
# 1890 "FStar.Tc.Rel.fst"
let _44_2606 = (match_num_binders (bs1, (mk_t t1')) (bs2, (mk_t t2')))
in (match (_44_2606) with
| ((bs1, t1'), (bs2, t2')) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (
# 1894 "FStar.Tc.Rel.fst"
let t1' = (FStar_Absyn_Util.subst_typ subst t1')
in (let _133_1358 = (mk_problem scope orig t1' problem.relation t2' None "lambda co-domain")
in (FStar_All.pipe_left (fun _133_1357 -> TProb (_133_1357)) _133_1358)))))
end)))
end
| (FStar_Absyn_Syntax.Typ_refine (_44_2612), FStar_Absyn_Syntax.Typ_refine (_44_2615)) -> begin
(
# 1898 "FStar.Tc.Rel.fst"
let _44_2620 = (as_refinement env wl t1)
in (match (_44_2620) with
| (x1, phi1) -> begin
(
# 1899 "FStar.Tc.Rel.fst"
let _44_2623 = (as_refinement env wl t2)
in (match (_44_2623) with
| (x2, phi2) -> begin
(
# 1900 "FStar.Tc.Rel.fst"
let base_prob = (let _133_1360 = (mk_problem (p_scope orig) orig x1.FStar_Absyn_Syntax.sort problem.relation x2.FStar_Absyn_Syntax.sort problem.element "refinement base type")
in (FStar_All.pipe_left (fun _133_1359 -> TProb (_133_1359)) _133_1360))
in (
# 1901 "FStar.Tc.Rel.fst"
let x1_for_x2 = (let _133_1362 = (FStar_Absyn_Syntax.v_binder x1)
in (let _133_1361 = (FStar_Absyn_Syntax.v_binder x2)
in (FStar_Absyn_Util.mk_subst_one_binder _133_1362 _133_1361)))
in (
# 1902 "FStar.Tc.Rel.fst"
let phi2 = (FStar_Absyn_Util.subst_typ x1_for_x2 phi2)
in (
# 1903 "FStar.Tc.Rel.fst"
let mk_imp = (fun imp phi1 phi2 -> (let _133_1379 = (imp phi1 phi2)
in (FStar_All.pipe_right _133_1379 (guard_on_element problem x1))))
in (
# 1904 "FStar.Tc.Rel.fst"
let fallback = (fun _44_2632 -> (match (()) with
| () -> begin
(
# 1905 "FStar.Tc.Rel.fst"
let impl = if (problem.relation = EQ) then begin
(mk_imp FStar_Absyn_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Absyn_Util.mk_imp phi1 phi2)
end
in (
# 1909 "FStar.Tc.Rel.fst"
let guard = (let _133_1382 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _133_1382 impl))
in (
# 1910 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.relation = EQ) then begin
(
# 1913 "FStar.Tc.Rel.fst"
let ref_prob = (let _133_1384 = (mk_problem (p_scope orig) orig phi1 EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _133_1383 -> TProb (_133_1383)) _133_1384))
in (match ((solve env (
# 1914 "FStar.Tc.Rel.fst"
let _44_2637 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; subst = _44_2637.subst; ctr = _44_2637.ctr; slack_vars = _44_2637.slack_vars; defer_ok = false; smt_ok = _44_2637.smt_ok; tcenv = _44_2637.tcenv}))) with
| Failed (_44_2640) -> begin
(fallback ())
end
| Success (subst, _44_2644) -> begin
(
# 1919 "FStar.Tc.Rel.fst"
let guard = (let _133_1387 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _133_1386 = (let _133_1385 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _133_1385 (guard_on_element problem x1)))
in (FStar_Absyn_Util.mk_conj _133_1387 _133_1386)))
in (
# 1920 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (
# 1921 "FStar.Tc.Rel.fst"
let wl = (
# 1921 "FStar.Tc.Rel.fst"
let _44_2649 = wl
in {attempting = _44_2649.attempting; wl_deferred = _44_2649.wl_deferred; subst = subst; ctr = (wl.ctr + 1); slack_vars = _44_2649.slack_vars; defer_ok = _44_2649.defer_ok; smt_ok = _44_2649.smt_ok; tcenv = _44_2649.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end)))))
end))
end))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_uvar (_))) | ((FStar_Absyn_Syntax.Typ_uvar (_), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _133_1389 = (destruct_flex_t t1)
in (let _133_1388 = (destruct_flex_t t2)
in (flex_flex orig _133_1389 _133_1388)))
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) when (problem.relation = EQ) -> begin
(let _133_1390 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _133_1390 t2 wl))
end
| ((_, FStar_Absyn_Syntax.Typ_uvar (_))) | ((_, FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) when (problem.relation = EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Absyn_Syntax.Typ_uvar (_), _)) | ((FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(
# 1949 "FStar.Tc.Rel.fst"
let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
EQ
end else begin
problem.relation
end
in if (let _133_1391 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _133_1391)) then begin
(let _133_1394 = (FStar_All.pipe_left (fun _133_1392 -> TProb (_133_1392)) (
# 1951 "FStar.Tc.Rel.fst"
let _44_2808 = problem
in {lhs = _44_2808.lhs; relation = new_rel; rhs = _44_2808.rhs; element = _44_2808.element; logical_guard = _44_2808.logical_guard; scope = _44_2808.scope; reason = _44_2808.reason; loc = _44_2808.loc; rank = _44_2808.rank}))
in (let _133_1393 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _133_1394 _133_1393 t2 wl)))
end else begin
(
# 1952 "FStar.Tc.Rel.fst"
let _44_2812 = (base_and_refinement env wl t2)
in (match (_44_2812) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _133_1397 = (FStar_All.pipe_left (fun _133_1395 -> TProb (_133_1395)) (
# 1955 "FStar.Tc.Rel.fst"
let _44_2814 = problem
in {lhs = _44_2814.lhs; relation = new_rel; rhs = _44_2814.rhs; element = _44_2814.element; logical_guard = _44_2814.logical_guard; scope = _44_2814.scope; reason = _44_2814.reason; loc = _44_2814.loc; rank = _44_2814.rank}))
in (let _133_1396 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _133_1397 _133_1396 t_base wl)))
end
| Some (y, phi) -> begin
(
# 1958 "FStar.Tc.Rel.fst"
let y' = (
# 1958 "FStar.Tc.Rel.fst"
let _44_2820 = y
in {FStar_Absyn_Syntax.v = _44_2820.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t1; FStar_Absyn_Syntax.p = _44_2820.FStar_Absyn_Syntax.p})
in (
# 1959 "FStar.Tc.Rel.fst"
let impl = (guard_on_element problem y' phi)
in (
# 1960 "FStar.Tc.Rel.fst"
let base_prob = (let _133_1399 = (mk_problem problem.scope orig t1 new_rel y.FStar_Absyn_Syntax.sort problem.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _133_1398 -> TProb (_133_1398)) _133_1399))
in (
# 1962 "FStar.Tc.Rel.fst"
let guard = (let _133_1400 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _133_1400 impl))
in (
# 1963 "FStar.Tc.Rel.fst"
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
# 1972 "FStar.Tc.Rel.fst"
let _44_2855 = (base_and_refinement env wl t1)
in (match (_44_2855) with
| (t_base, _44_2854) -> begin
(solve_t env (
# 1973 "FStar.Tc.Rel.fst"
let _44_2856 = problem
in {lhs = t_base; relation = EQ; rhs = _44_2856.rhs; element = _44_2856.element; logical_guard = _44_2856.logical_guard; scope = _44_2856.scope; reason = _44_2856.reason; loc = _44_2856.loc; rank = _44_2856.rank}) wl)
end))
end
end
| (FStar_Absyn_Syntax.Typ_refine (_44_2859), _44_2862) -> begin
(
# 1976 "FStar.Tc.Rel.fst"
let t2 = (let _133_1401 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _133_1401))
in (solve_t env (
# 1977 "FStar.Tc.Rel.fst"
let _44_2865 = problem
in {lhs = _44_2865.lhs; relation = _44_2865.relation; rhs = t2; element = _44_2865.element; logical_guard = _44_2865.logical_guard; scope = _44_2865.scope; reason = _44_2865.reason; loc = _44_2865.loc; rank = _44_2865.rank}) wl))
end
| (_44_2868, FStar_Absyn_Syntax.Typ_refine (_44_2870)) -> begin
(
# 1980 "FStar.Tc.Rel.fst"
let t1 = (let _133_1402 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _133_1402))
in (solve_t env (
# 1981 "FStar.Tc.Rel.fst"
let _44_2874 = problem
in {lhs = t1; relation = _44_2874.relation; rhs = _44_2874.rhs; element = _44_2874.element; logical_guard = _44_2874.logical_guard; scope = _44_2874.scope; reason = _44_2874.reason; loc = _44_2874.loc; rank = _44_2874.rank}) wl))
end
| ((FStar_Absyn_Syntax.Typ_btvar (_), _)) | ((FStar_Absyn_Syntax.Typ_const (_), _)) | ((FStar_Absyn_Syntax.Typ_app (_), _)) | ((_, FStar_Absyn_Syntax.Typ_btvar (_))) | ((_, FStar_Absyn_Syntax.Typ_const (_))) | ((_, FStar_Absyn_Syntax.Typ_app (_))) -> begin
(
# 1989 "FStar.Tc.Rel.fst"
let _44_2914 = (head_matches_delta env wl t1 t2)
in (match (_44_2914) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _44_2917) -> begin
(
# 1992 "FStar.Tc.Rel.fst"
let head1 = (let _133_1403 = (FStar_Absyn_Util.head_and_args t1)
in (FStar_All.pipe_right _133_1403 Prims.fst))
in (
# 1993 "FStar.Tc.Rel.fst"
let head2 = (let _133_1404 = (FStar_Absyn_Util.head_and_args t2)
in (FStar_All.pipe_right _133_1404 Prims.fst))
in (
# 1994 "FStar.Tc.Rel.fst"
let may_equate = (fun head -> (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_44_2924) -> begin
true
end
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Tc_Env.is_projector env tc.FStar_Absyn_Syntax.v)
end
| _44_2929 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _133_1410 = (let _133_1409 = (let _133_1408 = (FStar_Absyn_Util.mk_eq_typ t1 t2)
in (FStar_All.pipe_left (fun _133_1407 -> Some (_133_1407)) _133_1408))
in (solve_prob orig _133_1409 [] wl))
in (solve env _133_1410))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_44_2931, Some (t1, t2)) -> begin
(solve_t env (
# 2004 "FStar.Tc.Rel.fst"
let _44_2937 = problem
in {lhs = t1; relation = _44_2937.relation; rhs = t2; element = _44_2937.element; logical_guard = _44_2937.logical_guard; scope = _44_2937.scope; reason = _44_2937.reason; loc = _44_2937.loc; rank = _44_2937.rank}) wl)
end
| (_44_2940, None) -> begin
(
# 2007 "FStar.Tc.Rel.fst"
let _44_2943 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1412 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1411 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "Head matches: %s and %s\n" _133_1412 _133_1411)))
end else begin
()
end
in (
# 2008 "FStar.Tc.Rel.fst"
let _44_2947 = (FStar_Absyn_Util.head_and_args t1)
in (match (_44_2947) with
| (head, args) -> begin
(
# 2009 "FStar.Tc.Rel.fst"
let _44_2950 = (FStar_Absyn_Util.head_and_args t2)
in (match (_44_2950) with
| (head', args') -> begin
(
# 2010 "FStar.Tc.Rel.fst"
let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _133_1417 = (let _133_1416 = (FStar_Absyn_Print.typ_to_string head)
in (let _133_1415 = (FStar_Absyn_Print.args_to_string args)
in (let _133_1414 = (FStar_Absyn_Print.typ_to_string head')
in (let _133_1413 = (FStar_Absyn_Print.args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _133_1416 _133_1415 _133_1414 _133_1413)))))
in (giveup env _133_1417 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(let _133_1418 = (solve_prob orig None [] wl)
in (solve env _133_1418))
end else begin
(
# 2028 "FStar.Tc.Rel.fst"
let _44_2954 = (base_and_refinement env wl t1)
in (match (_44_2954) with
| (base1, refinement1) -> begin
(
# 2029 "FStar.Tc.Rel.fst"
let _44_2957 = (base_and_refinement env wl t2)
in (match (_44_2957) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(
# 2032 "FStar.Tc.Rel.fst"
let _44_2961 = if ((head_matches head head) <> FullMatch) then begin
(let _133_1421 = (let _133_1420 = (FStar_Absyn_Print.typ_to_string head)
in (let _133_1419 = (FStar_Absyn_Print.typ_to_string head')
in (FStar_Util.format2 "Assertion failed: expected full match of %s and %s\n" _133_1420 _133_1419)))
in (FStar_All.failwith _133_1421))
end else begin
()
end
in (
# 2034 "FStar.Tc.Rel.fst"
let subprobs = (FStar_List.map2 (fun a a' -> (match (((Prims.fst a), (Prims.fst a'))) with
| (FStar_Util.Inl (t), FStar_Util.Inl (t')) -> begin
(let _133_1425 = (mk_problem (p_scope orig) orig t EQ t' None "type index")
in (FStar_All.pipe_left (fun _133_1424 -> TProb (_133_1424)) _133_1425))
end
| (FStar_Util.Inr (v), FStar_Util.Inr (v')) -> begin
(let _133_1427 = (mk_problem (p_scope orig) orig v EQ v' None "term index")
in (FStar_All.pipe_left (fun _133_1426 -> EProb (_133_1426)) _133_1427))
end
| _44_2976 -> begin
(FStar_All.failwith "Impossible")
end)) args args')
in (
# 2040 "FStar.Tc.Rel.fst"
let formula = (let _133_1429 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Absyn_Util.mk_conj_l _133_1429))
in (
# 2041 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl))))))
end
| _44_2982 -> begin
(
# 2045 "FStar.Tc.Rel.fst"
let lhs = (force_refinement (base1, refinement1))
in (
# 2046 "FStar.Tc.Rel.fst"
let rhs = (force_refinement (base2, refinement2))
in (solve_t env (
# 2047 "FStar.Tc.Rel.fst"
let _44_2985 = problem
in {lhs = lhs; relation = _44_2985.relation; rhs = rhs; element = _44_2985.element; logical_guard = _44_2985.logical_guard; scope = _44_2985.scope; reason = _44_2985.reason; loc = _44_2985.loc; rank = _44_2985.rank}) wl)))
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
| _44_3024 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.comp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 2061 "FStar.Tc.Rel.fst"
let c1 = problem.lhs
in (
# 2062 "FStar.Tc.Rel.fst"
let c2 = problem.rhs
in (
# 2063 "FStar.Tc.Rel.fst"
let orig = CProb (problem)
in (
# 2064 "FStar.Tc.Rel.fst"
let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (
# 2066 "FStar.Tc.Rel.fst"
let solve_eq = (fun c1_comp c2_comp -> (
# 2067 "FStar.Tc.Rel.fst"
let _44_3041 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (
# 2069 "FStar.Tc.Rel.fst"
let sub_probs = (FStar_List.map2 (fun arg1 arg2 -> (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _133_1444 = (sub_prob t1 EQ t2 "effect arg")
in (FStar_All.pipe_left (fun _133_1443 -> TProb (_133_1443)) _133_1444))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _133_1446 = (sub_prob e1 EQ e2 "effect arg")
in (FStar_All.pipe_left (fun _133_1445 -> EProb (_133_1445)) _133_1446))
end
| _44_3056 -> begin
(FStar_All.failwith "impossible")
end)) c1_comp.FStar_Absyn_Syntax.effect_args c2_comp.FStar_Absyn_Syntax.effect_args)
in (
# 2073 "FStar.Tc.Rel.fst"
let guard = (let _133_1448 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Absyn_Util.mk_conj_l _133_1448))
in (
# 2074 "FStar.Tc.Rel.fst"
let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _133_1449 = (solve_prob orig None [] wl)
in (solve env _133_1449))
end else begin
(
# 2078 "FStar.Tc.Rel.fst"
let _44_3061 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1451 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _133_1450 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _133_1451 (rel_to_string problem.relation) _133_1450)))
end else begin
()
end
in (
# 2079 "FStar.Tc.Rel.fst"
let r = (FStar_Tc_Env.get_range env)
in (
# 2080 "FStar.Tc.Rel.fst"
let _44_3066 = (c1, c2)
in (match (_44_3066) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Absyn_Syntax.n, c2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Total (t1), FStar_Absyn_Syntax.Total (t2)) -> begin
(solve_t env (problem_using_guard orig t1 problem.relation t2 None "result type") wl)
end
| (FStar_Absyn_Syntax.Total (_44_3073), FStar_Absyn_Syntax.Comp (_44_3076)) -> begin
(let _133_1453 = (
# 2086 "FStar.Tc.Rel.fst"
let _44_3079 = problem
in (let _133_1452 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c1))
in {lhs = _133_1452; relation = _44_3079.relation; rhs = _44_3079.rhs; element = _44_3079.element; logical_guard = _44_3079.logical_guard; scope = _44_3079.scope; reason = _44_3079.reason; loc = _44_3079.loc; rank = _44_3079.rank}))
in (solve_c env _133_1453 wl))
end
| (FStar_Absyn_Syntax.Comp (_44_3082), FStar_Absyn_Syntax.Total (_44_3085)) -> begin
(let _133_1455 = (
# 2088 "FStar.Tc.Rel.fst"
let _44_3088 = problem
in (let _133_1454 = (FStar_All.pipe_left FStar_Absyn_Syntax.mk_Comp (FStar_Absyn_Util.comp_to_comp_typ c2))
in {lhs = _44_3088.lhs; relation = _44_3088.relation; rhs = _133_1454; element = _44_3088.element; logical_guard = _44_3088.logical_guard; scope = _44_3088.scope; reason = _44_3088.reason; loc = _44_3088.loc; rank = _44_3088.rank}))
in (solve_c env _133_1455 wl))
end
| (FStar_Absyn_Syntax.Comp (_44_3091), FStar_Absyn_Syntax.Comp (_44_3094)) -> begin
if (((FStar_Absyn_Util.is_ml_comp c1) && (FStar_Absyn_Util.is_ml_comp c2)) || ((FStar_Absyn_Util.is_total_comp c1) && ((FStar_Absyn_Util.is_total_comp c2) || (FStar_Absyn_Util.is_ml_comp c2)))) then begin
(solve_t env (problem_using_guard orig (FStar_Absyn_Util.comp_result c1) problem.relation (FStar_Absyn_Util.comp_result c2) None "result type") wl)
end else begin
(
# 2094 "FStar.Tc.Rel.fst"
let c1_comp = (FStar_Absyn_Util.comp_to_comp_typ c1)
in (
# 2095 "FStar.Tc.Rel.fst"
let c2_comp = (FStar_Absyn_Util.comp_to_comp_typ c2)
in if ((problem.relation = EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Absyn_Syntax.effect_name c2_comp.FStar_Absyn_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(
# 2099 "FStar.Tc.Rel.fst"
let c1 = (FStar_Tc_Normalize.weak_norm_comp env c1)
in (
# 2100 "FStar.Tc.Rel.fst"
let c2 = (FStar_Tc_Normalize.weak_norm_comp env c2)
in (
# 2101 "FStar.Tc.Rel.fst"
let _44_3101 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Absyn_Syntax.effect_name.FStar_Ident.str c2.FStar_Absyn_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_Tc_Env.monad_leq env c1.FStar_Absyn_Syntax.effect_name c2.FStar_Absyn_Syntax.effect_name)) with
| None -> begin
(let _133_1458 = (let _133_1457 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _133_1456 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _133_1457 _133_1456)))
in (giveup env _133_1458 orig))
end
| Some (edge) -> begin
if (problem.relation = EQ) then begin
(
# 2106 "FStar.Tc.Rel.fst"
let _44_3121 = (match (c1.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (wp1), _44_3114)::(FStar_Util.Inl (wlp1), _44_3109)::[] -> begin
(wp1, wlp1)
end
| _44_3118 -> begin
(let _133_1461 = (let _133_1460 = (let _133_1459 = (FStar_Absyn_Syntax.range_of_lid c1.FStar_Absyn_Syntax.effect_name)
in (FStar_Range.string_of_range _133_1459))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _133_1460))
in (FStar_All.failwith _133_1461))
end)
in (match (_44_3121) with
| (wp, wlp) -> begin
(
# 2109 "FStar.Tc.Rel.fst"
let c1 = (let _133_1467 = (let _133_1466 = (let _133_1462 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wp)
in (FStar_Absyn_Syntax.targ _133_1462))
in (let _133_1465 = (let _133_1464 = (let _133_1463 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wlp)
in (FStar_Absyn_Syntax.targ _133_1463))
in (_133_1464)::[])
in (_133_1466)::_133_1465))
in {FStar_Absyn_Syntax.effect_name = c2.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = c1.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _133_1467; FStar_Absyn_Syntax.flags = c1.FStar_Absyn_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(
# 2116 "FStar.Tc.Rel.fst"
let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _44_33 -> (match (_44_33) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.MLEFFECT) | (FStar_Absyn_Syntax.SOMETRIVIAL) -> begin
true
end
| _44_3128 -> begin
false
end))))
in (
# 2117 "FStar.Tc.Rel.fst"
let _44_3151 = (match ((c1.FStar_Absyn_Syntax.effect_args, c2.FStar_Absyn_Syntax.effect_args)) with
| ((FStar_Util.Inl (wp1), _44_3135)::_44_3131, (FStar_Util.Inl (wp2), _44_3143)::_44_3139) -> begin
(wp1, wp2)
end
| _44_3148 -> begin
(let _133_1471 = (let _133_1470 = (FStar_Absyn_Print.sli c1.FStar_Absyn_Syntax.effect_name)
in (let _133_1469 = (FStar_Absyn_Print.sli c2.FStar_Absyn_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _133_1470 _133_1469)))
in (FStar_All.failwith _133_1471))
end)
in (match (_44_3151) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(solve_t env (problem_using_guard orig c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ None "result type") wl)
end else begin
(
# 2122 "FStar.Tc.Rel.fst"
let c2_decl = (FStar_Tc_Env.get_effect_decl env c2.FStar_Absyn_Syntax.effect_name)
in (
# 2123 "FStar.Tc.Rel.fst"
let g = if is_null_wp_2 then begin
(
# 2125 "FStar.Tc.Rel.fst"
let _44_3153 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _133_1477 = (let _133_1476 = (let _133_1475 = (FStar_Absyn_Syntax.targ c1.FStar_Absyn_Syntax.result_typ)
in (let _133_1474 = (let _133_1473 = (let _133_1472 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _133_1472))
in (_133_1473)::[])
in (_133_1475)::_133_1474))
in (c2_decl.FStar_Absyn_Syntax.trivial, _133_1476))
in (FStar_Absyn_Syntax.mk_Typ_app _133_1477 (Some (FStar_Absyn_Syntax.ktype)) r)))
end else begin
(
# 2127 "FStar.Tc.Rel.fst"
let wp2_imp_wp1 = (let _133_1489 = (let _133_1488 = (let _133_1487 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _133_1486 = (let _133_1485 = (FStar_Absyn_Syntax.targ wpc2)
in (let _133_1484 = (let _133_1483 = (let _133_1479 = (let _133_1478 = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.ftv FStar_Absyn_Const.imp_lid _133_1478))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _133_1479))
in (let _133_1482 = (let _133_1481 = (let _133_1480 = (edge.FStar_Tc_Env.mlift c1.FStar_Absyn_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _133_1480))
in (_133_1481)::[])
in (_133_1483)::_133_1482))
in (_133_1485)::_133_1484))
in (_133_1487)::_133_1486))
in (c2_decl.FStar_Absyn_Syntax.wp_binop, _133_1488))
in (FStar_Absyn_Syntax.mk_Typ_app _133_1489 None r))
in (let _133_1494 = (let _133_1493 = (let _133_1492 = (FStar_Absyn_Syntax.targ c2.FStar_Absyn_Syntax.result_typ)
in (let _133_1491 = (let _133_1490 = (FStar_Absyn_Syntax.targ wp2_imp_wp1)
in (_133_1490)::[])
in (_133_1492)::_133_1491))
in (c2_decl.FStar_Absyn_Syntax.wp_as_type, _133_1493))
in (FStar_Absyn_Syntax.mk_Typ_app _133_1494 (Some (FStar_Absyn_Syntax.ktype)) r)))
end
in (
# 2133 "FStar.Tc.Rel.fst"
let base_prob = (let _133_1496 = (sub_prob c1.FStar_Absyn_Syntax.result_typ problem.relation c2.FStar_Absyn_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _133_1495 -> TProb (_133_1495)) _133_1496))
in (
# 2134 "FStar.Tc.Rel.fst"
let wl = (let _133_1500 = (let _133_1499 = (let _133_1498 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Absyn_Util.mk_conj _133_1498 g))
in (FStar_All.pipe_left (fun _133_1497 -> Some (_133_1497)) _133_1499))
in (solve_prob orig _133_1500 [] wl))
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
| _44_3165 -> begin
(FStar_All.failwith "Impossible")
end))
and solve_e' : FStar_Tc_Env.env  ->  (FStar_Absyn_Syntax.exp, Prims.unit) problem  ->  worklist  ->  solution = (fun env problem wl -> (
# 2144 "FStar.Tc.Rel.fst"
let problem = (
# 2144 "FStar.Tc.Rel.fst"
let _44_3169 = problem
in {lhs = _44_3169.lhs; relation = EQ; rhs = _44_3169.rhs; element = _44_3169.element; logical_guard = _44_3169.logical_guard; scope = _44_3169.scope; reason = _44_3169.reason; loc = _44_3169.loc; rank = _44_3169.rank})
in (
# 2145 "FStar.Tc.Rel.fst"
let e1 = problem.lhs
in (
# 2146 "FStar.Tc.Rel.fst"
let e2 = problem.rhs
in (
# 2147 "FStar.Tc.Rel.fst"
let orig = EProb (problem)
in (
# 2148 "FStar.Tc.Rel.fst"
let sub_prob = (fun lhs rhs reason -> (mk_problem (p_scope orig) orig lhs EQ rhs None reason))
in (
# 2150 "FStar.Tc.Rel.fst"
let _44_3181 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1510 = (prob_to_string env orig)
in (FStar_Util.print1 "Attempting:\n%s\n" _133_1510))
end else begin
()
end
in (
# 2152 "FStar.Tc.Rel.fst"
let flex_rigid = (fun _44_3188 e2 -> (match (_44_3188) with
| (e1, u1, t1, args1) -> begin
(
# 2154 "FStar.Tc.Rel.fst"
let maybe_vars1 = (pat_vars env [] args1)
in (
# 2156 "FStar.Tc.Rel.fst"
let sub_problems = (fun xs args2 -> (
# 2157 "FStar.Tc.Rel.fst"
let _44_3215 = (let _133_1526 = (FStar_All.pipe_right args2 (FStar_List.map (fun _44_34 -> (match (_44_34) with
| (FStar_Util.Inl (t), imp) -> begin
(
# 2159 "FStar.Tc.Rel.fst"
let kk = (FStar_Tc_Recheck.recompute_kind t)
in (
# 2160 "FStar.Tc.Rel.fst"
let _44_3202 = (new_tvar t.FStar_Absyn_Syntax.pos xs kk)
in (match (_44_3202) with
| (gi_xi, gi) -> begin
(
# 2161 "FStar.Tc.Rel.fst"
let gi_pi = (FStar_Absyn_Syntax.mk_Typ_app' (gi, args1) (Some (kk)) t.FStar_Absyn_Syntax.pos)
in (let _133_1522 = (let _133_1521 = (sub_prob gi_pi t "type index")
in (FStar_All.pipe_left (fun _133_1520 -> TProb (_133_1520)) _133_1521))
in ((FStar_Util.Inl (gi_xi), imp), _133_1522)))
end)))
end
| (FStar_Util.Inr (v), imp) -> begin
(
# 2164 "FStar.Tc.Rel.fst"
let tt = (FStar_Tc_Recheck.recompute_typ v)
in (
# 2165 "FStar.Tc.Rel.fst"
let _44_3211 = (new_evar v.FStar_Absyn_Syntax.pos xs tt)
in (match (_44_3211) with
| (gi_xi, gi) -> begin
(
# 2166 "FStar.Tc.Rel.fst"
let gi_pi = (FStar_Absyn_Syntax.mk_Exp_app' (gi, args1) (Some (tt)) v.FStar_Absyn_Syntax.pos)
in (let _133_1525 = (let _133_1524 = (sub_prob gi_pi v "expression index")
in (FStar_All.pipe_left (fun _133_1523 -> EProb (_133_1523)) _133_1524))
in ((FStar_Util.Inr (gi_xi), imp), _133_1525)))
end)))
end))))
in (FStar_All.pipe_right _133_1526 FStar_List.unzip))
in (match (_44_3215) with
| (gi_xi, gi_pi) -> begin
(
# 2168 "FStar.Tc.Rel.fst"
let formula = (let _133_1528 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) gi_pi)
in (FStar_Absyn_Util.mk_conj_l _133_1528))
in (gi_xi, gi_pi, formula))
end)))
in (
# 2171 "FStar.Tc.Rel.fst"
let project_e = (fun head2 args2 -> (
# 2176 "FStar.Tc.Rel.fst"
let giveup = (fun reason -> (let _133_1535 = (FStar_Util.format1 "flex-rigid: refusing to project expressions (%s)" reason)
in (giveup env _133_1535 orig)))
in (match ((let _133_1536 = (FStar_Absyn_Util.compress_exp head2)
in _133_1536.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (y) -> begin
(
# 2179 "FStar.Tc.Rel.fst"
let _44_3232 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_44_3232) with
| (all_xs, tres) -> begin
if ((FStar_List.length all_xs) <> (FStar_List.length args1)) then begin
(let _133_1539 = (let _133_1538 = (FStar_Absyn_Print.binders_to_string ", " all_xs)
in (let _133_1537 = (FStar_Absyn_Print.args_to_string args2)
in (FStar_Util.format2 "unequal arity:\n\texpetced binders %s\n\tgot args {%s}" _133_1538 _133_1537)))
in (giveup _133_1539))
end else begin
(
# 2184 "FStar.Tc.Rel.fst"
let rec aux = (fun xs args -> (match ((xs, args)) with
| ([], []) -> begin
(giveup "variable to project not found")
end
| (([], _)) | ((_, [])) -> begin
(FStar_All.failwith "impossible")
end
| ((FStar_Util.Inl (_44_3249), _44_3252)::xs, (FStar_Util.Inl (_44_3257), _44_3260)::args) -> begin
(aux xs args)
end
| ((FStar_Util.Inr (xi), _44_3268)::xs, (FStar_Util.Inr (arg), _44_3275)::args) -> begin
(match ((let _133_1544 = (FStar_Absyn_Util.compress_exp arg)
in _133_1544.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_bvar (z) -> begin
if (FStar_Absyn_Util.bvar_eq y z) then begin
(
# 2193 "FStar.Tc.Rel.fst"
let _44_3284 = (sub_problems all_xs args2)
in (match (_44_3284) with
| (gi_xi, gi_pi, f) -> begin
(
# 2194 "FStar.Tc.Rel.fst"
let sol = (let _133_1548 = (let _133_1547 = (let _133_1546 = (let _133_1545 = (FStar_Absyn_Util.bvar_to_exp xi)
in (_133_1545, gi_xi))
in (FStar_Absyn_Syntax.mk_Exp_app' _133_1546 None e1.FStar_Absyn_Syntax.pos))
in (all_xs, _133_1547))
in (FStar_Absyn_Syntax.mk_Exp_abs _133_1548 None e1.FStar_Absyn_Syntax.pos))
in (
# 2195 "FStar.Tc.Rel.fst"
let _44_3286 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1552 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _133_1551 = (FStar_Absyn_Print.exp_to_string sol)
in (let _133_1550 = (let _133_1549 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _133_1549 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Projected: %s -> %s\nSubprobs=\n%s\n" _133_1552 _133_1551 _133_1550))))
end else begin
()
end
in (let _133_1554 = (let _133_1553 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _133_1553))
in (solve env _133_1554))))
end))
end else begin
(aux xs args)
end
end
| _44_3289 -> begin
(aux xs args)
end)
end
| (x::xs, arg::args) -> begin
(let _133_1557 = (let _133_1556 = (FStar_Absyn_Print.binder_to_string x)
in (let _133_1555 = (FStar_Absyn_Print.arg_to_string arg)
in (FStar_Util.format2 "type incorrect term---impossible: expected %s; got %s\n" _133_1556 _133_1555)))
in (giveup _133_1557))
end))
in (aux (FStar_List.rev all_xs) (FStar_List.rev args1)))
end
end))
end
| _44_3298 -> begin
(giveup "rigid head term is not a variable")
end)))
in (
# 2206 "FStar.Tc.Rel.fst"
let imitate_or_project_e = (fun _44_3300 -> (match (()) with
| () -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid: not a pattern" orig wl))
end else begin
(
# 2214 "FStar.Tc.Rel.fst"
let _44_3301 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1561 = (FStar_Absyn_Print.exp_to_string e1)
in (let _133_1560 = (FStar_Absyn_Print.exp_to_string e2)
in (FStar_Util.print2 "Imitating expressions: %s =?= %s\n" _133_1561 _133_1560)))
end else begin
()
end
in (
# 2215 "FStar.Tc.Rel.fst"
let _44_3305 = (FStar_Absyn_Util.head_and_args_e e2)
in (match (_44_3305) with
| (head2, args2) -> begin
(
# 2216 "FStar.Tc.Rel.fst"
let fvhead = (FStar_Absyn_Util.freevars_exp head2)
in (
# 2217 "FStar.Tc.Rel.fst"
let _44_3310 = (occurs_check_e env (u1, t1) head2)
in (match (_44_3310) with
| (occurs_ok, _44_3309) -> begin
if ((FStar_Absyn_Util.fvs_included fvhead FStar_Absyn_Syntax.no_fvs) && occurs_ok) then begin
(
# 2219 "FStar.Tc.Rel.fst"
let _44_3318 = (match ((FStar_Absyn_Util.function_formals t1)) with
| None -> begin
([], t1)
end
| Some (xs, c) -> begin
(xs, (FStar_Absyn_Util.comp_result c))
end)
in (match (_44_3318) with
| (xs, tres) -> begin
(
# 2222 "FStar.Tc.Rel.fst"
let _44_3322 = (sub_problems xs args2)
in (match (_44_3322) with
| (gi_xi, gi_pi, f) -> begin
(
# 2223 "FStar.Tc.Rel.fst"
let sol = (
# 2224 "FStar.Tc.Rel.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (match (xs) with
| [] -> begin
body
end
| _44_3326 -> begin
(let _133_1563 = (let _133_1562 = (FStar_Absyn_Syntax.mk_Exp_app' (head2, gi_xi) None e1.FStar_Absyn_Syntax.pos)
in (xs, _133_1562))
in (FStar_Absyn_Syntax.mk_Exp_abs _133_1563 None e1.FStar_Absyn_Syntax.pos))
end))
in (
# 2228 "FStar.Tc.Rel.fst"
let _44_3328 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1567 = (FStar_Absyn_Print.uvar_e_to_string (u1, t1))
in (let _133_1566 = (FStar_Absyn_Print.exp_to_string sol)
in (let _133_1565 = (let _133_1564 = (FStar_All.pipe_right gi_pi (FStar_List.map (prob_to_string env)))
in (FStar_All.pipe_right _133_1564 (FStar_String.concat "\n")))
in (FStar_Util.print3 "Imitated: %s -> %s\nSubprobs=\n%s\n" _133_1567 _133_1566 _133_1565))))
end else begin
()
end
in (let _133_1569 = (let _133_1568 = (solve_prob orig (Some (f)) ((UE (((u1, t1), sol)))::[]) wl)
in (attempt gi_pi _133_1568))
in (solve env _133_1569))))
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
# 2240 "FStar.Tc.Rel.fst"
let fvs1 = (FStar_Absyn_Syntax.freevars_of_binders xs)
in (
# 2241 "FStar.Tc.Rel.fst"
let fvs2 = (FStar_Absyn_Util.freevars_exp e2)
in (
# 2242 "FStar.Tc.Rel.fst"
let _44_3340 = (occurs_check_e env (u1, t1) e2)
in (match (_44_3340) with
| (occurs_ok, _44_3339) -> begin
if (((FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.ftvs fvs1.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs2.FStar_Absyn_Syntax.fxvs fvs1.FStar_Absyn_Syntax.fxvs)) && occurs_ok) then begin
(
# 2248 "FStar.Tc.Rel.fst"
let sol = (FStar_Absyn_Syntax.mk_Exp_abs' (xs, e2) None e1.FStar_Absyn_Syntax.pos)
in (let _133_1570 = (solve_prob orig None ((UE (((u1, t1), sol)))::[]) wl)
in (solve env _133_1570)))
end else begin
(imitate_or_project_e ())
end
end))))
end)))))
end))
in (
# 2253 "FStar.Tc.Rel.fst"
let flex_flex = (fun _44_3347 _44_3352 -> (match ((_44_3347, _44_3352)) with
| ((e1, u1, t1, args1), (e2, u2, t2, args2)) -> begin
(
# 2254 "FStar.Tc.Rel.fst"
let maybe_vars1 = (pat_vars env [] args1)
in (
# 2255 "FStar.Tc.Rel.fst"
let maybe_vars2 = (pat_vars env [] args2)
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
(
# 2271 "FStar.Tc.Rel.fst"
let zs = (intersect_vars xs ys)
in (
# 2272 "FStar.Tc.Rel.fst"
let tt = (FStar_Tc_Recheck.recompute_typ e2)
in (
# 2273 "FStar.Tc.Rel.fst"
let _44_3373 = (let _133_1575 = (FStar_Tc_Env.get_range env)
in (new_evar _133_1575 zs tt))
in (match (_44_3373) with
| (u, _44_3372) -> begin
(
# 2274 "FStar.Tc.Rel.fst"
let sub1 = (match (xs) with
| [] -> begin
u
end
| _44_3376 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (xs, u) (Some (t1)) e1.FStar_Absyn_Syntax.pos)
end)
in (
# 2277 "FStar.Tc.Rel.fst"
let sub2 = (match (ys) with
| [] -> begin
u
end
| _44_3380 -> begin
(FStar_Absyn_Syntax.mk_Exp_abs (ys, u) (Some (t2)) e1.FStar_Absyn_Syntax.pos)
end)
in (let _133_1576 = (solve_prob orig None ((UE (((u1, t1), sub1)))::(UE (((u2, t2), sub2)))::[]) wl)
in (solve env _133_1576))))
end))))
end
end)))
end))
in (
# 2283 "FStar.Tc.Rel.fst"
let smt_fallback = (fun e1 e2 -> if wl.smt_ok then begin
(
# 2285 "FStar.Tc.Rel.fst"
let _44_3385 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1581 = (prob_to_string env orig)
in (FStar_Util.print1 "Using SMT to solve:\n%s\n" _133_1581))
end else begin
()
end
in (
# 2286 "FStar.Tc.Rel.fst"
let _44_3390 = (let _133_1583 = (FStar_Tc_Env.get_range env)
in (let _133_1582 = (FStar_Tc_Env.binders env)
in (new_tvar _133_1583 _133_1582 FStar_Absyn_Syntax.ktype)))
in (match (_44_3390) with
| (t, _44_3389) -> begin
(let _133_1587 = (let _133_1586 = (let _133_1585 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _133_1584 -> Some (_133_1584)) _133_1585))
in (solve_prob orig _133_1586 [] wl))
in (solve env _133_1587))
end)))
end else begin
(giveup env "no SMT solution permitted" orig)
end)
in (match ((e1.FStar_Absyn_Syntax.n, e2.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_ascribed (e1, _44_3393, _44_3395), _44_3399) -> begin
(solve_e env (
# 2292 "FStar.Tc.Rel.fst"
let _44_3401 = problem
in {lhs = e1; relation = _44_3401.relation; rhs = _44_3401.rhs; element = _44_3401.element; logical_guard = _44_3401.logical_guard; scope = _44_3401.scope; reason = _44_3401.reason; loc = _44_3401.loc; rank = _44_3401.rank}) wl)
end
| (_44_3404, FStar_Absyn_Syntax.Exp_ascribed (e2, _44_3407, _44_3409)) -> begin
(solve_e env (
# 2295 "FStar.Tc.Rel.fst"
let _44_3413 = problem
in {lhs = _44_3413.lhs; relation = _44_3413.relation; rhs = e2; element = _44_3413.element; logical_guard = _44_3413.logical_guard; scope = _44_3413.scope; reason = _44_3413.reason; loc = _44_3413.loc; rank = _44_3413.rank}) wl)
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_uvar (_))) | ((FStar_Absyn_Syntax.Exp_uvar (_), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _133_1589 = (destruct_flex_e e1)
in (let _133_1588 = (destruct_flex_e e2)
in (flex_flex _133_1589 _133_1588)))
end
| ((FStar_Absyn_Syntax.Exp_uvar (_), _)) | ((FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _), _)) -> begin
(let _133_1590 = (destruct_flex_e e1)
in (flex_rigid _133_1590 e2))
end
| ((_, FStar_Absyn_Syntax.Exp_uvar (_))) | ((_, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_uvar (_); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _))) -> begin
(let _133_1591 = (destruct_flex_e e2)
in (flex_rigid _133_1591 e1))
end
| (FStar_Absyn_Syntax.Exp_bvar (x1), FStar_Absyn_Syntax.Exp_bvar (x1')) -> begin
if (FStar_Absyn_Util.bvd_eq x1.FStar_Absyn_Syntax.v x1'.FStar_Absyn_Syntax.v) then begin
(let _133_1592 = (solve_prob orig None [] wl)
in (solve env _133_1592))
end else begin
(let _133_1598 = (let _133_1597 = (let _133_1596 = (let _133_1595 = (FStar_Tc_Recheck.recompute_typ e1)
in (let _133_1594 = (FStar_Tc_Recheck.recompute_typ e2)
in (FStar_Absyn_Util.mk_eq _133_1595 _133_1594 e1 e2)))
in (FStar_All.pipe_left (fun _133_1593 -> Some (_133_1593)) _133_1596))
in (solve_prob orig _133_1597 [] wl))
in (solve env _133_1598))
end
end
| (FStar_Absyn_Syntax.Exp_fvar (fv1, _44_3552), FStar_Absyn_Syntax.Exp_fvar (fv1', _44_3557)) -> begin
if (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv1'.FStar_Absyn_Syntax.v) then begin
(let _133_1599 = (solve_prob orig None [] wl)
in (solve env _133_1599))
end else begin
(giveup env "free-variables unequal" orig)
end
end
| (FStar_Absyn_Syntax.Exp_constant (s1), FStar_Absyn_Syntax.Exp_constant (s1')) -> begin
(
# 2325 "FStar.Tc.Rel.fst"
let const_eq = (fun s1 s2 -> (match ((s1, s2)) with
| (FStar_Const.Const_bytearray (b1, _44_3571), FStar_Const.Const_bytearray (b2, _44_3576)) -> begin
(b1 = b2)
end
| (FStar_Const.Const_string (b1, _44_3582), FStar_Const.Const_string (b2, _44_3587)) -> begin
(b1 = b2)
end
| _44_3592 -> begin
(s1 = s2)
end))
in if (const_eq s1 s1') then begin
(let _133_1604 = (solve_prob orig None [] wl)
in (solve env _133_1604))
end else begin
(giveup env "constants unequal" orig)
end)
end
| (FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_44_3602); FStar_Absyn_Syntax.tk = _44_3600; FStar_Absyn_Syntax.pos = _44_3598; FStar_Absyn_Syntax.fvs = _44_3596; FStar_Absyn_Syntax.uvs = _44_3594}, _44_3606), _44_3610) -> begin
(let _133_1606 = (
# 2334 "FStar.Tc.Rel.fst"
let _44_3612 = problem
in (let _133_1605 = (whnf_e env e1)
in {lhs = _133_1605; relation = _44_3612.relation; rhs = _44_3612.rhs; element = _44_3612.element; logical_guard = _44_3612.logical_guard; scope = _44_3612.scope; reason = _44_3612.reason; loc = _44_3612.loc; rank = _44_3612.rank}))
in (solve_e env _133_1606 wl))
end
| (_44_3615, FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_44_3625); FStar_Absyn_Syntax.tk = _44_3623; FStar_Absyn_Syntax.pos = _44_3621; FStar_Absyn_Syntax.fvs = _44_3619; FStar_Absyn_Syntax.uvs = _44_3617}, _44_3629)) -> begin
(let _133_1608 = (
# 2337 "FStar.Tc.Rel.fst"
let _44_3633 = problem
in (let _133_1607 = (whnf_e env e2)
in {lhs = _44_3633.lhs; relation = _44_3633.relation; rhs = _133_1607; element = _44_3633.element; logical_guard = _44_3633.logical_guard; scope = _44_3633.scope; reason = _44_3633.reason; loc = _44_3633.loc; rank = _44_3633.rank}))
in (solve_e env _133_1608 wl))
end
| (FStar_Absyn_Syntax.Exp_app (head1, args1), FStar_Absyn_Syntax.Exp_app (head2, args2)) -> begin
(
# 2340 "FStar.Tc.Rel.fst"
let orig_wl = wl
in (
# 2341 "FStar.Tc.Rel.fst"
let rec solve_args = (fun sub_probs wl args1 args2 -> (match ((args1, args2)) with
| ([], []) -> begin
(
# 2343 "FStar.Tc.Rel.fst"
let guard = (let _133_1618 = (let _133_1617 = (FStar_List.map p_guard sub_probs)
in (FStar_All.pipe_right _133_1617 (FStar_List.map Prims.fst)))
in (FStar_Absyn_Util.mk_conj_l _133_1618))
in (
# 2344 "FStar.Tc.Rel.fst"
let g = (simplify_formula env guard)
in (
# 2345 "FStar.Tc.Rel.fst"
let g = (FStar_Absyn_Util.compress_typ g)
in (match (g.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
(let _133_1619 = (solve_prob orig None wl.subst (
# 2348 "FStar.Tc.Rel.fst"
let _44_3658 = orig_wl
in {attempting = _44_3658.attempting; wl_deferred = _44_3658.wl_deferred; subst = []; ctr = _44_3658.ctr; slack_vars = _44_3658.slack_vars; defer_ok = _44_3658.defer_ok; smt_ok = _44_3658.smt_ok; tcenv = _44_3658.tcenv}))
in (solve env _133_1619))
end
| _44_3661 -> begin
(
# 2350 "FStar.Tc.Rel.fst"
let _44_3665 = (let _133_1621 = (FStar_Tc_Env.get_range env)
in (let _133_1620 = (FStar_Tc_Env.binders env)
in (new_tvar _133_1621 _133_1620 FStar_Absyn_Syntax.ktype)))
in (match (_44_3665) with
| (t, _44_3664) -> begin
(
# 2351 "FStar.Tc.Rel.fst"
let guard = (let _133_1622 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_Absyn_Util.mk_disj g _133_1622))
in (let _133_1623 = (solve_prob orig (Some (guard)) wl.subst (
# 2352 "FStar.Tc.Rel.fst"
let _44_3667 = orig_wl
in {attempting = _44_3667.attempting; wl_deferred = _44_3667.wl_deferred; subst = []; ctr = _44_3667.ctr; slack_vars = _44_3667.slack_vars; defer_ok = _44_3667.defer_ok; smt_ok = _44_3667.smt_ok; tcenv = _44_3667.tcenv}))
in (solve env _133_1623)))
end))
end))))
end
| (arg1::rest1, arg2::rest2) -> begin
(
# 2355 "FStar.Tc.Rel.fst"
let prob = (match (((Prims.fst arg1), (Prims.fst arg2))) with
| (FStar_Util.Inl (t1), FStar_Util.Inl (t2)) -> begin
(let _133_1625 = (mk_problem (p_scope orig) orig t1 EQ t2 None "expression type arg")
in (FStar_All.pipe_left (fun _133_1624 -> TProb (_133_1624)) _133_1625))
end
| (FStar_Util.Inr (e1), FStar_Util.Inr (e2)) -> begin
(let _133_1627 = (mk_problem (p_scope orig) orig e1 EQ e2 None "expression arg")
in (FStar_All.pipe_left (fun _133_1626 -> EProb (_133_1626)) _133_1627))
end
| _44_3687 -> begin
(FStar_All.failwith "Impossible: ill-typed expression")
end)
in (match ((solve env (
# 2361 "FStar.Tc.Rel.fst"
let _44_3689 = wl
in {attempting = (prob)::[]; wl_deferred = []; subst = _44_3689.subst; ctr = _44_3689.ctr; slack_vars = _44_3689.slack_vars; defer_ok = false; smt_ok = false; tcenv = _44_3689.tcenv}))) with
| Failed (_44_3692) -> begin
(smt_fallback e1 e2)
end
| Success (subst, _44_3696) -> begin
(solve_args ((prob)::sub_probs) (
# 2363 "FStar.Tc.Rel.fst"
let _44_3699 = wl
in {attempting = _44_3699.attempting; wl_deferred = _44_3699.wl_deferred; subst = subst; ctr = _44_3699.ctr; slack_vars = _44_3699.slack_vars; defer_ok = _44_3699.defer_ok; smt_ok = _44_3699.smt_ok; tcenv = _44_3699.tcenv}) rest1 rest2)
end))
end
| _44_3702 -> begin
(FStar_All.failwith "Impossible: lengths defer")
end))
in (
# 2368 "FStar.Tc.Rel.fst"
let rec match_head_and_args = (fun head1 head2 -> (match ((let _133_1635 = (let _133_1632 = (FStar_Absyn_Util.compress_exp head1)
in _133_1632.FStar_Absyn_Syntax.n)
in (let _133_1634 = (let _133_1633 = (FStar_Absyn_Util.compress_exp head2)
in _133_1633.FStar_Absyn_Syntax.n)
in (_133_1635, _133_1634)))) with
| (FStar_Absyn_Syntax.Exp_bvar (x), FStar_Absyn_Syntax.Exp_bvar (y)) when ((FStar_Absyn_Util.bvar_eq x y) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_fvar (f, _44_3713), FStar_Absyn_Syntax.Exp_fvar (g, _44_3718)) when (((FStar_Absyn_Util.fvar_eq f g) && (not ((FStar_Absyn_Util.is_interpreted f.FStar_Absyn_Syntax.v)))) && ((FStar_List.length args1) = (FStar_List.length args2))) -> begin
(solve_args [] wl args1 args2)
end
| (FStar_Absyn_Syntax.Exp_ascribed (e, _44_3724, _44_3726), _44_3730) -> begin
(match_head_and_args e head2)
end
| (_44_3733, FStar_Absyn_Syntax.Exp_ascribed (e, _44_3736, _44_3738)) -> begin
(match_head_and_args head1 e)
end
| (FStar_Absyn_Syntax.Exp_abs (_44_3743), _44_3746) -> begin
(let _133_1637 = (
# 2374 "FStar.Tc.Rel.fst"
let _44_3748 = problem
in (let _133_1636 = (whnf_e env e1)
in {lhs = _133_1636; relation = _44_3748.relation; rhs = _44_3748.rhs; element = _44_3748.element; logical_guard = _44_3748.logical_guard; scope = _44_3748.scope; reason = _44_3748.reason; loc = _44_3748.loc; rank = _44_3748.rank}))
in (solve_e env _133_1637 wl))
end
| (_44_3751, FStar_Absyn_Syntax.Exp_abs (_44_3753)) -> begin
(let _133_1639 = (
# 2376 "FStar.Tc.Rel.fst"
let _44_3756 = problem
in (let _133_1638 = (whnf_e env e2)
in {lhs = _44_3756.lhs; relation = _44_3756.relation; rhs = _133_1638; element = _44_3756.element; logical_guard = _44_3756.logical_guard; scope = _44_3756.scope; reason = _44_3756.reason; loc = _44_3756.loc; rank = _44_3756.rank}))
in (solve_e env _133_1639 wl))
end
| _44_3759 -> begin
(smt_fallback e1 e2)
end))
in (match_head_and_args head1 head2))))
end
| _44_3761 -> begin
(
# 2383 "FStar.Tc.Rel.fst"
let _44_3765 = (let _133_1641 = (FStar_Tc_Env.get_range env)
in (let _133_1640 = (FStar_Tc_Env.binders env)
in (new_tvar _133_1641 _133_1640 FStar_Absyn_Syntax.ktype)))
in (match (_44_3765) with
| (t, _44_3764) -> begin
(
# 2384 "FStar.Tc.Rel.fst"
let guard = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (
# 2385 "FStar.Tc.Rel.fst"
let _44_3767 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1642 = (FStar_Absyn_Print.typ_to_string guard)
in (FStar_Util.print1 "Emitting guard %s\n" _133_1642))
end else begin
()
end
in (let _133_1646 = (let _133_1645 = (let _133_1644 = (FStar_Absyn_Util.mk_eq t t e1 e2)
in (FStar_All.pipe_left (fun _133_1643 -> Some (_133_1643)) _133_1644))
in (solve_prob orig _133_1645 [] wl))
in (solve env _133_1646))))
end))
end)))))))))))

# 2387 "FStar.Tc.Rel.fst"
let guard_to_string : FStar_Tc_Env.env  ->  guard_t  ->  Prims.string = (fun env g -> (
# 2393 "FStar.Tc.Rel.fst"
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
# 2399 "FStar.Tc.Rel.fst"
let carry = (let _133_1652 = (FStar_List.map (fun _44_3778 -> (match (_44_3778) with
| (_44_3776, x) -> begin
(prob_to_string env x)
end)) g.deferred.carry)
in (FStar_All.pipe_right _133_1652 (FStar_String.concat ",\n")))
in (FStar_Util.format2 "\n\t{guard_f=%s;\n\t deferred={\n%s};}\n" form carry))))

# 2400 "FStar.Tc.Rel.fst"
let guard_of_guard_formula : guard_formula  ->  guard_t = (fun g -> {guard_f = g; deferred = {carry = []; slack = []}; implicits = []})

# 2405 "FStar.Tc.Rel.fst"
let guard_form : guard_t  ->  guard_formula = (fun g -> g.guard_f)

# 2407 "FStar.Tc.Rel.fst"
let is_trivial : guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = _44_3784} -> begin
true
end
| _44_3791 -> begin
false
end))

# 2411 "FStar.Tc.Rel.fst"
let trivial_guard : guard_t = {guard_f = Trivial; deferred = {carry = []; slack = []}; implicits = []}

# 2413 "FStar.Tc.Rel.fst"
let abstract_guard : FStar_Absyn_Syntax.bvvar  ->  guard_t Prims.option  ->  guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({guard_f = Trivial; deferred = _; implicits = _})) -> begin
g
end
| Some (g) -> begin
(
# 2419 "FStar.Tc.Rel.fst"
let f = (match (g.guard_f) with
| NonTrivial (f) -> begin
f
end
| _44_3807 -> begin
(FStar_All.failwith "impossible")
end)
in (let _133_1669 = (
# 2422 "FStar.Tc.Rel.fst"
let _44_3809 = g
in (let _133_1668 = (let _133_1667 = (let _133_1666 = (let _133_1665 = (let _133_1664 = (FStar_Absyn_Syntax.v_binder x)
in (_133_1664)::[])
in (_133_1665, f))
in (FStar_Absyn_Syntax.mk_Typ_lam _133_1666 None f.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left (fun _133_1663 -> NonTrivial (_133_1663)) _133_1667))
in {guard_f = _133_1668; deferred = _44_3809.deferred; implicits = _44_3809.implicits}))
in Some (_133_1669)))
end))

# 2422 "FStar.Tc.Rel.fst"
let apply_guard : guard_t  ->  FStar_Absyn_Syntax.exp  ->  guard_t = (fun g e -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(
# 2426 "FStar.Tc.Rel.fst"
let _44_3816 = g
in (let _133_1681 = (let _133_1680 = (let _133_1679 = (let _133_1678 = (let _133_1677 = (let _133_1676 = (FStar_Absyn_Syntax.varg e)
in (_133_1676)::[])
in (f, _133_1677))
in (FStar_Absyn_Syntax.mk_Typ_app _133_1678))
in (FStar_All.pipe_left (FStar_Absyn_Syntax.syn f.FStar_Absyn_Syntax.pos (Some (FStar_Absyn_Syntax.ktype))) _133_1679))
in NonTrivial (_133_1680))
in {guard_f = _133_1681; deferred = _44_3816.deferred; implicits = _44_3816.implicits}))
end))

# 2426 "FStar.Tc.Rel.fst"
let trivial : guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| Trivial -> begin
()
end
| NonTrivial (_44_3821) -> begin
(FStar_All.failwith "impossible")
end))

# 2430 "FStar.Tc.Rel.fst"
let conj_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((Trivial, g)) | ((g, Trivial)) -> begin
g
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(let _133_1688 = (FStar_Absyn_Util.mk_conj f1 f2)
in NonTrivial (_133_1688))
end))

# 2435 "FStar.Tc.Rel.fst"
let check_trivial : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  guard_formula = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _44_3839 -> begin
NonTrivial (t)
end))

# 2439 "FStar.Tc.Rel.fst"
let imp_guard_f : guard_formula  ->  guard_formula  ->  guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (Trivial, g) -> begin
g
end
| (g, Trivial) -> begin
Trivial
end
| (NonTrivial (f1), NonTrivial (f2)) -> begin
(
# 2445 "FStar.Tc.Rel.fst"
let imp = (FStar_Absyn_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

# 2445 "FStar.Tc.Rel.fst"
let binop_guard : (guard_formula  ->  guard_formula  ->  guard_formula)  ->  guard_t  ->  guard_t  ->  guard_t = (fun f g1 g2 -> (let _133_1711 = (f g1.guard_f g2.guard_f)
in {guard_f = _133_1711; deferred = {carry = (FStar_List.append g1.deferred.carry g2.deferred.carry); slack = (FStar_List.append g1.deferred.slack g2.deferred.slack)}; implicits = (FStar_List.append g1.implicits g2.implicits)}))

# 2450 "FStar.Tc.Rel.fst"
let conj_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

# 2451 "FStar.Tc.Rel.fst"
let imp_guard : guard_t  ->  guard_t  ->  guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

# 2452 "FStar.Tc.Rel.fst"
let close_guard : FStar_Absyn_Syntax.binders  ->  guard_t  ->  guard_t = (fun binders g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(
# 2456 "FStar.Tc.Rel.fst"
let _44_3866 = g
in (let _133_1726 = (let _133_1725 = (FStar_Absyn_Util.close_forall binders f)
in (FStar_All.pipe_right _133_1725 (fun _133_1724 -> NonTrivial (_133_1724))))
in {guard_f = _133_1726; deferred = _44_3866.deferred; implicits = _44_3866.implicits}))
end))

# 2456 "FStar.Tc.Rel.fst"
let mk_guard = (fun g ps slack locs -> {guard_f = g; deferred = {carry = ps; slack = slack}; implicits = []})

# 2460 "FStar.Tc.Rel.fst"
let new_t_problem = (fun env lhs rel rhs elt loc -> (
# 2468 "FStar.Tc.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _133_1738 = (FStar_Tc_Normalize.typ_norm_to_string env lhs)
in (let _133_1737 = (FStar_Tc_Normalize.typ_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _133_1738 (rel_to_string rel) _133_1737)))
end else begin
"TOP"
end
in (
# 2471 "FStar.Tc.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2472 "FStar.Tc.Rel.fst"
let new_t_prob : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  rel  ->  FStar_Absyn_Syntax.typ  ->  (prob * ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) = (fun env t1 rel t2 -> (
# 2475 "FStar.Tc.Rel.fst"
let x = (let _133_1747 = (FStar_Tc_Env.get_range env)
in (FStar_Absyn_Util.gen_bvar_p _133_1747 t1))
in (
# 2476 "FStar.Tc.Rel.fst"
let env = (FStar_Tc_Env.push_local_binding env (FStar_Tc_Env.Binding_var ((x.FStar_Absyn_Syntax.v, x.FStar_Absyn_Syntax.sort))))
in (
# 2477 "FStar.Tc.Rel.fst"
let p = (let _133_1751 = (let _133_1749 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left (fun _133_1748 -> Some (_133_1748)) _133_1749))
in (let _133_1750 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 rel t2 _133_1751 _133_1750)))
in (TProb (p), x)))))

# 2478 "FStar.Tc.Rel.fst"
let new_k_problem = (fun env lhs rel rhs elt loc -> (
# 2481 "FStar.Tc.Rel.fst"
let reason = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _133_1759 = (FStar_Tc_Normalize.kind_norm_to_string env lhs)
in (let _133_1758 = (FStar_Tc_Normalize.kind_norm_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _133_1759 (rel_to_string rel) _133_1758)))
end else begin
"TOP"
end
in (
# 2484 "FStar.Tc.Rel.fst"
let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

# 2485 "FStar.Tc.Rel.fst"
let simplify_guard : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (match (g.guard_f) with
| Trivial -> begin
g
end
| NonTrivial (f) -> begin
(
# 2490 "FStar.Tc.Rel.fst"
let _44_3900 = if (FStar_Tc_Env.debug env FStar_Options.High) then begin
(let _133_1764 = (FStar_Absyn_Print.typ_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _133_1764))
end else begin
()
end
in (
# 2491 "FStar.Tc.Rel.fst"
let f = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Simplify)::[]) env f)
in (
# 2492 "FStar.Tc.Rel.fst"
let f = (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (fv) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
Trivial
end
| _44_3906 -> begin
NonTrivial (f)
end)
in (
# 2495 "FStar.Tc.Rel.fst"
let _44_3908 = g
in {guard_f = f; deferred = _44_3908.deferred; implicits = _44_3908.implicits}))))
end))

# 2495 "FStar.Tc.Rel.fst"
let solve_and_commit : FStar_Tc_Env.env  ->  worklist  ->  ((prob * Prims.string)  ->  deferred Prims.option)  ->  deferred Prims.option = (fun env probs err -> (
# 2498 "FStar.Tc.Rel.fst"
let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(
# 2498 "FStar.Tc.Rel.fst"
let _44_3913 = probs
in {attempting = _44_3913.attempting; wl_deferred = _44_3913.wl_deferred; subst = _44_3913.subst; ctr = _44_3913.ctr; slack_vars = _44_3913.slack_vars; defer_ok = false; smt_ok = _44_3913.smt_ok; tcenv = _44_3913.tcenv})
end else begin
probs
end
in (
# 2499 "FStar.Tc.Rel.fst"
let sol = (solve env probs)
in (match (sol) with
| Success (s, deferred) -> begin
(
# 2502 "FStar.Tc.Rel.fst"
let _44_3921 = (commit env s)
in Some (deferred))
end
| Failed (d, s) -> begin
(
# 2505 "FStar.Tc.Rel.fst"
let _44_3927 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _133_1776 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _133_1776))
end else begin
()
end
in (err (d, s)))
end))))

# 2507 "FStar.Tc.Rel.fst"
let with_guard : FStar_Tc_Env.env  ->  prob  ->  deferred Prims.option  ->  guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _133_1788 = (let _133_1787 = (let _133_1786 = (let _133_1785 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _133_1785 (fun _133_1784 -> NonTrivial (_133_1784))))
in {guard_f = _133_1786; deferred = d; implicits = []})
in (simplify_guard env _133_1787))
in (FStar_All.pipe_left (fun _133_1783 -> Some (_133_1783)) _133_1788))
end))

# 2512 "FStar.Tc.Rel.fst"
let try_keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t Prims.option = (fun env k1 k2 -> (
# 2515 "FStar.Tc.Rel.fst"
let _44_3938 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1796 = (FStar_Absyn_Print.kind_to_string k1)
in (let _133_1795 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print2 "try_keq of %s and %s\n" _133_1796 _133_1795)))
end else begin
()
end
in (
# 2517 "FStar.Tc.Rel.fst"
let prob = (let _133_1801 = (let _133_1800 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k1)
in (let _133_1799 = (FStar_Tc_Normalize.norm_kind ((FStar_Tc_Normalize.Beta)::[]) env k2)
in (let _133_1798 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _133_1800 EQ _133_1799 None _133_1798))))
in (FStar_All.pipe_left (fun _133_1797 -> KProb (_133_1797)) _133_1801))
in (let _133_1803 = (solve_and_commit env (singleton env prob) (fun _44_3941 -> None))
in (FStar_All.pipe_left (with_guard env prob) _133_1803)))))

# 2518 "FStar.Tc.Rel.fst"
let keq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env t k1 k2 -> (match ((try_keq env k1 k2)) with
| None -> begin
(
# 2523 "FStar.Tc.Rel.fst"
let r = (match (t) with
| None -> begin
(FStar_Tc_Env.get_range env)
end
| Some (t) -> begin
t.FStar_Absyn_Syntax.pos
end)
in (match (t) with
| None -> begin
(let _133_1814 = (let _133_1813 = (let _133_1812 = (FStar_Tc_Errors.incompatible_kinds env k2 k1)
in (_133_1812, r))
in FStar_Absyn_Syntax.Error (_133_1813))
in (Prims.raise _133_1814))
end
| Some (t) -> begin
(let _133_1817 = (let _133_1816 = (let _133_1815 = (FStar_Tc_Errors.expected_typ_of_kind env k2 t k1)
in (_133_1815, r))
in FStar_Absyn_Syntax.Error (_133_1816))
in (Prims.raise _133_1817))
end))
end
| Some (g) -> begin
g
end))

# 2530 "FStar.Tc.Rel.fst"
let subkind : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  guard_t = (fun env k1 k2 -> (
# 2533 "FStar.Tc.Rel.fst"
let _44_3960 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1827 = (let _133_1824 = (FStar_Tc_Env.get_range env)
in (FStar_All.pipe_left FStar_Range.string_of_range _133_1824))
in (let _133_1826 = (FStar_Absyn_Print.kind_to_string k1)
in (let _133_1825 = (FStar_Absyn_Print.kind_to_string k2)
in (FStar_Util.print3 "(%s) subkind of %s and %s\n" _133_1827 _133_1826 _133_1825))))
end else begin
()
end
in (
# 2535 "FStar.Tc.Rel.fst"
let prob = (let _133_1832 = (let _133_1831 = (whnf_k env k1)
in (let _133_1830 = (whnf_k env k2)
in (let _133_1829 = (FStar_Tc_Env.get_range env)
in (new_k_problem env _133_1831 SUB _133_1830 None _133_1829))))
in (FStar_All.pipe_left (fun _133_1828 -> KProb (_133_1828)) _133_1832))
in (
# 2536 "FStar.Tc.Rel.fst"
let res = (let _133_1839 = (let _133_1838 = (solve_and_commit env (singleton env prob) (fun _44_3963 -> (let _133_1837 = (let _133_1836 = (let _133_1835 = (FStar_Tc_Errors.incompatible_kinds env k1 k2)
in (let _133_1834 = (FStar_Tc_Env.get_range env)
in (_133_1835, _133_1834)))
in FStar_Absyn_Syntax.Error (_133_1836))
in (Prims.raise _133_1837))))
in (FStar_All.pipe_left (with_guard env prob) _133_1838))
in (FStar_Util.must _133_1839))
in res))))

# 2541 "FStar.Tc.Rel.fst"
let try_teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (
# 2544 "FStar.Tc.Rel.fst"
let _44_3969 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1847 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1846 = (FStar_Absyn_Print.typ_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _133_1847 _133_1846)))
end else begin
()
end
in (
# 2546 "FStar.Tc.Rel.fst"
let prob = (let _133_1850 = (let _133_1849 = (FStar_Tc_Env.get_range env)
in (new_t_problem env t1 EQ t2 None _133_1849))
in (FStar_All.pipe_left (fun _133_1848 -> TProb (_133_1848)) _133_1850))
in (
# 2547 "FStar.Tc.Rel.fst"
let g = (let _133_1852 = (solve_and_commit env (singleton env prob) (fun _44_3972 -> None))
in (FStar_All.pipe_left (with_guard env prob) _133_1852))
in g))))

# 2548 "FStar.Tc.Rel.fst"
let teq : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _133_1862 = (let _133_1861 = (let _133_1860 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _133_1859 = (FStar_Tc_Env.get_range env)
in (_133_1860, _133_1859)))
in FStar_Absyn_Syntax.Error (_133_1861))
in (Prims.raise _133_1862))
end
| Some (g) -> begin
(
# 2554 "FStar.Tc.Rel.fst"
let _44_3981 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1865 = (FStar_Absyn_Print.typ_to_string t1)
in (let _133_1864 = (FStar_Absyn_Print.typ_to_string t2)
in (let _133_1863 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _133_1865 _133_1864 _133_1863))))
end else begin
()
end
in g)
end))

# 2555 "FStar.Tc.Rel.fst"
let try_subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t Prims.option = (fun env t1 t2 -> (
# 2558 "FStar.Tc.Rel.fst"
let kopt = (fun _44_35 -> (match (_44_35) with
| None -> begin
"None"
end
| Some (t) -> begin
(FStar_Absyn_Print.kind_to_string t)
end))
in (
# 2561 "FStar.Tc.Rel.fst"
let k = (fun t1 -> (match ((let _133_1876 = (FStar_Absyn_Util.compress_typ t1)
in _133_1876.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (x) -> begin
(let _133_1880 = (let _133_1877 = (FStar_Absyn_Print.kind_to_string x.FStar_Absyn_Syntax.sort)
in (Prims.strcat _133_1877 " ... "))
in (let _133_1879 = (let _133_1878 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _133_1878))
in (Prims.strcat _133_1880 _133_1879)))
end
| _44_3996 -> begin
(let _133_1881 = (FStar_ST.read t1.FStar_Absyn_Syntax.tk)
in (kopt _133_1881))
end))
in (
# 2564 "FStar.Tc.Rel.fst"
let _44_3997 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1885 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _133_1884 = (k t1)
in (let _133_1883 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _133_1882 = (k t2)
in (FStar_Util.print4 "try_subtype of %s : %s and %s : %s\n" _133_1885 _133_1884 _133_1883 _133_1882)))))
end else begin
()
end
in (
# 2570 "FStar.Tc.Rel.fst"
let _44_4001 = (new_t_prob env t1 SUB t2)
in (match (_44_4001) with
| (prob, x) -> begin
(
# 2571 "FStar.Tc.Rel.fst"
let g = (let _133_1887 = (solve_and_commit env (singleton env prob) (fun _44_4002 -> None))
in (FStar_All.pipe_left (with_guard env prob) _133_1887))
in (
# 2572 "FStar.Tc.Rel.fst"
let _44_4005 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _133_1891 = (FStar_Tc_Normalize.typ_norm_to_string env t1)
in (let _133_1890 = (FStar_Tc_Normalize.typ_norm_to_string env t2)
in (let _133_1889 = (let _133_1888 = (FStar_Util.must g)
in (guard_to_string env _133_1888))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _133_1891 _133_1890 _133_1889))))
end else begin
()
end
in (abstract_guard x g)))
end))))))

# 2575 "FStar.Tc.Rel.fst"
let subtype_fail = (fun env t1 t2 -> (let _133_1898 = (let _133_1897 = (let _133_1896 = (FStar_Tc_Errors.basic_type_error env None t2 t1)
in (let _133_1895 = (FStar_Tc_Env.get_range env)
in (_133_1896, _133_1895)))
in FStar_Absyn_Syntax.Error (_133_1897))
in (Prims.raise _133_1898)))

# 2578 "FStar.Tc.Rel.fst"
let subtype : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  guard_t = (fun env t1 t2 -> (match ((try_subtype env t1 t2)) with
| Some (f) -> begin
f
end
| None -> begin
(subtype_fail env t1 t2)
end))

# 2583 "FStar.Tc.Rel.fst"
let sub_comp : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp  ->  guard_t Prims.option = (fun env c1 c2 -> (
# 2586 "FStar.Tc.Rel.fst"
let _44_4019 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1912 = (FStar_Absyn_Print.comp_typ_to_string c1)
in (let _133_1911 = (FStar_Absyn_Print.comp_typ_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _133_1912 _133_1911)))
end else begin
()
end
in (
# 2588 "FStar.Tc.Rel.fst"
let rel = if env.FStar_Tc_Env.use_eq then begin
EQ
end else begin
SUB
end
in (
# 2589 "FStar.Tc.Rel.fst"
let prob = (let _133_1915 = (let _133_1914 = (FStar_Tc_Env.get_range env)
in (new_problem env c1 rel c2 None _133_1914 "sub_comp"))
in (FStar_All.pipe_left (fun _133_1913 -> CProb (_133_1913)) _133_1915))
in (let _133_1917 = (solve_and_commit env (singleton env prob) (fun _44_4023 -> None))
in (FStar_All.pipe_left (with_guard env prob) _133_1917))))))

# 2590 "FStar.Tc.Rel.fst"
let solve_deferred_constraints : FStar_Tc_Env.env  ->  guard_t  ->  guard_t = (fun env g -> (
# 2593 "FStar.Tc.Rel.fst"
let fail = (fun _44_4030 -> (match (_44_4030) with
| (d, s) -> begin
(
# 2594 "FStar.Tc.Rel.fst"
let msg = (explain env d s)
in (Prims.raise (FStar_Absyn_Syntax.Error ((msg, (p_loc d))))))
end))
in (
# 2596 "FStar.Tc.Rel.fst"
let _44_4035 = if ((FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) && ((FStar_List.length g.deferred.carry) <> 0)) then begin
(let _133_1930 = (let _133_1929 = (FStar_All.pipe_right g.deferred.carry (FStar_List.map (fun _44_4034 -> (match (_44_4034) with
| (msg, x) -> begin
(let _133_1928 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc x))
in (let _133_1927 = (prob_to_string env x)
in (let _133_1926 = (let _133_1925 = (FStar_All.pipe_right (p_guard x) Prims.fst)
in (FStar_Tc_Normalize.formula_norm_to_string env _133_1925))
in (FStar_Util.format4 "(At %s) %s\n%s\nguard is %s\n" _133_1928 msg _133_1927 _133_1926))))
end))))
in (FStar_All.pipe_right _133_1929 (FStar_String.concat "\n")))
in (FStar_All.pipe_left (FStar_Util.print1 "Trying to solve carried problems: begin\n%s\nend\n") _133_1930))
end else begin
()
end
in (
# 2603 "FStar.Tc.Rel.fst"
let gopt = (let _133_1931 = (wl_of_guard env g.deferred)
in (solve_and_commit env _133_1931 fail))
in (match (gopt) with
| Some ({carry = _44_4040; slack = slack}) -> begin
(
# 2606 "FStar.Tc.Rel.fst"
let _44_4043 = (fix_slack_vars slack)
in (
# 2607 "FStar.Tc.Rel.fst"
let _44_4045 = g
in {guard_f = _44_4045.guard_f; deferred = no_deferred; implicits = _44_4045.implicits}))
end
| _44_4048 -> begin
(FStar_All.failwith "impossible")
end)))))

# 2608 "FStar.Tc.Rel.fst"
let try_discharge_guard : FStar_Tc_Env.env  ->  guard_t  ->  Prims.unit = (fun env g -> (
# 2611 "FStar.Tc.Rel.fst"
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
# 2616 "FStar.Tc.Rel.fst"
let vc = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| Trivial -> begin
()
end
| NonTrivial (vc) -> begin
(
# 2620 "FStar.Tc.Rel.fst"
let _44_4059 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _133_1938 = (FStar_Tc_Env.get_range env)
in (let _133_1937 = (let _133_1936 = (FStar_Absyn_Print.formula_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _133_1936))
in (FStar_Tc_Errors.diag _133_1938 _133_1937)))
end else begin
()
end
in (env.FStar_Tc_Env.solver.FStar_Tc_Env.solve env vc))
end))
end)
end))





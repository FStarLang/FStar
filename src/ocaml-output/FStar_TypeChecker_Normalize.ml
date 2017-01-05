
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Primops
| Eager_unfolding
| Inlining
| NoDeltaSteps
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars
| NoFullNorm 
 and steps =
step Prims.list


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iota = (fun _discr_ -> (match (_discr_) with
| Iota (_) -> begin
true
end
| _ -> begin
false
end))


let is_Zeta = (fun _discr_ -> (match (_discr_) with
| Zeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exclude = (fun _discr_ -> (match (_discr_) with
| Exclude (_) -> begin
true
end
| _ -> begin
false
end))


let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Primops = (fun _discr_ -> (match (_discr_) with
| Primops (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eager_unfolding = (fun _discr_ -> (match (_discr_) with
| Eager_unfolding (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inlining = (fun _discr_ -> (match (_discr_) with
| Inlining (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoDeltaSteps = (fun _discr_ -> (match (_discr_) with
| NoDeltaSteps (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))


let is_PureSubtermsWithinComputations = (fun _discr_ -> (match (_discr_) with
| PureSubtermsWithinComputations (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reify = (fun _discr_ -> (match (_discr_) with
| Reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_CompressUvars = (fun _discr_ -> (match (_discr_) with
| CompressUvars (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoFullNorm = (fun _discr_ -> (match (_discr_) with
| NoFullNorm (_) -> begin
true
end
| _ -> begin
false
end))


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_55_13) -> begin
_55_13
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_55_16) -> begin
_55_16
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list


let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))


let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))


let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))


let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_55_19) -> begin
_55_19
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_55_22) -> begin
_55_22
end))


let closure_to_string : closure  ->  Prims.string = (fun _55_1 -> (match (_55_1) with
| Clos (_55_25, t, _55_28, _55_30) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (_55_34) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))


let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))


let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))


let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))


let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let is_Steps = (fun _discr_ -> (match (_discr_) with
| Steps (_) -> begin
true
end
| _ -> begin
false
end))


let is_Debug = (fun _discr_ -> (match (_discr_) with
| Debug (_) -> begin
true
end
| _ -> begin
false
end))


let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_55_43) -> begin
_55_43
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_55_46) -> begin
_55_46
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_55_49) -> begin
_55_49
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_55_52) -> begin
_55_52
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_55_55) -> begin
_55_55
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_55_58) -> begin
_55_58
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_55_61) -> begin
_55_61
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_55_64) -> begin
_55_64
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_55_67) -> begin
_55_67
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_55_70) -> begin
_55_70
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_55_76) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _154_231 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _154_231 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _55_2 -> (match (_55_2) with
| Arg (c, _55_83, _55_85) -> begin
(let _154_234 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" _154_234))
end
| MemoLazy (_55_89) -> begin
"MemoLazy"
end
| Abs (_55_92, bs, _55_95, _55_97, _55_99) -> begin
(let _154_235 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _154_235))
end
| UnivArgs (_55_103) -> begin
"UnivArgs"
end
| Match (_55_106) -> begin
"Match"
end
| App (t, _55_110, _55_112) -> begin
(let _154_236 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" _154_236))
end
| Meta (m, _55_117) -> begin
"Meta"
end
| Let (_55_121) -> begin
"Let"
end
| Steps (s, _55_125) -> begin
"Steps"
end
| Debug (t) -> begin
(let _154_237 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" _154_237))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _154_240 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _154_240 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _55_3 -> (match (_55_3) with
| [] -> begin
true
end
| _55_136 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _55_143 -> begin
(let _154_256 = (let _154_255 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _154_255))
in (failwith _154_256))
end)


let comp_to_comp_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| _55_159 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _55_171 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_55_171) with
| (binders, cdef) -> begin
(

let _55_172 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(let _154_271 = (let _154_270 = (let _154_269 = (let _154_268 = (FStar_Util.string_of_int (FStar_List.length binders))
in (let _154_267 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (let _154_266 = (let _154_265 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string _154_265))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" _154_268 _154_267 _154_266))))
in ((_154_269), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Syntax_Syntax.Error (_154_270))
in (Prims.raise _154_271))
end else begin
()
end
in (

let inst = (let _154_275 = (let _154_274 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_154_274)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _55_177 _55_181 -> (match (((_55_177), (_55_181))) with
| ((x, _55_176), (t, _55_180)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _154_275))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _154_276 = (

let _55_184 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _55_184.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _55_184.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _55_184.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _55_184.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _154_276 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c)))))
end))
end)))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid) then begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid) then begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end else begin
None
end
end
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _55_206 = (FStar_List.fold_left (fun _55_197 u -> (match (_55_197) with
| (cur_kernel, cur_max, out) -> begin
(

let _55_201 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_201) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_55_206) with
| (_55_203, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| _55_223 -> begin
(failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _55_216 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(failwith "Universe variable not found")
end
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us = (let _154_293 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _154_293 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _55_250 = (FStar_Syntax_Util.univ_kernel u)
in (match (_55_250) with
| (_55_248, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _55_252 -> begin
us
end))
end
| _55_254 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _154_296 = (aux u)
in (FStar_List.map (fun _154_295 -> FStar_Syntax_Syntax.U_succ (_154_295)) _154_296))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (

let _55_273 = (log cfg (fun _55_272 -> (match (()) with
| () -> begin
(let _154_321 = (FStar_Syntax_Print.tag_of_term t)
in (let _154_320 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _154_321 _154_320)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _55_277 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_55_280) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_55_293) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _154_326 = (let _154_325 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_154_325))
in (mk _154_326 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _154_327 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _154_327))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_55_304) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _55_311) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _55_327 = (closures_as_binders_delayed cfg env bs)
in (match (_55_327) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _154_330 = (let _154_329 = (let _154_328 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_154_328)))
in FStar_Syntax_Syntax.Tm_abs (_154_329))
in (mk _154_330 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _55_335 = (closures_as_binders_delayed cfg env bs)
in (match (_55_335) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _55_343 = (let _154_332 = (let _154_331 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_331)::[])
in (closures_as_binders_delayed cfg env _154_332))
in (match (_55_343) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _154_336 = (let _154_335 = (let _154_334 = (let _154_333 = (FStar_List.hd x)
in (FStar_All.pipe_right _154_333 Prims.fst))
in ((_154_334), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_154_335))
in (mk _154_336 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _154_342 = (let _154_341 = (let _154_340 = (closure_as_term_delayed cfg env t1)
in (let _154_339 = (let _154_338 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _154_337 -> FStar_Util.Inl (_154_337)) _154_338))
in ((_154_340), (_154_339), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_154_341))
in (mk _154_342 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _154_348 = (let _154_347 = (let _154_346 = (closure_as_term_delayed cfg env t1)
in (let _154_345 = (let _154_344 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _154_343 -> FStar_Util.Inr (_154_343)) _154_344))
in ((_154_346), (_154_345), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_154_347))
in (mk _154_348 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _154_353 = (let _154_352 = (let _154_351 = (closure_as_term_delayed cfg env t')
in (let _154_350 = (let _154_349 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_154_349))
in ((_154_351), (_154_350))))
in FStar_Syntax_Syntax.Tm_meta (_154_352))
in (mk _154_353 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _154_359 = (let _154_358 = (let _154_357 = (closure_as_term_delayed cfg env t')
in (let _154_356 = (let _154_355 = (let _154_354 = (closure_as_term_delayed cfg env tbody)
in ((m), (_154_354)))
in FStar_Syntax_Syntax.Meta_monadic (_154_355))
in ((_154_357), (_154_356))))
in FStar_Syntax_Syntax.Tm_meta (_154_358))
in (mk _154_359 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(let _154_365 = (let _154_364 = (let _154_363 = (closure_as_term_delayed cfg env t')
in (let _154_362 = (let _154_361 = (let _154_360 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (_154_360)))
in FStar_Syntax_Syntax.Meta_monadic_lift (_154_361))
in ((_154_363), (_154_362))))
in FStar_Syntax_Syntax.Tm_meta (_154_364))
in (mk _154_365 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _154_368 = (let _154_367 = (let _154_366 = (closure_as_term_delayed cfg env t')
in ((_154_366), (m)))
in FStar_Syntax_Syntax.Tm_meta (_154_367))
in (mk _154_368 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _55_390 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_55_396) -> begin
body
end
| FStar_Util.Inl (_55_399) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _55_402 = lb
in {FStar_Syntax_Syntax.lbname = _55_402.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _55_402.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _55_402.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_55_406, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _55_415 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _55_419 env -> (Dummy)::env) lbs env_univs)
end
in (

let _55_423 = lb
in (let _154_380 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _154_379 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _55_423.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _55_423.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _154_380; FStar_Syntax_Syntax.lbeff = _55_423.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _154_379}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _55_426 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _55_441 -> (match (_55_441) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_55_446) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _55_456 = (norm_pat env hd)
in (match (_55_456) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _154_392 = (norm_pat env p)
in (Prims.fst _154_392)))))
in (((

let _55_459 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _55_459.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_459.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _55_476 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _55_467 _55_470 -> (match (((_55_467), (_55_470))) with
| ((pats, env), (p, b)) -> begin
(

let _55_473 = (norm_pat env p)
in (match (_55_473) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_55_476) with
| (pats, env) -> begin
(((

let _55_477 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _55_477.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_477.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _55_481 = x
in (let _154_395 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_395}))
in (((

let _55_484 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _55_484.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_484.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _55_488 = x
in (let _154_396 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_488.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_488.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_396}))
in (((

let _55_491 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _55_491.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_491.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _55_497 = x
in (let _154_397 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_397}))
in (

let t = (closure_as_term cfg env t)
in (((

let _55_501 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _55_501.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_501.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _55_505 = (norm_pat env pat)
in (match (_55_505) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _154_398 = (closure_as_term cfg env w)
in Some (_154_398))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _154_401 = (let _154_400 = (let _154_399 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_154_399)))
in FStar_Syntax_Syntax.Tm_match (_154_400))
in (mk _154_401 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _55_516 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _55_522 -> begin
(FStar_List.map (fun _55_525 -> (match (_55_525) with
| (x, imp) -> begin
(let _154_409 = (closure_as_term_delayed cfg env x)
in ((_154_409), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _55_541 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _55_531 _55_534 -> (match (((_55_531), (_55_534))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _55_535 = b
in (let _154_415 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_535.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_535.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_415}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_55_541) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _55_547 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _154_420 = (closure_as_term_delayed cfg env t)
in (let _154_419 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _154_420 _154_419)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _154_422 = (closure_as_term_delayed cfg env t)
in (let _154_421 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _154_422 _154_421)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _55_4 -> (match (_55_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _154_424 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_154_424))
end
| f -> begin
f
end))))
in (let _154_426 = (

let _55_565 = c
in (let _154_425 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _154_425; FStar_Syntax_Syntax.effect_name = _55_565.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _154_426)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun _55_5 -> (match (_55_5) with
| FStar_Syntax_Syntax.DECREASES (_55_570) -> begin
false
end
| _55_573 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), (flags))))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), (flags))))
end else begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end
end)
end
| _55_582 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _154_441 = (let _154_440 = (FStar_Util.string_of_int i)
in ((_154_440), (None)))
in FStar_Const.Const_int (_154_441)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _154_637 = (let _154_636 = (FStar_List.map (fun m -> (let _154_635 = (let _154_604 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_154_604), ((fun x y -> (int_as_const (x + y))))))
in (let _154_634 = (let _154_633 = (let _154_615 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_154_615), ((fun x y -> (int_as_const (x - y))))))
in (let _154_632 = (let _154_631 = (let _154_626 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_154_626), ((fun x y -> (int_as_const (x * y))))))
in (_154_631)::[])
in (_154_633)::_154_632))
in (_154_635)::_154_634))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _154_636))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _154_637))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (let _154_647 = (let _154_646 = (let _154_645 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _154_645 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (_154_646))
in (mk _154_647)))
in (

let ctor = (fun x -> (let _154_652 = (let _154_651 = (let _154_650 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _154_650 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (_154_651))
in (mk _154_652)))
in (let _154_682 = (let _154_679 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_154_679), ((fun s -> (let _154_678 = (FStar_String.list_of_string s)
in (let _154_677 = (let _154_676 = (let _154_675 = (let _154_674 = (let _154_670 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_670 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _154_673 = (let _154_672 = (let _154_671 = (name (("FStar")::("Char")::("char")::[]))
in ((_154_671), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_154_672)::[])
in ((_154_674), (_154_673))))
in FStar_Syntax_Syntax.Tm_app (_154_675))
in (mk _154_676))
in (FStar_List.fold_right (fun c a -> (let _154_669 = (let _154_668 = (let _154_667 = (let _154_660 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _154_660 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _154_666 = (let _154_665 = (let _154_661 = (name (("FStar")::("Char")::("char")::[]))
in ((_154_661), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _154_664 = (let _154_663 = (let _154_662 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_154_662), (None)))
in (_154_663)::(((a), (None)))::[])
in (_154_665)::_154_664))
in ((_154_667), (_154_666))))
in FStar_Syntax_Syntax.Tm_app (_154_668))
in (mk _154_669))) _154_678 _154_677)))))))
in (_154_682)::[]))))


let reduce_equality : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun tm -> (

let is_decidable_equality = (fun t -> (match ((let _154_687 = (FStar_Syntax_Util.un_uinst t)
in _154_687.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq)
end
| _55_627 -> begin
false
end))
in (

let is_propositional_equality = (fun t -> (match ((let _154_690 = (FStar_Syntax_Util.un_uinst t)
in _154_690.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)
end
| _55_633 -> begin
false
end))
in (match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (op_eq_inst, ((_typ, _55_645))::((a1, _55_641))::((a2, _55_637))::[]) when (is_decidable_equality op_eq_inst) -> begin
(

let tt = (match ((FStar_Syntax_Util.eq_tm a1 a2)) with
| FStar_Syntax_Util.Equal -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) tm.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Util.NotEqual -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) tm.FStar_Syntax_Syntax.pos)
end
| _55_653 -> begin
tm
end)
in tt)
end
| (FStar_Syntax_Syntax.Tm_app (eq2_inst, (_)::((a1, _))::((a2, _))::[])) | (FStar_Syntax_Syntax.Tm_app (eq2_inst, ((a1, _))::((a2, _))::[])) when (is_propositional_equality eq2_inst) -> begin
(

let tt = (match ((FStar_Syntax_Util.eq_tm a1 a2)) with
| FStar_Syntax_Util.Equal -> begin
FStar_Syntax_Util.t_true
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Syntax_Util.t_false
end
| _55_681 -> begin
tm
end)
in tt)
end
| _55_684 -> begin
tm
end))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let find = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _55_696 -> (match (_55_696) with
| (l, _55_695) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| _55_698 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _55_706))::((a2, _55_702))::[]) -> begin
(match ((find fv arith_ops)) with
| None -> begin
tm
end
| Some (_55_713, op) -> begin
(

let norm = (fun i j -> (

let c = (let _154_707 = (FStar_Util.int_of_string i)
in (let _154_706 = (FStar_Util.int_of_string j)
in (op _154_707 _154_706)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _154_711 = (let _154_708 = (FStar_Syntax_Subst.compress a1)
in _154_708.FStar_Syntax_Syntax.n)
in (let _154_710 = (let _154_709 = (FStar_Syntax_Subst.compress a2)
in _154_709.FStar_Syntax_Syntax.n)
in ((_154_711), (_154_710))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _55_724))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _55_732))::[])) -> begin
(match ((let _154_719 = (let _154_712 = (FStar_Syntax_Subst.compress head1)
in _154_712.FStar_Syntax_Syntax.n)
in (let _154_718 = (let _154_713 = (FStar_Syntax_Subst.compress head2)
in _154_713.FStar_Syntax_Syntax.n)
in (let _154_717 = (let _154_714 = (FStar_Syntax_Subst.compress arg1)
in _154_714.FStar_Syntax_Syntax.n)
in (let _154_716 = (let _154_715 = (FStar_Syntax_Subst.compress arg2)
in _154_715.FStar_Syntax_Syntax.n)
in ((_154_719), (_154_718), (_154_717), (_154_716))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _154_723 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _154_722 = (let _154_721 = (let _154_720 = (norm i j)
in ((_154_720), (None)))
in (_154_721)::[])
in (FStar_Syntax_Util.mk_app _154_723 _154_722)))
end
| _55_754 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _55_767 -> begin
tm
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _55_771))::[]) -> begin
(match ((find fv un_ops)) with
| None -> begin
tm
end
| Some (_55_778, op) -> begin
(match ((let _154_726 = (FStar_Syntax_Subst.compress a1)
in _154_726.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, _55_784)) -> begin
(let _154_727 = (FStar_Bytes.unicode_bytes_as_string b)
in (op _154_727))
end
| _55_789 -> begin
tm
end)
end)
end
| _55_791 -> begin
(reduce_equality tm)
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _55_796 = t
in {FStar_Syntax_Syntax.n = _55_796.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _55_796.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_796.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _55_805 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
(reduce_primops steps tm)
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _55_883 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| _55_926 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _55_953))::((_55_944, (arg, _55_947)))::[] -> begin
arg
end
| _55_957 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _55_961))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _55_967))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _55_971 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _154_738 = (FStar_Syntax_Subst.compress t)
in _154_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_55_989)::[], body, _55_993) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _55_1001 -> begin
tm
end)
end
| _55_1003 -> begin
tm
end)
end
| _55_1005 -> begin
tm
end)
end else begin
(reduce_equality tm)
end
end
end
end
end
end
| _55_1007 -> begin
tm
end)
end))))


let is_norm_request = (fun hd args -> (match ((let _154_742 = (let _154_741 = (FStar_Syntax_Util.un_uinst hd)
in _154_741.FStar_Syntax_Syntax.n)
in ((_154_742), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_55_1015)::(_55_1013)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_55_1021)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| _55_1025 -> begin
false
end))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| _55_1039 -> begin
(failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _55_1046 = (log cfg (fun _55_1045 -> (match (()) with
| () -> begin
(let _154_784 = (FStar_Syntax_Print.tag_of_term t)
in (let _154_783 = (FStar_Syntax_Print.term_to_string t)
in (let _154_782 = (let _154_781 = (let _154_780 = (FStar_Util.first_N (Prims.parse_int "4") stack)
in (FStar_All.pipe_left Prims.fst _154_780))
in (stack_to_string _154_781))
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" _154_784 _154_783 _154_782))))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_55_1049) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app (hd, args) when (((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm)))) && (is_norm_request hd args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _55_1092 = cfg
in {steps = s; tcenv = _55_1092.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _55_1101; FStar_Syntax_Syntax.pos = _55_1099; FStar_Syntax_Syntax.vars = _55_1097}, (a1)::(a2)::rest) -> begin
(

let _55_1115 = (FStar_Syntax_Util.head_and_args t)
in (match (_55_1115) with
| (hd, _55_1114) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _55_1123; FStar_Syntax_Syntax.pos = _55_1121; FStar_Syntax_Syntax.vars = _55_1119}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _55_1134 = (FStar_Syntax_Util.head_and_args t)
in (match (_55_1134) with
| (reify_head, _55_1133) -> begin
(

let a = (let _154_788 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (Prims.fst a))
in (FStar_Syntax_Subst.compress _154_788))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_55_1143)); FStar_Syntax_Syntax.tk = _55_1141; FStar_Syntax_Syntax.pos = _55_1139; FStar_Syntax_Syntax.vars = _55_1137}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| _55_1152 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _154_789 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _154_789)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _154_791 = (let _154_790 = (FStar_List.map (norm_universe cfg env) us)
in ((_154_790), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_154_791))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun _55_6 -> (match (_55_6) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in if (not (should_delta)) then begin
(rebuild cfg env stack t)
end else begin
(

let r_env = (let _154_793 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _154_793))
in (match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _55_1176 = (log cfg (fun _55_1175 -> (match (()) with
| () -> begin
(FStar_Util.print "Tm_fvar case 2\n" [])
end)))
in (rebuild cfg env stack t))
end
| Some (us, t) -> begin
(

let _55_1183 = (log cfg (fun _55_1182 -> (match (()) with
| () -> begin
(let _154_797 = (FStar_Syntax_Print.term_to_string t0)
in (let _154_796 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _154_797 _154_796)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _55_1189))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _55_1197 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _55_1199 -> begin
(let _154_801 = (let _154_800 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _154_800))
in (failwith _154_801))
end)
end else begin
(norm cfg env stack t)
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_55_1203) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _55_1217 = (log cfg (fun _55_1216 -> (match (()) with
| () -> begin
(let _154_804 = (FStar_Syntax_Print.term_to_string t)
in (let _154_803 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _154_804 _154_803)))
end)))
in (match ((let _154_805 = (FStar_Syntax_Subst.compress t')
in _154_805.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_55_1220) -> begin
(norm cfg env stack t')
end
| _55_1223 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end)
end else begin
(norm cfg env stack t0)
end
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (_55_1233))::_55_1231 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_55_1239))::_55_1237 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _55_1245, _55_1247))::stack_rest -> begin
(match (c) with
| Univ (_55_1252) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _55_1255 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (_55_1258)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _55_1262 = (log cfg (fun _55_1261 -> (match (()) with
| () -> begin
(let _154_807 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _154_807))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun _55_7 -> (match (_55_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _55_1272 -> begin
false
end))))) -> begin
(

let _55_1274 = (log cfg (fun _55_1273 -> (match (()) with
| () -> begin
(let _154_810 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _154_810))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _55_1280 = (log cfg (fun _55_1279 -> (match (()) with
| () -> begin
(let _154_812 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _154_812))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _55_1283 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _55_1285 -> begin
(

let cfg = (

let _55_1286 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _55_1286.tcenv; delta_level = _55_1286.delta_level})
in (let _154_813 = (closure_as_term cfg env t)
in (rebuild cfg env stack _154_813)))
end)
end
| (_55_1291)::tl -> begin
(

let _55_1294 = (log cfg (fun _55_1293 -> (match (()) with
| () -> begin
(let _154_815 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _154_815))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _55_1303 = cfg
in {steps = s; tcenv = _55_1303.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _55_1309 = (set_memo r ((env), (t)))
in (

let _55_1312 = (log cfg (fun _55_1311 -> (match (()) with
| () -> begin
(let _154_817 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _154_817))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _154_818 = (closure_as_term cfg env t)
in (rebuild cfg env stack _154_818))
end else begin
(

let _55_1348 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_55_1348) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _154_824 = (let _154_822 = (let _154_820 = (let _154_819 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _154_819))
in (FStar_All.pipe_right _154_820 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _154_822 (fun _154_821 -> FStar_Util.Inl (_154_821))))
in (FStar_All.pipe_right _154_824 (fun _154_823 -> Some (_154_823))))
end
| _55_1353 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _55_1356 -> (Dummy)::env) env))
in (

let _55_1360 = (log cfg (fun _55_1359 -> (match (()) with
| () -> begin
(let _154_828 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _154_828))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _55_1368 stack -> (match (_55_1368) with
| (a, aq) -> begin
(let _154_835 = (let _154_834 = (let _154_833 = (let _154_832 = (let _154_831 = (FStar_Util.mk_ref None)
in ((env), (a), (_154_831), (false)))
in Clos (_154_832))
in ((_154_833), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_154_834))
in (_154_835)::stack)
end)) args))
in (

let _55_1372 = (log cfg (fun _55_1371 -> (match (()) with
| () -> begin
(let _154_837 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _154_837))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let _55_1382 = x
in {FStar_Syntax_Syntax.ppname = _55_1382.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1382.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _55_1386 -> begin
(let _154_838 = (closure_as_term cfg env t)
in (rebuild cfg env stack _154_838))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _55_1390 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_55_1390) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _154_841 = (let _154_840 = (let _154_839 = (FStar_Syntax_Subst.close closing f)
in (((

let _55_1392 = x
in {FStar_Syntax_Syntax.ppname = _55_1392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_154_839)))
in FStar_Syntax_Syntax.Tm_refine (_154_840))
in (mk _154_841 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _154_842 = (closure_as_term cfg env t)
in (rebuild cfg env stack _154_842))
end else begin
(

let _55_1401 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_55_1401) with
| (bs, c) -> begin
(

let c = (let _154_845 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _55_1403 -> (Dummy)::env) env))
in (norm_comp cfg _154_845 c))
in (

let t = (let _154_846 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _154_846 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _, _))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _55_1449 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _55_1452 = (log cfg (fun _55_1451 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _154_848 = (norm cfg env [] t)
in FStar_Util.Inl (_154_848))
end
| FStar_Util.Inr (c) -> begin
(let _154_849 = (norm_comp cfg env c)
in FStar_Util.Inr (_154_849))
end)
in (let _154_850 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _154_850)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_55_1465, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_55_1477); FStar_Syntax_Syntax.lbunivs = _55_1475; FStar_Syntax_Syntax.lbtyp = _55_1473; FStar_Syntax_Syntax.lbeff = _55_1471; FStar_Syntax_Syntax.lbdef = _55_1469})::_55_1467), _55_1483) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))))))) then begin
(

let env = (let _154_853 = (let _154_852 = (let _154_851 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_154_851), (false)))
in Clos (_154_852))
in (_154_853)::env)
in (norm cfg env stack body))
end else begin
(

let _55_1497 = (let _154_856 = (let _154_855 = (let _154_854 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _154_854 FStar_Syntax_Syntax.mk_binder))
in (_154_855)::[])
in (FStar_Syntax_Subst.open_term _154_856 body))
in (match (_55_1497) with
| (bs, body) -> begin
(

let lb = (

let _55_1498 = lb
in (let _154_862 = (let _154_859 = (let _154_857 = (FStar_List.hd bs)
in (FStar_All.pipe_right _154_857 Prims.fst))
in (FStar_All.pipe_right _154_859 (fun _154_858 -> FStar_Util.Inl (_154_858))))
in (let _154_861 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _154_860 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _154_862; FStar_Syntax_Syntax.lbunivs = _55_1498.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _154_861; FStar_Syntax_Syntax.lbeff = _55_1498.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _154_860}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _55_1502 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _154_865 = (closure_as_term cfg env t)
in (rebuild cfg env stack _154_865))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _55_1528 = (FStar_List.fold_right (fun lb _55_1517 -> (match (_55_1517) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _154_868 = (

let _55_1518 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _55_1518.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _55_1518.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _154_868))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_55_1528) with
| (rec_env, memos, _55_1527) -> begin
(

let _55_1531 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _154_875 = (let _154_874 = (let _154_873 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_154_873), (false)))
in Clos (_154_874))
in (_154_875)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _55_1551; FStar_Syntax_Syntax.pos = _55_1549; FStar_Syntax_Syntax.vars = _55_1547}, _55_1556, _55_1558))::_55_1545 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| _55_1563 -> begin
false
end)
in if (not (should_reify)) then begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _55_1567 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _55_1567.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end else begin
(match ((let _154_876 = (FStar_Syntax_Subst.compress head)
in _154_876.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _55_1581 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_55_1581) with
| (_55_1579, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body = (let _154_880 = (let _154_879 = (let _154_878 = (let _154_877 = (FStar_Syntax_Syntax.mk_binder x)
in (_154_877)::[])
in ((_154_878), (body), (None)))
in FStar_Syntax_Syntax.Tm_abs (_154_879))
in (FStar_Syntax_Syntax.mk _154_880 None body.FStar_Syntax_Syntax.pos))
in (

let bind_inst = (match ((let _154_881 = (FStar_Syntax_Subst.compress bind_repr)
in _154_881.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (_55_1591)::(_55_1589)::[]) -> begin
(let _154_887 = (let _154_886 = (let _154_885 = (let _154_884 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv lb.FStar_Syntax_Syntax.lbtyp)
in (let _154_883 = (let _154_882 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_154_882)::[])
in (_154_884)::_154_883))
in ((bind), (_154_885)))
in FStar_Syntax_Syntax.Tm_uinst (_154_886))
in (FStar_Syntax_Syntax.mk _154_887 None t.FStar_Syntax_Syntax.pos))
end
| _55_1596 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (

let reified = (let _154_901 = (let _154_900 = (let _154_899 = (let _154_898 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _154_897 = (let _154_896 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_895 = (let _154_894 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _154_893 = (let _154_892 = (FStar_Syntax_Syntax.as_arg head)
in (let _154_891 = (let _154_890 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _154_889 = (let _154_888 = (FStar_Syntax_Syntax.as_arg body)
in (_154_888)::[])
in (_154_890)::_154_889))
in (_154_892)::_154_891))
in (_154_894)::_154_893))
in (_154_896)::_154_895))
in (_154_898)::_154_897))
in ((bind_inst), (_154_899)))
in FStar_Syntax_Syntax.Tm_app (_154_900))
in (FStar_Syntax_Syntax.mk _154_901 None t.FStar_Syntax_Syntax.pos))
in (let _154_902 = (FStar_List.tl stack)
in (norm cfg env _154_902 reified)))))))
end
| FStar_Util.Inr (_55_1600) -> begin
(failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _55_1610 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_55_1610) with
| (_55_1608, bind_repr) -> begin
(

let maybe_unfold_action = (fun head -> (

let maybe_extract_fv = (fun t -> (

let t = (match ((let _154_907 = (FStar_Syntax_Subst.compress t)
in _154_907.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (t, _55_1617) -> begin
t
end
| _55_1621 -> begin
head
end)
in (match ((let _154_908 = (FStar_Syntax_Subst.compress t)
in _154_908.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
Some (x)
end
| _55_1626 -> begin
None
end)))
in (match ((maybe_extract_fv head)) with
| Some (x) when (let _154_909 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv _154_909)) -> begin
(

let head = (norm cfg env [] head)
in (

let action_unfolded = (match ((maybe_extract_fv head)) with
| Some (_55_1631) -> begin
Some (true)
end
| _55_1634 -> begin
Some (false)
end)
in ((head), (action_unfolded))))
end
| _55_1637 -> begin
((head), (None))
end)))
in (

let rec bind_on_lift = (fun args acc -> (match (args) with
| [] -> begin
(match ((FStar_List.rev acc)) with
| [] -> begin
(failwith "bind_on_lift should be always called with a non-empty list")
end
| ((head, _55_1646))::args -> begin
(

let _55_1651 = (maybe_unfold_action head)
in (match (_55_1651) with
| (head, found_action) -> begin
(

let mk = (fun tm -> (FStar_Syntax_Syntax.mk tm None t.FStar_Syntax_Syntax.pos))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (found_action) with
| None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| Some (false) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))))
end
| Some (true) -> begin
body
end)))
end))
end)
end
| ((e, q))::es -> begin
(match ((let _154_916 = (FStar_Syntax_Subst.compress e)
in _154_916.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) when (not ((FStar_Syntax_Util.is_pure_effect m1))) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "monadic_app_var" None t')
in (

let body = (let _154_919 = (let _154_918 = (let _154_917 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_154_917), (q)))
in (_154_918)::acc)
in (bind_on_lift es _154_919))
in (

let lifted_e0 = (reify_lift cfg.tcenv e0 m1 m2 t')
in (

let continuation = (FStar_Syntax_Util.abs ((((x), (None)))::[]) body (Some (FStar_Util.Inr (((m2), ([]))))))
in (

let bind_inst = (match ((let _154_920 = (FStar_Syntax_Subst.compress bind_repr)
in _154_920.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (_55_1681)::(_55_1679)::[]) -> begin
(let _154_926 = (let _154_925 = (let _154_924 = (let _154_923 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t')
in (let _154_922 = (let _154_921 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_154_921)::[])
in (_154_923)::_154_922))
in ((bind), (_154_924)))
in FStar_Syntax_Syntax.Tm_uinst (_154_925))
in (FStar_Syntax_Syntax.mk _154_926 None e0.FStar_Syntax_Syntax.pos))
end
| _55_1686 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (let _154_940 = (let _154_939 = (let _154_938 = (let _154_937 = (FStar_Syntax_Syntax.as_arg t')
in (let _154_936 = (let _154_935 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_934 = (let _154_933 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _154_932 = (let _154_931 = (FStar_Syntax_Syntax.as_arg lifted_e0)
in (let _154_930 = (let _154_929 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _154_928 = (let _154_927 = (FStar_Syntax_Syntax.as_arg continuation)
in (_154_927)::[])
in (_154_929)::_154_928))
in (_154_931)::_154_930))
in (_154_933)::_154_932))
in (_154_935)::_154_934))
in (_154_937)::_154_936))
in ((bind_inst), (_154_938)))
in FStar_Syntax_Syntax.Tm_app (_154_939))
in (FStar_Syntax_Syntax.mk _154_940 None e0.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (_55_1690)) -> begin
(bind_on_lift es ((((e0), (q)))::acc))
end
| _55_1695 -> begin
(bind_on_lift es ((((e), (q)))::acc))
end)
end))
in (

let binded_head = (let _154_942 = (let _154_941 = (FStar_Syntax_Syntax.as_arg head)
in (_154_941)::args)
in (bind_on_lift _154_942 []))
in (let _154_943 = (FStar_List.tl stack)
in (norm cfg env _154_943 binded_head)))))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (reify_lift cfg.tcenv e msrc mtgt t')
in (norm cfg env stack lifted))
end
| _55_1707 -> begin
(norm cfg env stack head)
end)
end)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _55_1720; FStar_Syntax_Syntax.pos = _55_1718; FStar_Syntax_Syntax.vars = _55_1716}, _55_1725, _55_1727))::_55_1714 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| _55_1732 -> begin
false
end)
in if should_reify then begin
(let _154_945 = (FStar_List.tl stack)
in (let _154_944 = (reify_lift cfg.tcenv head m m' t)
in (norm cfg env _154_945 _154_944)))
end else begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _55_1735 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _55_1735.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end)
end
| _55_1739 -> begin
(match (stack) with
| (_55_1743)::_55_1741 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _55_1748) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _55_1755 -> begin
(norm cfg env stack head)
end)
end
| _55_1757 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _154_946 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_154_946))
end
| _55_1762 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and reify_lift : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> if (FStar_Syntax_Util.is_pure_effect msrc) then begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let _55_1774 = ed.FStar_Syntax_Syntax.return_repr
in (match (_55_1774) with
| (_55_1772, return_repr) -> begin
(

let return_inst = (match ((let _154_952 = (FStar_Syntax_Subst.compress return_repr)
in _154_952.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (_55_1777)::[]) -> begin
(let _154_956 = (let _154_955 = (let _154_954 = (let _154_953 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_154_953)::[])
in ((return_tm), (_154_954)))
in FStar_Syntax_Syntax.Tm_uinst (_154_955))
in (FStar_Syntax_Syntax.mk _154_956 None e.FStar_Syntax_Syntax.pos))
end
| _55_1782 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (let _154_962 = (let _154_961 = (let _154_960 = (let _154_959 = (FStar_Syntax_Syntax.as_arg t)
in (let _154_958 = (let _154_957 = (FStar_Syntax_Syntax.as_arg e)
in (_154_957)::[])
in (_154_959)::_154_958))
in ((return_inst), (_154_960)))
in FStar_Syntax_Syntax.Tm_app (_154_961))
in (FStar_Syntax_Syntax.mk _154_962 None e.FStar_Syntax_Syntax.pos)))
end)))
end else begin
(failwith "NYI: non pure monadic lift normalisation")
end)
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _55_1789 -> (match (_55_1789) with
| (a, imp) -> begin
(let _154_967 = (norm cfg env [] a)
in ((_154_967), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _55_1798 = comp
in (let _154_974 = (let _154_973 = (let _154_972 = (norm cfg env [] t)
in (let _154_971 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_154_972), (_154_971))))
in FStar_Syntax_Syntax.Total (_154_973))
in {FStar_Syntax_Syntax.n = _154_974; FStar_Syntax_Syntax.tk = _55_1798.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _55_1798.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_1798.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _55_1804 = comp
in (let _154_978 = (let _154_977 = (let _154_976 = (norm cfg env [] t)
in (let _154_975 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_154_976), (_154_975))))
in FStar_Syntax_Syntax.GTotal (_154_977))
in {FStar_Syntax_Syntax.n = _154_978; FStar_Syntax_Syntax.tk = _55_1804.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _55_1804.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_1804.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _55_1812 -> (match (_55_1812) with
| (a, i) -> begin
(let _154_982 = (norm cfg env [] a)
in ((_154_982), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _55_8 -> (match (_55_8) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _154_984 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_154_984))
end
| f -> begin
f
end))))
in (

let _55_1818 = comp
in (let _154_989 = (let _154_988 = (

let _55_1820 = ct
in (let _154_987 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _154_986 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _154_985 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _154_987; FStar_Syntax_Syntax.effect_name = _55_1820.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _154_986; FStar_Syntax_Syntax.effect_args = _154_985; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_154_988))
in {FStar_Syntax_Syntax.n = _154_989; FStar_Syntax_Syntax.tk = _55_1818.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _55_1818.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_1818.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _55_1827 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _55_1827.tcenv; delta_level = _55_1827.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _154_997 = (norm t)
in (FStar_Syntax_Util.non_informative _154_997)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_55_1832) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _55_1838 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _55_1838.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _55_1838.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_1838.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _55_1845 = ct
in {FStar_Syntax_Syntax.comp_univs = _55_1845.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _55_1845.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _55_1845.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _55_1845.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _55_1849 = ct
in {FStar_Syntax_Syntax.comp_univs = _55_1849.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _55_1849.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _55_1849.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _55_1849.FStar_Syntax_Syntax.flags}))
end)
in (

let _55_1852 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _55_1852.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _55_1852.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _55_1852.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _55_1855 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _55_1860 -> (match (_55_1860) with
| (x, imp) -> begin
(let _154_1002 = (

let _55_1861 = x
in (let _154_1001 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_1861.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_1861.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_1001}))
in ((_154_1002), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _55_1874 = (FStar_List.fold_left (fun _55_1868 b -> (match (_55_1868) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_55_1874) with
| (nbs, _55_1873) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _154_1014 = (let _154_1013 = (let _154_1012 = (let _154_1011 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags _154_1011 flags))
in (FStar_Syntax_Util.lcomp_of_comp _154_1012))
in FStar_Util.Inl (_154_1013))
in Some (_154_1014))
end else begin
(let _154_1018 = (let _154_1017 = (let _154_1016 = (let _154_1015 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags _154_1015 flags))
in (FStar_Syntax_Util.lcomp_of_comp _154_1016))
in FStar_Util.Inl (_154_1017))
in Some (_154_1018))
end)
end else begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)
end
| _55_1884 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _55_1894 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _154_1024 = (FStar_Syntax_Print.term_to_string tm)
in (let _154_1023 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _154_1024 _154_1023)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _55_1902 = cfg
in {steps = s; tcenv = _55_1902.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _55_1915 = (set_memo r ((env), (t)))
in (

let _55_1918 = (log cfg (fun _55_1917 -> (match (()) with
| () -> begin
(let _154_1026 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _154_1026))
end)))
in (rebuild cfg env stack t)))
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _154_1027 = (

let _55_1941 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _55_1941.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _55_1941.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _55_1941.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _154_1027))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _55_1977), aq, r))::stack -> begin
(

let _55_1986 = (log cfg (fun _55_1985 -> (match (()) with
| () -> begin
(let _154_1029 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _154_1029))
end)))
in if (FStar_List.contains (Exclude (Iota)) cfg.steps) then begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end
end
| Some (_55_1996, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _154_1030 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _154_1030)))
end
| (Match (env, branches, r))::stack -> begin
(

let _55_2017 = (log cfg (fun _55_2016 -> (match (()) with
| () -> begin
(let _154_1032 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _154_1032))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _55_2021 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _55_9 -> (match (_55_9) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _55_2027 -> begin
false
end))))
in (

let steps' = if (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)) then begin
(Exclude (Zeta))::[]
end else begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end
in (

let _55_2030 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = _55_2030.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg_exclude_iota_zeta env t)
end else begin
(norm cfg_exclude_iota_zeta env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_55_2040) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _55_2050 = (norm_pat env hd)
in (match (_55_2050) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _154_1045 = (norm_pat env p)
in (Prims.fst _154_1045)))))
in (((

let _55_2053 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _55_2053.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_2053.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _55_2070 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _55_2061 _55_2064 -> (match (((_55_2061), (_55_2064))) with
| ((pats, env), (p, b)) -> begin
(

let _55_2067 = (norm_pat env p)
in (match (_55_2067) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_55_2070) with
| (pats, env) -> begin
(((

let _55_2071 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _55_2071.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_2071.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _55_2075 = x
in (let _154_1048 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_2075.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2075.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_1048}))
in (((

let _55_2078 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _55_2078.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_2078.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _55_2082 = x
in (let _154_1049 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_2082.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2082.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_1049}))
in (((

let _55_2085 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _55_2085.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_2085.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _55_2091 = x
in (let _154_1050 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _55_2091.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _55_2091.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _154_1050}))
in (

let t = (norm_or_whnf env t)
in (((

let _55_2095 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _55_2095.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _55_2095.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _55_2099 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _55_2104 = (FStar_Syntax_Subst.open_branch branch)
in (match (_55_2104) with
| (p, wopt, e) -> begin
(

let _55_2107 = (norm_pat env p)
in (match (_55_2107) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _154_1052 = (norm_or_whnf env w)
in Some (_154_1052))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _154_1053 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _154_1053)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _55_2118) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _55_2143 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee p -> (

let scrutinee = (FStar_Syntax_Util.unmeta scrutinee)
in (

let _55_2160 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_55_2160) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_55_2166) -> begin
Some (m)
end
| FStar_Util.Inr (true) -> begin
Some (m)
end
| FStar_Util.Inr (false) -> begin
None
end))))
in (match (mopt) with
| None -> begin
FStar_Util.Inr (false)
end
| Some (m) -> begin
m
end))
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
FStar_Util.Inl ((scrutinee)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (_55_2183) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _55_2190 -> begin
(let _154_1070 = (not ((is_cons head)))
in FStar_Util.Inr (_154_1070))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _154_1071 = (FStar_Syntax_Util.un_uinst head)
in _154_1071.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _55_2198 -> begin
(let _154_1072 = (not ((is_cons head)))
in FStar_Util.Inr (_154_1072))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _55_2208))::rest_a, ((p, _55_2214))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _55_2222 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat scrutinee p)) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _55_2240 = (log cfg (fun _55_2239 -> (match (()) with
| () -> begin
(let _154_1083 = (FStar_Syntax_Print.pat_to_string p)
in (let _154_1082 = (let _154_1081 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _154_1081 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _154_1083 _154_1082)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _154_1088 = (let _154_1087 = (let _154_1086 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_154_1086), (false)))
in Clos (_154_1087))
in (_154_1088)::env)) env s)
in (let _154_1089 = (guard_when_clause wopt b rest)
in (norm cfg env stack _154_1089))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun _55_10 -> (match (_55_10) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _55_2253 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _55_2257 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _154_1101 = (config s e)
in (norm _154_1101 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _154_1108 = (config s e)
in (norm_comp _154_1108 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _154_1113 = (config [] env)
in (norm_universe _154_1113 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _154_1118 = (config [] env)
in (ghost_to_pure_aux _154_1118 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _154_1125 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _154_1125)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _55_2276 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _55_2276.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _55_2276.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _55_2278 -> (match (()) with
| () -> begin
(let _154_1127 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _154_1127))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _154_1132 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _154_1132)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _154_1138 = (let _154_1137 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _154_1137 [] c))
in (FStar_Syntax_Print.comp_to_string _154_1138)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _154_1149 = (let _154_1148 = (let _154_1147 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_154_1147)))
in FStar_Syntax_Syntax.Tm_refine (_154_1148))
in (mk _154_1149 t0.FStar_Syntax_Syntax.pos))
end
| _55_2301 -> begin
t
end))
end
| _55_2303 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let _55_2308 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_55_2308) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _55_2311 -> begin
(

let _55_2314 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_55_2314) with
| (binders, args) -> begin
(let _154_1158 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _154_1157 = (let _154_1156 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _154_1154 -> FStar_Util.Inl (_154_1154)))
in (FStar_All.pipe_right _154_1156 (fun _154_1155 -> Some (_154_1155))))
in (FStar_Syntax_Util.abs binders _154_1158 _154_1157)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match ((let _154_1163 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_154_1163), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _55_2320) -> begin
(let _154_1164 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _154_1164))
end
| (_55_2323, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| _55_2328 -> begin
(

let _55_2331 = (FStar_Syntax_Util.head_and_args t)
in (match (_55_2331) with
| (head, args) -> begin
(match ((let _154_1165 = (FStar_Syntax_Subst.compress head)
in _154_1165.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_55_2333, thead) -> begin
(

let _55_2339 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_55_2339) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _55_2347 = (env.FStar_TypeChecker_Env.type_of (

let _55_2340 = env
in {FStar_TypeChecker_Env.solver = _55_2340.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_2340.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_2340.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_2340.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_2340.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_2340.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _55_2340.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_2340.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_2340.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_2340.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_2340.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_2340.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_2340.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_2340.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_2340.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_2340.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_2340.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _55_2340.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _55_2340.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_2340.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _55_2340.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_55_2347) with
| (_55_2343, ty, _55_2346) -> begin
(eta_expand_with_type t ty)
end))
end
end))
end
| _55_2349 -> begin
(

let _55_2357 = (env.FStar_TypeChecker_Env.type_of (

let _55_2350 = env
in {FStar_TypeChecker_Env.solver = _55_2350.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _55_2350.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _55_2350.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _55_2350.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _55_2350.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _55_2350.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _55_2350.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _55_2350.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _55_2350.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _55_2350.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _55_2350.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _55_2350.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _55_2350.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _55_2350.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _55_2350.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _55_2350.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _55_2350.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _55_2350.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _55_2350.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _55_2350.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _55_2350.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_55_2357) with
| (_55_2353, ty, _55_2356) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end))





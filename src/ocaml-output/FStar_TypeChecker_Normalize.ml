
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


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_53_11) -> begin
_53_11
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_14) -> begin
_53_14
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
| Clos (_53_17) -> begin
_53_17
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_20) -> begin
_53_20
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_23, t, _53_26, _53_28) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_32 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range)
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
| Arg (_53_39) -> begin
_53_39
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_42) -> begin
_53_42
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_45) -> begin
_53_45
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_48) -> begin
_53_48
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_51) -> begin
_53_51
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_54) -> begin
_53_54
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_57) -> begin
_53_57
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_60) -> begin
_53_60
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_53_63) -> begin
_53_63
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_53_66) -> begin
_53_66
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_72) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_230 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_230 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_79, _53_81) -> begin
(closure_to_string c)
end
| MemoLazy (_53_85) -> begin
"MemoLazy"
end
| Abs (_53_88, bs, _53_91, _53_93, _53_95) -> begin
(let _147_233 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_233))
end
| _53_99 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_236 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_236 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_106 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_113 -> begin
(let _147_252 = (let _147_251 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_251))
in (FStar_All.failwith _147_252))
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
| _53_129 -> begin
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

let _53_141 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_141) with
| (binders, cdef) -> begin
(

let _53_142 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _147_264 = (let _147_263 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_263)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_147 _53_151 -> (match (((_53_147), (_53_151))) with
| ((x, _53_146), (t, _53_150)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _147_264))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _147_265 = (

let _53_154 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_154.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_154.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_154.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_154.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _147_265 FStar_Syntax_Syntax.mk_Comp))
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

let _53_176 = (FStar_List.fold_left (fun _53_167 u -> (match (_53_167) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_171 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_171) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_176) with
| (_53_173, u, out) -> begin
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
| _53_193 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_186 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(FStar_All.failwith "Universe variable not found")
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

let us = (let _147_282 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_282 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_220 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_220) with
| (_53_218, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_222 -> begin
us
end))
end
| _53_224 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_285 = (aux u)
in (FStar_List.map (fun _147_284 -> FStar_Syntax_Syntax.U_succ (_147_284)) _147_285))
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

let _53_243 = (log cfg (fun _53_242 -> (match (()) with
| () -> begin
(let _147_309 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _147_309 _147_308)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_247 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_250) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_263) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_314 = (let _147_313 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_313))
in (mk _147_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_315 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_315))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_274) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_281) -> begin
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

let _53_297 = (closures_as_binders_delayed cfg env bs)
in (match (_53_297) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _147_318 = (let _147_317 = (let _147_316 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_147_316)))
in FStar_Syntax_Syntax.Tm_abs (_147_317))
in (mk _147_318 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_305 = (closures_as_binders_delayed cfg env bs)
in (match (_53_305) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_313 = (let _147_320 = (let _147_319 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_319)::[])
in (closures_as_binders_delayed cfg env _147_320))
in (match (_53_313) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _147_324 = (let _147_323 = (let _147_322 = (let _147_321 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_321 Prims.fst))
in ((_147_322), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_147_323))
in (mk _147_324 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _147_330 = (let _147_329 = (let _147_328 = (closure_as_term_delayed cfg env t1)
in (let _147_327 = (let _147_326 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _147_325 -> FStar_Util.Inl (_147_325)) _147_326))
in ((_147_328), (_147_327), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_329))
in (mk _147_330 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _147_336 = (let _147_335 = (let _147_334 = (closure_as_term_delayed cfg env t1)
in (let _147_333 = (let _147_332 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _147_331 -> FStar_Util.Inr (_147_331)) _147_332))
in ((_147_334), (_147_333), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_335))
in (mk _147_336 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _147_341 = (let _147_340 = (let _147_339 = (closure_as_term_delayed cfg env t')
in (let _147_338 = (let _147_337 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_147_337))
in ((_147_339), (_147_338))))
in FStar_Syntax_Syntax.Tm_meta (_147_340))
in (mk _147_341 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _147_347 = (let _147_346 = (let _147_345 = (closure_as_term_delayed cfg env t')
in (let _147_344 = (let _147_343 = (let _147_342 = (closure_as_term_delayed cfg env tbody)
in ((m), (_147_342)))
in FStar_Syntax_Syntax.Meta_monadic (_147_343))
in ((_147_345), (_147_344))))
in FStar_Syntax_Syntax.Tm_meta (_147_346))
in (mk _147_347 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_350 = (let _147_349 = (let _147_348 = (closure_as_term_delayed cfg env t')
in ((_147_348), (m)))
in FStar_Syntax_Syntax.Tm_meta (_147_349))
in (mk _147_350 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_352 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_358) -> begin
body
end
| FStar_Util.Inl (_53_361) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_364 = lb
in {FStar_Syntax_Syntax.lbname = _53_364.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_364.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_364.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_368, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_377 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_381 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_385 = lb
in (let _147_362 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_361 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_385.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_385.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_362; FStar_Syntax_Syntax.lbeff = _53_385.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_361}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_388 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_403 -> (match (_53_403) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_408) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_418 = (norm_pat env hd)
in (match (_53_418) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_374 = (norm_pat env p)
in (Prims.fst _147_374)))))
in (((

let _53_421 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_421.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_421.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_438 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_429 _53_432 -> (match (((_53_429), (_53_432))) with
| ((pats, env), (p, b)) -> begin
(

let _53_435 = (norm_pat env p)
in (match (_53_435) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_438) with
| (pats, env) -> begin
(((

let _53_439 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_439.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_439.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_443 = x
in (let _147_377 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_443.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_443.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_377}))
in (((

let _53_446 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_446.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_446.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_450 = x
in (let _147_378 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_450.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_450.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_378}))
in (((

let _53_453 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_453.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_453.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_459 = x
in (let _147_379 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_459.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_459.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_379}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_463 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_463.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_463.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_467 = (norm_pat env pat)
in (match (_53_467) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_380 = (closure_as_term cfg env w)
in Some (_147_380))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _147_383 = (let _147_382 = (let _147_381 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_147_381)))
in FStar_Syntax_Syntax.Tm_match (_147_382))
in (mk _147_383 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_478 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_484 -> begin
(FStar_List.map (fun _53_487 -> (match (_53_487) with
| (x, imp) -> begin
(let _147_391 = (closure_as_term_delayed cfg env x)
in ((_147_391), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_503 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_493 _53_496 -> (match (((_53_493), (_53_496))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_497 = b
in (let _147_397 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_397}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_503) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_509 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _147_402 = (closure_as_term_delayed cfg env t)
in (let _147_401 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _147_402 _147_401)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _147_404 = (closure_as_term_delayed cfg env t)
in (let _147_403 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _147_404 _147_403)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_406 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_406))
end
| f -> begin
f
end))))
in (let _147_408 = (

let _53_527 = c
in (let _147_407 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _147_407; FStar_Syntax_Syntax.effect_name = _53_527.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _147_408)))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_total_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid))
end else begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
Some (FStar_Util.Inr (FStar_Syntax_Const.effect_GTot_lid))
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
end
| _53_536 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _147_421 = (let _147_420 = (FStar_Util.string_of_int i)
in ((_147_420), (None)))
in FStar_Const.Const_int (_147_421)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _147_617 = (let _147_616 = (FStar_List.map (fun m -> (let _147_615 = (let _147_584 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_147_584), ((fun x y -> (int_as_const (x + y))))))
in (let _147_614 = (let _147_613 = (let _147_595 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_147_595), ((fun x y -> (int_as_const (x - y))))))
in (let _147_612 = (let _147_611 = (let _147_606 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_147_606), ((fun x y -> (int_as_const (x * y))))))
in (_147_611)::[])
in (_147_613)::_147_612))
in (_147_615)::_147_614))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _147_616))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _147_617))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let arith_op = (fun fv -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_575 -> (match (_53_575) with
| (l, _53_574) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) arith_ops)
end
| _53_577 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_585))::((a2, _53_581))::[]) -> begin
(match ((arith_op fv)) with
| None -> begin
tm
end
| Some (_53_592, op) -> begin
(

let norm = (fun i j -> (

let c = (let _147_674 = (FStar_Util.int_of_string i)
in (let _147_673 = (FStar_Util.int_of_string j)
in (op _147_674 _147_673)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _147_678 = (let _147_675 = (FStar_Syntax_Subst.compress a1)
in _147_675.FStar_Syntax_Syntax.n)
in (let _147_677 = (let _147_676 = (FStar_Syntax_Subst.compress a2)
in _147_676.FStar_Syntax_Syntax.n)
in ((_147_678), (_147_677))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _53_603))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _53_611))::[])) -> begin
(match ((let _147_686 = (let _147_679 = (FStar_Syntax_Subst.compress head1)
in _147_679.FStar_Syntax_Syntax.n)
in (let _147_685 = (let _147_680 = (FStar_Syntax_Subst.compress head2)
in _147_680.FStar_Syntax_Syntax.n)
in (let _147_684 = (let _147_681 = (FStar_Syntax_Subst.compress arg1)
in _147_681.FStar_Syntax_Syntax.n)
in (let _147_683 = (let _147_682 = (FStar_Syntax_Subst.compress arg2)
in _147_682.FStar_Syntax_Syntax.n)
in ((_147_686), (_147_685), (_147_684), (_147_683))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _147_690 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _147_689 = (let _147_688 = (let _147_687 = (norm i j)
in ((_147_687), (None)))
in (_147_688)::[])
in (FStar_Syntax_Util.mk_app _147_690 _147_689)))
end
| _53_633 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _53_646 -> begin
tm
end))
end)
end
| _53_648 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_653 = t
in {FStar_Syntax_Syntax.n = _53_653.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_653.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_653.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_662 -> begin
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
| _53_740 -> begin
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
| _53_783 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_810))::((_53_801, (arg, _53_804)))::[] -> begin
arg
end
| _53_814 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_818))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_824))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_828 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _147_701 = (FStar_Syntax_Subst.compress t)
in _147_701.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_846)::[], body, _53_850) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_858 -> begin
tm
end)
end
| _53_860 -> begin
tm
end)
end
| _53_862 -> begin
tm
end)
end else begin
tm
end
end
end
end
end
end
| _53_864 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_871 = (log cfg (fun _53_870 -> (match (()) with
| () -> begin
(let _147_734 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_733 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_734 _147_733)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_874) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_916; FStar_Syntax_Syntax.pos = _53_914; FStar_Syntax_Syntax.vars = _53_912}, ((tm, _53_922))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_928 = cfg
in {steps = s; tcenv = _53_928.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_937; FStar_Syntax_Syntax.pos = _53_935; FStar_Syntax_Syntax.vars = _53_933}, (a1)::(a2)::rest) -> begin
(

let _53_951 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_951) with
| (hd, _53_950) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_959; FStar_Syntax_Syntax.pos = _53_957; FStar_Syntax_Syntax.vars = _53_955}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_970 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_970) with
| (reify_head, _53_969) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _147_738 = (FStar_Syntax_Subst.compress e)
in _147_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_990 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_990) with
| (_53_988, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _147_743 = (let _147_742 = (let _147_741 = (let _147_739 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_739)::[])
in (let _147_740 = (FStar_Syntax_Util.mk_reify body)
in ((_147_741), (_147_740), (None))))
in FStar_Syntax_Syntax.Tm_abs (_147_742))
in (FStar_Syntax_Syntax.mk _147_743 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _147_757 = (let _147_756 = (let _147_755 = (let _147_754 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_753 = (let _147_752 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _147_751 = (let _147_750 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_749 = (let _147_748 = (FStar_Syntax_Syntax.as_arg head)
in (let _147_747 = (let _147_746 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_745 = (let _147_744 = (FStar_Syntax_Syntax.as_arg body)
in (_147_744)::[])
in (_147_746)::_147_745))
in (_147_748)::_147_747))
in (_147_750)::_147_749))
in (_147_752)::_147_751))
in (_147_754)::_147_753))
in ((bind_repr), (_147_755)))
in FStar_Syntax_Syntax.Tm_app (_147_756))
in (FStar_Syntax_Syntax.mk _147_757 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_997) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_1000) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_1003 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_1012)); FStar_Syntax_Syntax.tk = _53_1010; FStar_Syntax_Syntax.pos = _53_1008; FStar_Syntax_Syntax.vars = _53_1006}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_1028 -> (match (_53_1028) with
| (pat, wopt, tm) -> begin
(let _147_759 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_147_759)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_1032 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _147_760 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_760)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _147_762 = (let _147_761 = (FStar_List.map (norm_universe cfg env) us)
in ((_147_761), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_147_762))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun _53_5 -> (match (_53_5) with
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
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_1059 = (log cfg (fun _53_1058 -> (match (()) with
| () -> begin
(let _147_766 = (FStar_Syntax_Print.term_to_string t0)
in (let _147_765 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _147_766 _147_765)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1065))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1073 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1075 -> begin
(let _147_770 = (let _147_769 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_769))
in (FStar_All.failwith _147_770))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1079) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _53_1093 = (log cfg (fun _53_1092 -> (match (()) with
| () -> begin
(let _147_773 = (FStar_Syntax_Print.term_to_string t)
in (let _147_772 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_773 _147_772)))
end)))
in (match ((let _147_774 = (FStar_Syntax_Subst.compress t')
in _147_774.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1096) -> begin
(norm cfg env stack t')
end
| _53_1099 -> begin
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
| (UnivArgs (_53_1109))::_53_1107 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1115))::_53_1113 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1121, _53_1123))::stack_rest -> begin
(match (c) with
| Univ (_53_1128) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1131 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1134)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1138 = (log cfg (fun _53_1137 -> (match (()) with
| () -> begin
(let _147_776 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_776))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1144 = (log cfg (fun _53_1143 -> (match (()) with
| () -> begin
(let _147_778 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_778))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1150 = (log cfg (fun _53_1149 -> (match (()) with
| () -> begin
(let _147_780 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_780))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1153 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1155 -> begin
(

let cfg = (

let _53_1156 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1156.tcenv; delta_level = _53_1156.delta_level})
in (let _147_781 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_781)))
end)
end
| (_53_1161)::tl -> begin
(

let _53_1164 = (log cfg (fun _53_1163 -> (match (()) with
| () -> begin
(let _147_783 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_783))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1173 = cfg
in {steps = s; tcenv = _53_1173.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1179 = (set_memo r ((env), (t)))
in (

let _53_1182 = (log cfg (fun _53_1181 -> (match (()) with
| () -> begin
(let _147_785 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_785))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_786 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_786))
end else begin
(

let _53_1218 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1218) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _147_792 = (let _147_790 = (let _147_788 = (let _147_787 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _147_787))
in (FStar_All.pipe_right _147_788 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_790 (fun _147_789 -> FStar_Util.Inl (_147_789))))
in (FStar_All.pipe_right _147_792 (fun _147_791 -> Some (_147_791))))
end
| _53_1223 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1226 -> (Dummy)::env) env))
in (

let _53_1230 = (log cfg (fun _53_1229 -> (match (()) with
| () -> begin
(let _147_796 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_796))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1238 stack -> (match (_53_1238) with
| (a, aq) -> begin
(let _147_803 = (let _147_802 = (let _147_801 = (let _147_800 = (let _147_799 = (FStar_Util.mk_ref None)
in ((env), (a), (_147_799), (false)))
in Clos (_147_800))
in ((_147_801), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_147_802))
in (_147_803)::stack)
end)) args))
in (

let _53_1242 = (log cfg (fun _53_1241 -> (match (()) with
| () -> begin
(let _147_805 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_805))
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

let _53_1252 = x
in {FStar_Syntax_Syntax.ppname = _53_1252.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1252.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1256 -> begin
(let _147_806 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_806))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1260 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1260) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _147_809 = (let _147_808 = (let _147_807 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1262 = x
in {FStar_Syntax_Syntax.ppname = _53_1262.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1262.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_147_807)))
in FStar_Syntax_Syntax.Tm_refine (_147_808))
in (mk _147_809 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_810 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_810))
end else begin
(

let _53_1271 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1271) with
| (bs, c) -> begin
(

let c = (let _147_813 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1273 -> (Dummy)::env) env))
in (norm_comp cfg _147_813 c))
in (

let t = (let _147_814 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_814 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1301 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1304 = (log cfg (fun _53_1303 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _147_816 = (norm cfg env [] t)
in FStar_Util.Inl (_147_816))
end
| FStar_Util.Inr (c) -> begin
(let _147_817 = (norm_comp cfg env c)
in FStar_Util.Inr (_147_817))
end)
in (let _147_818 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_818)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1317, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1329); FStar_Syntax_Syntax.lbunivs = _53_1327; FStar_Syntax_Syntax.lbtyp = _53_1325; FStar_Syntax_Syntax.lbeff = _53_1323; FStar_Syntax_Syntax.lbdef = _53_1321})::_53_1319), _53_1335) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _147_821 = (let _147_820 = (let _147_819 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_147_819), (false)))
in Clos (_147_820))
in (_147_821)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1349 = (let _147_824 = (let _147_823 = (let _147_822 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _147_822 FStar_Syntax_Syntax.mk_binder))
in (_147_823)::[])
in (FStar_Syntax_Subst.open_term _147_824 body))
in (match (_53_1349) with
| (bs, body) -> begin
(

let lb = (

let _53_1350 = lb
in (let _147_830 = (let _147_827 = (let _147_825 = (FStar_List.hd bs)
in (FStar_All.pipe_right _147_825 Prims.fst))
in (FStar_All.pipe_right _147_827 (fun _147_826 -> FStar_Util.Inl (_147_826))))
in (let _147_829 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_828 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _147_830; FStar_Syntax_Syntax.lbunivs = _53_1350.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_829; FStar_Syntax_Syntax.lbeff = _53_1350.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_828}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1354 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _147_833 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_833))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1380 = (FStar_List.fold_right (fun lb _53_1369 -> (match (_53_1369) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _147_836 = (

let _53_1370 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1370.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_836))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1380) with
| (rec_env, memos, _53_1379) -> begin
(

let _53_1383 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _147_843 = (let _147_842 = (let _147_841 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_147_841), (false)))
in Clos (_147_842))
in (_147_843)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1398 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _53_1398.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m') -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1406 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _53_1406.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _53_1410 -> begin
(match (stack) with
| (_53_1414)::_53_1412 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1419) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1426 -> begin
(norm cfg env stack head)
end)
end
| _53_1428 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_844 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_844))
end
| _53_1433 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1441 -> (match (_53_1441) with
| (a, imp) -> begin
(let _147_849 = (norm cfg env [] a)
in ((_147_849), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1450 = comp
in (let _147_856 = (let _147_855 = (let _147_854 = (norm cfg env [] t)
in (let _147_853 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_854), (_147_853))))
in FStar_Syntax_Syntax.Total (_147_855))
in {FStar_Syntax_Syntax.n = _147_856; FStar_Syntax_Syntax.tk = _53_1450.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1450.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1450.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1456 = comp
in (let _147_860 = (let _147_859 = (let _147_858 = (norm cfg env [] t)
in (let _147_857 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_858), (_147_857))))
in FStar_Syntax_Syntax.GTotal (_147_859))
in {FStar_Syntax_Syntax.n = _147_860; FStar_Syntax_Syntax.tk = _53_1456.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1456.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1456.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1464 -> (match (_53_1464) with
| (a, i) -> begin
(let _147_864 = (norm cfg env [] a)
in ((_147_864), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_6 -> (match (_53_6) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_866 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_147_866))
end
| f -> begin
f
end))))
in (

let _53_1470 = comp
in (let _147_871 = (let _147_870 = (

let _53_1472 = ct
in (let _147_869 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _147_868 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_867 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _147_869; FStar_Syntax_Syntax.effect_name = _53_1472.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_868; FStar_Syntax_Syntax.effect_args = _147_867; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_147_870))
in {FStar_Syntax_Syntax.n = _147_871; FStar_Syntax_Syntax.tk = _53_1470.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1470.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1470.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1479 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1479.tcenv; delta_level = _53_1479.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _147_879 = (norm t)
in (FStar_Syntax_Util.non_informative _147_879)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1484) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1490 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1490.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1490.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1490.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1497 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1497.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1497.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1497.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1497.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1501 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1501.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1501.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1501.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1501.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1504 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1504.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1504.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1504.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1507 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1512 -> (match (_53_1512) with
| (x, imp) -> begin
(let _147_884 = (

let _53_1513 = x
in (let _147_883 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1513.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1513.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_883}))
in ((_147_884), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1526 = (FStar_List.fold_left (fun _53_1520 b -> (match (_53_1520) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1526) with
| (nbs, _53_1525) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _147_895 = (let _147_894 = (let _147_893 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _147_893))
in FStar_Util.Inl (_147_894))
in Some (_147_895))
end else begin
(let _147_898 = (let _147_897 = (let _147_896 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _147_896))
in FStar_Util.Inl (_147_897))
in Some (_147_898))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1535 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _53_1545 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _147_904 = (FStar_Syntax_Print.term_to_string tm)
in (let _147_903 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _147_904 _147_903)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1553 = cfg
in {steps = s; tcenv = _53_1553.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1566 = (set_memo r ((env), (t)))
in (

let _53_1569 = (log cfg (fun _53_1568 -> (match (()) with
| () -> begin
(let _147_906 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_906))
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
in (let _147_907 = (

let _53_1592 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1592.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1592.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1592.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_907))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1628), aq, r))::stack -> begin
(

let _53_1637 = (log cfg (fun _53_1636 -> (match (()) with
| () -> begin
(let _147_909 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_909))
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
| Some (_53_1647, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _147_910 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_910)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1668 = (log cfg (fun _53_1667 -> (match (()) with
| () -> begin
(let _147_912 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _147_912))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _53_1672 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _53_7 -> (match (_53_7) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _53_1678 -> begin
false
end))))
in (

let _53_1680 = cfg
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1680.tcenv; delta_level = new_delta}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1690) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1700 = (norm_pat env hd)
in (match (_53_1700) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_925 = (norm_pat env p)
in (Prims.fst _147_925)))))
in (((

let _53_1703 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1703.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1703.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1720 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1711 _53_1714 -> (match (((_53_1711), (_53_1714))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1717 = (norm_pat env p)
in (match (_53_1717) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1720) with
| (pats, env) -> begin
(((

let _53_1721 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1721.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1721.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1725 = x
in (let _147_928 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1725.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1725.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_928}))
in (((

let _53_1728 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1728.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1728.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1732 = x
in (let _147_929 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1732.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1732.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_929}))
in (((

let _53_1735 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1735.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1735.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1741 = x
in (let _147_930 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1741.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1741.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_930}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1745 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1745.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1745.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1749 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1754 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1754) with
| (p, wopt, e) -> begin
(

let _53_1757 = (norm_pat env p)
in (match (_53_1757) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_932 = (norm_or_whnf env w)
in Some (_147_932))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _147_933 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _147_933)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1768) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1793 -> begin
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

let _53_1810 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_53_1810) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_53_1816) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1833) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1840 -> begin
(let _147_950 = (not ((is_cons head)))
in FStar_Util.Inr (_147_950))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _147_951 = (FStar_Syntax_Util.un_uinst head)
in _147_951.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1848 -> begin
(let _147_952 = (not ((is_cons head)))
in FStar_Util.Inr (_147_952))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1858))::rest_a, ((p, _53_1864))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1872 -> begin
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

let _53_1890 = (log cfg (fun _53_1889 -> (match (()) with
| () -> begin
(let _147_963 = (FStar_Syntax_Print.pat_to_string p)
in (let _147_962 = (let _147_961 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _147_961 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _147_963 _147_962)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _147_968 = (let _147_967 = (let _147_966 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_147_966), (false)))
in Clos (_147_967))
in (_147_968)::env)) env s)
in (let _147_969 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_969))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun _53_8 -> (match (_53_8) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _53_1903 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _53_1907 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_981 = (config s e)
in (norm _147_981 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_988 = (config s e)
in (norm_comp _147_988 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_993 = (config [] env)
in (norm_universe _147_993 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_998 = (config [] env)
in (ghost_to_pure_aux _147_998 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _147_1005 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _147_1005)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1926 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1926.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1926.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1928 -> (match (()) with
| () -> begin
(let _147_1007 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _147_1007))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_1012 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_1012)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_1018 = (let _147_1017 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_1017 [] c))
in (FStar_Syntax_Print.comp_to_string _147_1018)))


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
(let _147_1029 = (let _147_1028 = (let _147_1027 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_147_1027)))
in FStar_Syntax_Syntax.Tm_refine (_147_1028))
in (mk _147_1029 t0.FStar_Syntax_Syntax.pos))
end
| _53_1951 -> begin
t
end))
end
| _53_1953 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1960 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1960) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1963 -> begin
(

let _53_1966 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1966) with
| (binders, args) -> begin
(let _147_1040 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_1039 = (let _147_1038 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1036 -> FStar_Util.Inl (_147_1036)))
in (FStar_All.pipe_right _147_1038 (fun _147_1037 -> Some (_147_1037))))
in (FStar_Syntax_Util.abs binders _147_1040 _147_1039)))
end))
end)
end)))
in (match ((let _147_1041 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_147_1041), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1970) -> begin
(let _147_1042 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _147_1042))
end
| (_53_1973, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1978 -> begin
(

let _53_1981 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1981) with
| (head, args) -> begin
(match ((let _147_1043 = (FStar_Syntax_Subst.compress head)
in _147_1043.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1983, thead) -> begin
(

let _53_1989 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1989) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1997 = (env.FStar_TypeChecker_Env.type_of (

let _53_1990 = env
in {FStar_TypeChecker_Env.solver = _53_1990.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1990.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1990.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1990.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1990.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1990.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1990.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1990.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1990.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1990.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1990.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1990.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1990.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1990.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1990.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1990.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1990.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1990.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1990.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1990.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1990.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1997) with
| (_53_1993, ty, _53_1996) -> begin
(expand ty)
end))
end
end))
end
| _53_1999 -> begin
(

let _53_2007 = (env.FStar_TypeChecker_Env.type_of (

let _53_2000 = env
in {FStar_TypeChecker_Env.solver = _53_2000.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_2000.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_2000.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_2000.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_2000.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_2000.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_2000.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_2000.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_2000.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_2000.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_2000.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_2000.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_2000.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_2000.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_2000.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_2000.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_2000.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_2000.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_2000.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_2000.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_2000.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_2007) with
| (_53_2003, ty, _53_2006) -> begin
(expand ty)
end))
end)
end))
end)))





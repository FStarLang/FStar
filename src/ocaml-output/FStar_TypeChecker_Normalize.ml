
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
| Exclude (_53_12) -> begin
_53_12
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_15) -> begin
_53_15
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
| Clos (_53_18) -> begin
_53_18
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_21) -> begin
_53_21
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_24, t, _53_27, _53_29) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_33 -> begin
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
| Arg (_53_40) -> begin
_53_40
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_43) -> begin
_53_43
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_46) -> begin
_53_46
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_49) -> begin
_53_49
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_52) -> begin
_53_52
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_55) -> begin
_53_55
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_58) -> begin
_53_58
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_61) -> begin
_53_61
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_53_64) -> begin
_53_64
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_53_67) -> begin
_53_67
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_73) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _148_231 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _148_231 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_80, _53_82) -> begin
(closure_to_string c)
end
| MemoLazy (_53_86) -> begin
"MemoLazy"
end
| Abs (_53_89, bs, _53_92, _53_94, _53_96) -> begin
(let _148_234 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _148_234))
end
| _53_100 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _148_237 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _148_237 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_107 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_114 -> begin
(let _148_253 = (let _148_252 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _148_252))
in (FStar_All.failwith _148_253))
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
| _53_130 -> begin
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

let _53_142 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_142) with
| (binders, cdef) -> begin
(

let _53_143 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _148_265 = (let _148_264 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_148_264)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_148 _53_152 -> (match (((_53_148), (_53_152))) with
| ((x, _53_147), (t, _53_151)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _148_265))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _148_266 = (

let _53_155 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_155.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_155.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_155.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_155.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _148_266 FStar_Syntax_Syntax.mk_Comp))
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

let _53_177 = (FStar_List.fold_left (fun _53_168 u -> (match (_53_168) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_172 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_172) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_177) with
| (_53_174, u, out) -> begin
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
| _53_194 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_187 -> begin
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

let us = (let _148_283 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _148_283 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_221 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_221) with
| (_53_219, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_223 -> begin
us
end))
end
| _53_225 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _148_286 = (aux u)
in (FStar_List.map (fun _148_285 -> FStar_Syntax_Syntax.U_succ (_148_285)) _148_286))
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

let _53_244 = (log cfg (fun _53_243 -> (match (()) with
| () -> begin
(let _148_311 = (FStar_Syntax_Print.tag_of_term t)
in (let _148_310 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _148_311 _148_310)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_248 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_251) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_264) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _148_316 = (let _148_315 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_148_315))
in (mk _148_316 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _148_317 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _148_317))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_275) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_282) -> begin
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

let _53_298 = (closures_as_binders_delayed cfg env bs)
in (match (_53_298) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _148_320 = (let _148_319 = (let _148_318 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_148_318)))
in FStar_Syntax_Syntax.Tm_abs (_148_319))
in (mk _148_320 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_306 = (closures_as_binders_delayed cfg env bs)
in (match (_53_306) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_314 = (let _148_322 = (let _148_321 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_321)::[])
in (closures_as_binders_delayed cfg env _148_322))
in (match (_53_314) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _148_326 = (let _148_325 = (let _148_324 = (let _148_323 = (FStar_List.hd x)
in (FStar_All.pipe_right _148_323 Prims.fst))
in ((_148_324), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_148_325))
in (mk _148_326 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _148_332 = (let _148_331 = (let _148_330 = (closure_as_term_delayed cfg env t1)
in (let _148_329 = (let _148_328 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _148_327 -> FStar_Util.Inl (_148_327)) _148_328))
in ((_148_330), (_148_329), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_148_331))
in (mk _148_332 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _148_338 = (let _148_337 = (let _148_336 = (closure_as_term_delayed cfg env t1)
in (let _148_335 = (let _148_334 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _148_333 -> FStar_Util.Inr (_148_333)) _148_334))
in ((_148_336), (_148_335), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_148_337))
in (mk _148_338 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _148_343 = (let _148_342 = (let _148_341 = (closure_as_term_delayed cfg env t')
in (let _148_340 = (let _148_339 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_148_339))
in ((_148_341), (_148_340))))
in FStar_Syntax_Syntax.Tm_meta (_148_342))
in (mk _148_343 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _148_349 = (let _148_348 = (let _148_347 = (closure_as_term_delayed cfg env t')
in (let _148_346 = (let _148_345 = (let _148_344 = (closure_as_term_delayed cfg env tbody)
in ((m), (_148_344)))
in FStar_Syntax_Syntax.Meta_monadic (_148_345))
in ((_148_347), (_148_346))))
in FStar_Syntax_Syntax.Tm_meta (_148_348))
in (mk _148_349 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _148_352 = (let _148_351 = (let _148_350 = (closure_as_term_delayed cfg env t')
in ((_148_350), (m)))
in FStar_Syntax_Syntax.Tm_meta (_148_351))
in (mk _148_352 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_353 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_359) -> begin
body
end
| FStar_Util.Inl (_53_362) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_365 = lb
in {FStar_Syntax_Syntax.lbname = _53_365.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_365.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_365.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_369, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_378 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_382 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_386 = lb
in (let _148_364 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_363 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_386.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_386.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _148_364; FStar_Syntax_Syntax.lbeff = _53_386.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _148_363}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_389 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_404 -> (match (_53_404) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_409) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_419 = (norm_pat env hd)
in (match (_53_419) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _148_376 = (norm_pat env p)
in (Prims.fst _148_376)))))
in (((

let _53_422 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_422.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_422.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_439 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_430 _53_433 -> (match (((_53_430), (_53_433))) with
| ((pats, env), (p, b)) -> begin
(

let _53_436 = (norm_pat env p)
in (match (_53_436) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_439) with
| (pats, env) -> begin
(((

let _53_440 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_440.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_440.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_444 = x
in (let _148_379 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_444.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_444.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_379}))
in (((

let _53_447 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_447.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_447.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_451 = x
in (let _148_380 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_451.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_451.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_380}))
in (((

let _53_454 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_454.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_454.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_460 = x
in (let _148_381 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_460.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_460.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_381}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_464 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_464.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_464.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_468 = (norm_pat env pat)
in (match (_53_468) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_382 = (closure_as_term cfg env w)
in Some (_148_382))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _148_385 = (let _148_384 = (let _148_383 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_148_383)))
in FStar_Syntax_Syntax.Tm_match (_148_384))
in (mk _148_385 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_479 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_485 -> begin
(FStar_List.map (fun _53_488 -> (match (_53_488) with
| (x, imp) -> begin
(let _148_393 = (closure_as_term_delayed cfg env x)
in ((_148_393), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_504 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_494 _53_497 -> (match (((_53_494), (_53_497))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_498 = b
in (let _148_399 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_498.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_498.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_399}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_504) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_510 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _148_404 = (closure_as_term_delayed cfg env t)
in (let _148_403 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _148_404 _148_403)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _148_406 = (closure_as_term_delayed cfg env t)
in (let _148_405 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _148_406 _148_405)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _148_408 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_148_408))
end
| f -> begin
f
end))))
in (let _148_410 = (

let _53_528 = c
in (let _148_409 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _148_409; FStar_Syntax_Syntax.effect_name = _53_528.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _148_410)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun _53_5 -> (match (_53_5) with
| FStar_Syntax_Syntax.DECREASES (_53_533) -> begin
false
end
| _53_536 -> begin
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
| _53_545 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _148_425 = (let _148_424 = (FStar_Util.string_of_int i)
in ((_148_424), (None)))
in FStar_Const.Const_int (_148_425)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _148_621 = (let _148_620 = (FStar_List.map (fun m -> (let _148_619 = (let _148_588 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_148_588), ((fun x y -> (int_as_const (x + y))))))
in (let _148_618 = (let _148_617 = (let _148_599 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_148_599), ((fun x y -> (int_as_const (x - y))))))
in (let _148_616 = (let _148_615 = (let _148_610 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_148_610), ((fun x y -> (int_as_const (x * y))))))
in (_148_615)::[])
in (_148_617)::_148_616))
in (_148_619)::_148_618))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _148_620))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _148_621))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (let _148_631 = (let _148_630 = (let _148_629 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _148_629 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (_148_630))
in (mk _148_631)))
in (

let ctor = (fun x -> (let _148_636 = (let _148_635 = (let _148_634 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _148_634 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (_148_635))
in (mk _148_636)))
in (let _148_666 = (let _148_663 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_148_663), ((fun s -> (let _148_662 = (FStar_String.list_of_string s)
in (let _148_661 = (let _148_660 = (let _148_659 = (let _148_658 = (let _148_654 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_654 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _148_657 = (let _148_656 = (let _148_655 = (name (("FStar")::("Char")::("char")::[]))
in ((_148_655), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_148_656)::[])
in ((_148_658), (_148_657))))
in FStar_Syntax_Syntax.Tm_app (_148_659))
in (mk _148_660))
in (FStar_List.fold_right (fun c a -> (let _148_653 = (let _148_652 = (let _148_651 = (let _148_644 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _148_644 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _148_650 = (let _148_649 = (let _148_645 = (name (("FStar")::("Char")::("char")::[]))
in ((_148_645), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _148_648 = (let _148_647 = (let _148_646 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_148_646), (None)))
in (_148_647)::(((a), (None)))::[])
in (_148_649)::_148_648))
in ((_148_651), (_148_650))))
in FStar_Syntax_Syntax.Tm_app (_148_652))
in (mk _148_653))) _148_662 _148_661)))))))
in (_148_666)::[]))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let find = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_595 -> (match (_53_595) with
| (l, _53_594) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| _53_597 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_605))::((a2, _53_601))::[]) -> begin
(match ((find fv arith_ops)) with
| None -> begin
tm
end
| Some (_53_612, op) -> begin
(

let norm = (fun i j -> (

let c = (let _148_683 = (FStar_Util.int_of_string i)
in (let _148_682 = (FStar_Util.int_of_string j)
in (op _148_683 _148_682)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _148_687 = (let _148_684 = (FStar_Syntax_Subst.compress a1)
in _148_684.FStar_Syntax_Syntax.n)
in (let _148_686 = (let _148_685 = (FStar_Syntax_Subst.compress a2)
in _148_685.FStar_Syntax_Syntax.n)
in ((_148_687), (_148_686))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _53_623))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _53_631))::[])) -> begin
(match ((let _148_695 = (let _148_688 = (FStar_Syntax_Subst.compress head1)
in _148_688.FStar_Syntax_Syntax.n)
in (let _148_694 = (let _148_689 = (FStar_Syntax_Subst.compress head2)
in _148_689.FStar_Syntax_Syntax.n)
in (let _148_693 = (let _148_690 = (FStar_Syntax_Subst.compress arg1)
in _148_690.FStar_Syntax_Syntax.n)
in (let _148_692 = (let _148_691 = (FStar_Syntax_Subst.compress arg2)
in _148_691.FStar_Syntax_Syntax.n)
in ((_148_695), (_148_694), (_148_693), (_148_692))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _148_699 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _148_698 = (let _148_697 = (let _148_696 = (norm i j)
in ((_148_696), (None)))
in (_148_697)::[])
in (FStar_Syntax_Util.mk_app _148_699 _148_698)))
end
| _53_653 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _53_666 -> begin
tm
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_670))::[]) -> begin
(match ((find fv un_ops)) with
| None -> begin
tm
end
| Some (_53_677, op) -> begin
(match ((let _148_702 = (FStar_Syntax_Subst.compress a1)
in _148_702.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, _53_683)) -> begin
(let _148_703 = (FStar_Bytes.unicode_bytes_as_string b)
in (op _148_703))
end
| _53_688 -> begin
tm
end)
end)
end
| _53_690 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_695 = t
in {FStar_Syntax_Syntax.n = _53_695.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_695.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_695.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_704 -> begin
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
| _53_782 -> begin
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
| _53_825 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_852))::((_53_843, (arg, _53_846)))::[] -> begin
arg
end
| _53_856 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_860))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_866))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_870 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _148_714 = (FStar_Syntax_Subst.compress t)
in _148_714.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_888)::[], body, _53_892) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_900 -> begin
tm
end)
end
| _53_902 -> begin
tm
end)
end
| _53_904 -> begin
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
| _53_906 -> begin
tm
end)
end))))


let is_norm_request = (fun hd args -> (match ((let _148_718 = (let _148_717 = (FStar_Syntax_Util.un_uinst hd)
in _148_717.FStar_Syntax_Syntax.n)
in ((_148_718), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_53_914)::(_53_912)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_53_920)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| _53_924 -> begin
false
end))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| _53_938 -> begin
(FStar_All.failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_945 = (log cfg (fun _53_944 -> (match (()) with
| () -> begin
(let _148_752 = (FStar_Syntax_Print.tag_of_term t)
in (let _148_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _148_752 _148_751)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_948) -> begin
(FStar_All.failwith "Impossible")
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

let _53_991 = cfg
in {steps = s; tcenv = _53_991.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_1000; FStar_Syntax_Syntax.pos = _53_998; FStar_Syntax_Syntax.vars = _53_996}, (a1)::(a2)::rest) -> begin
(

let _53_1014 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1014) with
| (hd, _53_1013) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_1022; FStar_Syntax_Syntax.pos = _53_1020; FStar_Syntax_Syntax.vars = _53_1018}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_1033 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1033) with
| (reify_head, _53_1032) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _148_756 = (FStar_Syntax_Subst.compress e)
in _148_756.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_1053 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_1053) with
| (_53_1051, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _148_761 = (let _148_760 = (let _148_759 = (let _148_757 = (FStar_Syntax_Syntax.mk_binder x)
in (_148_757)::[])
in (let _148_758 = (FStar_Syntax_Util.mk_reify body)
in ((_148_759), (_148_758), (None))))
in FStar_Syntax_Syntax.Tm_abs (_148_760))
in (FStar_Syntax_Syntax.mk _148_761 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _148_775 = (let _148_774 = (let _148_773 = (let _148_772 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_771 = (let _148_770 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _148_769 = (let _148_768 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_767 = (let _148_766 = (FStar_Syntax_Syntax.as_arg head)
in (let _148_765 = (let _148_764 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _148_763 = (let _148_762 = (FStar_Syntax_Syntax.as_arg body)
in (_148_762)::[])
in (_148_764)::_148_763))
in (_148_766)::_148_765))
in (_148_768)::_148_767))
in (_148_770)::_148_769))
in (_148_772)::_148_771))
in ((bind_repr), (_148_773)))
in FStar_Syntax_Syntax.Tm_app (_148_774))
in (FStar_Syntax_Syntax.mk _148_775 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_1060) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_1063) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_1066 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_1075)); FStar_Syntax_Syntax.tk = _53_1073; FStar_Syntax_Syntax.pos = _53_1071; FStar_Syntax_Syntax.vars = _53_1069}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_1091 -> (match (_53_1091) with
| (pat, wopt, tm) -> begin
(let _148_777 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_148_777)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_1095 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _148_778 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _148_778)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _148_780 = (let _148_779 = (FStar_List.map (norm_universe cfg env) us)
in ((_148_779), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_148_780))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun _53_6 -> (match (_53_6) with
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

let r_env = (let _148_782 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _148_782))
in (match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_1123 = (log cfg (fun _53_1122 -> (match (()) with
| () -> begin
(let _148_785 = (FStar_Syntax_Print.term_to_string t0)
in (let _148_784 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _148_785 _148_784)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1129))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1137 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1139 -> begin
(let _148_789 = (let _148_788 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _148_788))
in (FStar_All.failwith _148_789))
end)
end else begin
(norm cfg env stack t)
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1143) -> begin
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

let _53_1157 = (log cfg (fun _53_1156 -> (match (()) with
| () -> begin
(let _148_792 = (FStar_Syntax_Print.term_to_string t)
in (let _148_791 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _148_792 _148_791)))
end)))
in (match ((let _148_793 = (FStar_Syntax_Subst.compress t')
in _148_793.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1160) -> begin
(norm cfg env stack t')
end
| _53_1163 -> begin
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
| (UnivArgs (_53_1173))::_53_1171 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1179))::_53_1177 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1185, _53_1187))::stack_rest -> begin
(match (c) with
| Univ (_53_1192) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1195 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1198)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1202 = (log cfg (fun _53_1201 -> (match (()) with
| () -> begin
(let _148_795 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_795))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l, cflags)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1210 = (log cfg (fun _53_1209 -> (match (()) with
| () -> begin
(let _148_797 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_797))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1216 = (log cfg (fun _53_1215 -> (match (()) with
| () -> begin
(let _148_799 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_799))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1219 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1221 -> begin
(

let cfg = (

let _53_1222 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1222.tcenv; delta_level = _53_1222.delta_level})
in (let _148_800 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_800)))
end)
end
| (_53_1227)::tl -> begin
(

let _53_1230 = (log cfg (fun _53_1229 -> (match (()) with
| () -> begin
(let _148_802 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _148_802))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1239 = cfg
in {steps = s; tcenv = _53_1239.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1245 = (set_memo r ((env), (t)))
in (

let _53_1248 = (log cfg (fun _53_1247 -> (match (()) with
| () -> begin
(let _148_804 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _148_804))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _148_805 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_805))
end else begin
(

let _53_1284 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1284) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _148_811 = (let _148_809 = (let _148_807 = (let _148_806 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _148_806))
in (FStar_All.pipe_right _148_807 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _148_809 (fun _148_808 -> FStar_Util.Inl (_148_808))))
in (FStar_All.pipe_right _148_811 (fun _148_810 -> Some (_148_810))))
end
| _53_1289 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1292 -> (Dummy)::env) env))
in (

let _53_1296 = (log cfg (fun _53_1295 -> (match (()) with
| () -> begin
(let _148_815 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _148_815))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1304 stack -> (match (_53_1304) with
| (a, aq) -> begin
(let _148_822 = (let _148_821 = (let _148_820 = (let _148_819 = (let _148_818 = (FStar_Util.mk_ref None)
in ((env), (a), (_148_818), (false)))
in Clos (_148_819))
in ((_148_820), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_148_821))
in (_148_822)::stack)
end)) args))
in (

let _53_1308 = (log cfg (fun _53_1307 -> (match (()) with
| () -> begin
(let _148_824 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _148_824))
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

let _53_1318 = x
in {FStar_Syntax_Syntax.ppname = _53_1318.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1322 -> begin
(let _148_825 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_825))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1326 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1326) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _148_828 = (let _148_827 = (let _148_826 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1328 = x
in {FStar_Syntax_Syntax.ppname = _53_1328.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1328.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_148_826)))
in FStar_Syntax_Syntax.Tm_refine (_148_827))
in (mk _148_828 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _148_829 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_829))
end else begin
(

let _53_1337 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1337) with
| (bs, c) -> begin
(

let c = (let _148_832 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1339 -> (Dummy)::env) env))
in (norm_comp cfg _148_832 c))
in (

let t = (let _148_833 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _148_833 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1367 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1370 = (log cfg (fun _53_1369 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _148_835 = (norm cfg env [] t)
in FStar_Util.Inl (_148_835))
end
| FStar_Util.Inr (c) -> begin
(let _148_836 = (norm_comp cfg env c)
in FStar_Util.Inr (_148_836))
end)
in (let _148_837 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _148_837)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1383, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1395); FStar_Syntax_Syntax.lbunivs = _53_1393; FStar_Syntax_Syntax.lbtyp = _53_1391; FStar_Syntax_Syntax.lbeff = _53_1389; FStar_Syntax_Syntax.lbdef = _53_1387})::_53_1385), _53_1401) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))))))) then begin
(

let env = (let _148_840 = (let _148_839 = (let _148_838 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_148_838), (false)))
in Clos (_148_839))
in (_148_840)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1415 = (let _148_843 = (let _148_842 = (let _148_841 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _148_841 FStar_Syntax_Syntax.mk_binder))
in (_148_842)::[])
in (FStar_Syntax_Subst.open_term _148_843 body))
in (match (_53_1415) with
| (bs, body) -> begin
(

let lb = (

let _53_1416 = lb
in (let _148_849 = (let _148_846 = (let _148_844 = (FStar_List.hd bs)
in (FStar_All.pipe_right _148_844 Prims.fst))
in (FStar_All.pipe_right _148_846 (fun _148_845 -> FStar_Util.Inl (_148_845))))
in (let _148_848 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _148_847 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _148_849; FStar_Syntax_Syntax.lbunivs = _53_1416.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _148_848; FStar_Syntax_Syntax.lbeff = _53_1416.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _148_847}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1420 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _148_852 = (closure_as_term cfg env t)
in (rebuild cfg env stack _148_852))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1446 = (FStar_List.fold_right (fun lb _53_1435 -> (match (_53_1435) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _148_855 = (

let _53_1436 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1436.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _148_855))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1446) with
| (rec_env, memos, _53_1445) -> begin
(

let _53_1449 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _148_862 = (let _148_861 = (let _148_860 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_148_860), (false)))
in Clos (_148_861))
in (_148_862)::env)) (Prims.snd lbs) env)
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

let _53_1464 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _53_1464.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m') -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1472 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _53_1472.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _53_1476 -> begin
(match (stack) with
| (_53_1480)::_53_1478 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1485) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1492 -> begin
(norm cfg env stack head)
end)
end
| _53_1494 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _148_863 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_148_863))
end
| _53_1499 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1507 -> (match (_53_1507) with
| (a, imp) -> begin
(let _148_868 = (norm cfg env [] a)
in ((_148_868), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1516 = comp
in (let _148_875 = (let _148_874 = (let _148_873 = (norm cfg env [] t)
in (let _148_872 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_148_873), (_148_872))))
in FStar_Syntax_Syntax.Total (_148_874))
in {FStar_Syntax_Syntax.n = _148_875; FStar_Syntax_Syntax.tk = _53_1516.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1516.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1516.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1522 = comp
in (let _148_879 = (let _148_878 = (let _148_877 = (norm cfg env [] t)
in (let _148_876 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_148_877), (_148_876))))
in FStar_Syntax_Syntax.GTotal (_148_878))
in {FStar_Syntax_Syntax.n = _148_879; FStar_Syntax_Syntax.tk = _53_1522.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1522.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1522.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1530 -> (match (_53_1530) with
| (a, i) -> begin
(let _148_883 = (norm cfg env [] a)
in ((_148_883), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_7 -> (match (_53_7) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _148_885 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_148_885))
end
| f -> begin
f
end))))
in (

let _53_1536 = comp
in (let _148_890 = (let _148_889 = (

let _53_1538 = ct
in (let _148_888 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _148_887 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _148_886 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _148_888; FStar_Syntax_Syntax.effect_name = _53_1538.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _148_887; FStar_Syntax_Syntax.effect_args = _148_886; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_148_889))
in {FStar_Syntax_Syntax.n = _148_890; FStar_Syntax_Syntax.tk = _53_1536.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1536.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1536.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1545 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1545.tcenv; delta_level = _53_1545.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _148_898 = (norm t)
in (FStar_Syntax_Util.non_informative _148_898)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1550) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1556 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1556.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1556.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1556.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1563 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1563.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1563.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1563.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1563.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1567 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1567.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1567.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1567.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1567.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1570 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1570.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1570.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1570.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1573 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1578 -> (match (_53_1578) with
| (x, imp) -> begin
(let _148_903 = (

let _53_1579 = x
in (let _148_902 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1579.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1579.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_902}))
in ((_148_903), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1592 = (FStar_List.fold_left (fun _53_1586 b -> (match (_53_1586) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1592) with
| (nbs, _53_1591) -> begin
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
(let _148_915 = (let _148_914 = (let _148_913 = (let _148_912 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags _148_912 flags))
in (FStar_Syntax_Util.lcomp_of_comp _148_913))
in FStar_Util.Inl (_148_914))
in Some (_148_915))
end else begin
(let _148_919 = (let _148_918 = (let _148_917 = (let _148_916 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags _148_916 flags))
in (FStar_Syntax_Util.lcomp_of_comp _148_917))
in FStar_Util.Inl (_148_918))
in Some (_148_919))
end)
end else begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)
end
| _53_1602 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _53_1612 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _148_925 = (FStar_Syntax_Print.term_to_string tm)
in (let _148_924 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _148_925 _148_924)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1620 = cfg
in {steps = s; tcenv = _53_1620.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1633 = (set_memo r ((env), (t)))
in (

let _53_1636 = (log cfg (fun _53_1635 -> (match (()) with
| () -> begin
(let _148_927 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _148_927))
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
in (let _148_928 = (

let _53_1659 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1659.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1659.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1659.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _148_928))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1695), aq, r))::stack -> begin
(

let _53_1704 = (log cfg (fun _53_1703 -> (match (()) with
| () -> begin
(let _148_930 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _148_930))
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
| Some (_53_1714, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _148_931 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _148_931)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1735 = (log cfg (fun _53_1734 -> (match (()) with
| () -> begin
(let _148_933 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _148_933))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _53_1739 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _53_8 -> (match (_53_8) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _53_1745 -> begin
false
end))))
in (

let steps' = if (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)) then begin
(Exclude (Zeta))::[]
end else begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end
in (

let _53_1748 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = _53_1748.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg_exclude_iota_zeta env t)
end else begin
(norm cfg_exclude_iota_zeta env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1758) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1768 = (norm_pat env hd)
in (match (_53_1768) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _148_946 = (norm_pat env p)
in (Prims.fst _148_946)))))
in (((

let _53_1771 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1771.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1771.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1788 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1779 _53_1782 -> (match (((_53_1779), (_53_1782))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1785 = (norm_pat env p)
in (match (_53_1785) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1788) with
| (pats, env) -> begin
(((

let _53_1789 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1789.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1789.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1793 = x
in (let _148_949 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1793.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1793.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_949}))
in (((

let _53_1796 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1796.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1796.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1800 = x
in (let _148_950 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1800.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1800.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_950}))
in (((

let _53_1803 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1803.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1803.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1809 = x
in (let _148_951 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1809.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1809.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _148_951}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1813 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1813.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1813.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1817 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1822 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1822) with
| (p, wopt, e) -> begin
(

let _53_1825 = (norm_pat env p)
in (match (_53_1825) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _148_953 = (norm_or_whnf env w)
in Some (_148_953))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _148_954 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _148_954)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1836) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1861 -> begin
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

let _53_1878 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_53_1878) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_53_1884) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1901) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1908 -> begin
(let _148_971 = (not ((is_cons head)))
in FStar_Util.Inr (_148_971))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _148_972 = (FStar_Syntax_Util.un_uinst head)
in _148_972.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1916 -> begin
(let _148_973 = (not ((is_cons head)))
in FStar_Util.Inr (_148_973))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1926))::rest_a, ((p, _53_1932))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1940 -> begin
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

let _53_1958 = (log cfg (fun _53_1957 -> (match (()) with
| () -> begin
(let _148_984 = (FStar_Syntax_Print.pat_to_string p)
in (let _148_983 = (let _148_982 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _148_982 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _148_984 _148_983)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _148_989 = (let _148_988 = (let _148_987 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_148_987), (false)))
in Clos (_148_988))
in (_148_989)::env)) env s)
in (let _148_990 = (guard_when_clause wopt b rest)
in (norm cfg env stack _148_990))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun _53_9 -> (match (_53_9) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _53_1971 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _53_1975 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _148_1002 = (config s e)
in (norm _148_1002 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _148_1009 = (config s e)
in (norm_comp _148_1009 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _148_1014 = (config [] env)
in (norm_universe _148_1014 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _148_1019 = (config [] env)
in (ghost_to_pure_aux _148_1019 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _148_1026 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _148_1026)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1994 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1994.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1994.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1996 -> (match (()) with
| () -> begin
(let _148_1028 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _148_1028))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _148_1033 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _148_1033)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _148_1039 = (let _148_1038 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _148_1038 [] c))
in (FStar_Syntax_Print.comp_to_string _148_1039)))


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
(let _148_1050 = (let _148_1049 = (let _148_1048 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_148_1048)))
in FStar_Syntax_Syntax.Tm_refine (_148_1049))
in (mk _148_1050 t0.FStar_Syntax_Syntax.pos))
end
| _53_2019 -> begin
t
end))
end
| _53_2021 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let _53_2026 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_2026) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_2029 -> begin
(

let _53_2032 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_2032) with
| (binders, args) -> begin
(let _148_1059 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _148_1058 = (let _148_1057 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _148_1055 -> FStar_Util.Inl (_148_1055)))
in (FStar_All.pipe_right _148_1057 (fun _148_1056 -> Some (_148_1056))))
in (FStar_Syntax_Util.abs binders _148_1059 _148_1058)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match ((let _148_1064 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_148_1064), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_2038) -> begin
(let _148_1065 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _148_1065))
end
| (_53_2041, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| _53_2046 -> begin
(

let _53_2049 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_2049) with
| (head, args) -> begin
(match ((let _148_1066 = (FStar_Syntax_Subst.compress head)
in _148_1066.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_2051, thead) -> begin
(

let _53_2057 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_2057) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_2065 = (env.FStar_TypeChecker_Env.type_of (

let _53_2058 = env
in {FStar_TypeChecker_Env.solver = _53_2058.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_2058.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_2058.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_2058.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_2058.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_2058.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_2058.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_2058.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_2058.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_2058.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_2058.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_2058.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_2058.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_2058.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_2058.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_2058.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_2058.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_2058.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_2058.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_2058.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_2058.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_2065) with
| (_53_2061, ty, _53_2064) -> begin
(eta_expand_with_type t ty)
end))
end
end))
end
| _53_2067 -> begin
(

let _53_2075 = (env.FStar_TypeChecker_Env.type_of (

let _53_2068 = env
in {FStar_TypeChecker_Env.solver = _53_2068.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_2068.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_2068.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_2068.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_2068.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_2068.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_2068.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_2068.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_2068.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_2068.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_2068.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_2068.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_2068.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_2068.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_2068.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_2068.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_2068.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_2068.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_2068.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_2068.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_2068.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_2075) with
| (_53_2071, ty, _53_2074) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end))





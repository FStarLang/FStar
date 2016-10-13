
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


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_69) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_216 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_216 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_76, _53_78) -> begin
(closure_to_string c)
end
| MemoLazy (_53_82) -> begin
"MemoLazy"
end
| Abs (_53_85, bs, _53_88, _53_90, _53_92) -> begin
(let _147_219 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_219))
end
| _53_96 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_222 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_222 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_103 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_110 -> begin
(let _147_238 = (let _147_237 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_237))
in (FStar_All.failwith _147_238))
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
| _53_126 -> begin
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

let _53_138 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_138) with
| (binders, cdef) -> begin
(

let _53_139 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _147_250 = (let _147_249 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_249)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_144 _53_148 -> (match (((_53_144), (_53_148))) with
| ((x, _53_143), (t, _53_147)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _147_250))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _147_251 = (

let _53_151 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_151.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_151.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_151.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_151.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _147_251 FStar_Syntax_Syntax.mk_Comp))
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

let _53_173 = (FStar_List.fold_left (fun _53_164 u -> (match (_53_164) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_168 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_168) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_173) with
| (_53_170, u, out) -> begin
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
| _53_190 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_183 -> begin
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

let us = (let _147_268 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_268 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_217 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_217) with
| (_53_215, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_219 -> begin
us
end))
end
| _53_221 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_271 = (aux u)
in (FStar_List.map (fun _147_270 -> FStar_Syntax_Syntax.U_succ (_147_270)) _147_271))
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

let _53_240 = (log cfg (fun _53_239 -> (match (()) with
| () -> begin
(let _147_295 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_294 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _147_295 _147_294)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_244 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_247) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_260) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_300 = (let _147_299 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_299))
in (mk _147_300 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_301 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_301))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_271) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_278) -> begin
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

let _53_294 = (closures_as_binders_delayed cfg env bs)
in (match (_53_294) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _147_304 = (let _147_303 = (let _147_302 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_147_302)))
in FStar_Syntax_Syntax.Tm_abs (_147_303))
in (mk _147_304 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_302 = (closures_as_binders_delayed cfg env bs)
in (match (_53_302) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_310 = (let _147_306 = (let _147_305 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_305)::[])
in (closures_as_binders_delayed cfg env _147_306))
in (match (_53_310) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _147_310 = (let _147_309 = (let _147_308 = (let _147_307 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_307 Prims.fst))
in ((_147_308), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_147_309))
in (mk _147_310 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _147_316 = (let _147_315 = (let _147_314 = (closure_as_term_delayed cfg env t1)
in (let _147_313 = (let _147_312 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _147_311 -> FStar_Util.Inl (_147_311)) _147_312))
in ((_147_314), (_147_313), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_315))
in (mk _147_316 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _147_322 = (let _147_321 = (let _147_320 = (closure_as_term_delayed cfg env t1)
in (let _147_319 = (let _147_318 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _147_317 -> FStar_Util.Inr (_147_317)) _147_318))
in ((_147_320), (_147_319), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_321))
in (mk _147_322 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _147_327 = (let _147_326 = (let _147_325 = (closure_as_term_delayed cfg env t')
in (let _147_324 = (let _147_323 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_147_323))
in ((_147_325), (_147_324))))
in FStar_Syntax_Syntax.Tm_meta (_147_326))
in (mk _147_327 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _147_333 = (let _147_332 = (let _147_331 = (closure_as_term_delayed cfg env t')
in (let _147_330 = (let _147_329 = (let _147_328 = (closure_as_term_delayed cfg env tbody)
in ((m), (_147_328)))
in FStar_Syntax_Syntax.Meta_monadic (_147_329))
in ((_147_331), (_147_330))))
in FStar_Syntax_Syntax.Tm_meta (_147_332))
in (mk _147_333 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_336 = (let _147_335 = (let _147_334 = (closure_as_term_delayed cfg env t')
in ((_147_334), (m)))
in FStar_Syntax_Syntax.Tm_meta (_147_335))
in (mk _147_336 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_349 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_355) -> begin
body
end
| FStar_Util.Inl (_53_358) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_361 = lb
in {FStar_Syntax_Syntax.lbname = _53_361.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_361.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_361.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_365, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_374 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_378 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_382 = lb
in (let _147_348 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_347 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_382.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_382.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_348; FStar_Syntax_Syntax.lbeff = _53_382.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_347}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_385 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_400 -> (match (_53_400) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_405) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_415 = (norm_pat env hd)
in (match (_53_415) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_360 = (norm_pat env p)
in (Prims.fst _147_360)))))
in (((

let _53_418 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_418.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_418.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_435 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_426 _53_429 -> (match (((_53_426), (_53_429))) with
| ((pats, env), (p, b)) -> begin
(

let _53_432 = (norm_pat env p)
in (match (_53_432) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_435) with
| (pats, env) -> begin
(((

let _53_436 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_436.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_436.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_440 = x
in (let _147_363 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_440.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_440.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_363}))
in (((

let _53_443 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_443.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_443.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_447 = x
in (let _147_364 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_447.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_447.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_364}))
in (((

let _53_450 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_450.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_450.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_456 = x
in (let _147_365 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_365}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_460 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_460.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_460.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_464 = (norm_pat env pat)
in (match (_53_464) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_366 = (closure_as_term cfg env w)
in Some (_147_366))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _147_369 = (let _147_368 = (let _147_367 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_147_367)))
in FStar_Syntax_Syntax.Tm_match (_147_368))
in (mk _147_369 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_475 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_481 -> begin
(FStar_List.map (fun _53_484 -> (match (_53_484) with
| (x, imp) -> begin
(let _147_377 = (closure_as_term_delayed cfg env x)
in ((_147_377), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_500 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_490 _53_493 -> (match (((_53_490), (_53_493))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_494 = b
in (let _147_383 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_494.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_494.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_383}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_500) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_506 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _147_388 = (closure_as_term_delayed cfg env t)
in (let _147_387 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _147_388 _147_387)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _147_390 = (closure_as_term_delayed cfg env t)
in (let _147_389 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _147_390 _147_389)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_392 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_392))
end
| f -> begin
f
end))))
in (let _147_394 = (

let _53_524 = c
in (let _147_393 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _147_393; FStar_Syntax_Syntax.effect_name = _53_524.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _147_394)))))
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
| _53_533 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _147_407 = (let _147_406 = (FStar_Util.string_of_int i)
in ((_147_406), (None)))
in FStar_Const.Const_int (_147_407)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _147_603 = (let _147_602 = (FStar_List.map (fun m -> (let _147_601 = (let _147_570 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_147_570), ((fun x y -> (int_as_const (x + y))))))
in (let _147_600 = (let _147_599 = (let _147_581 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_147_581), ((fun x y -> (int_as_const (x - y))))))
in (let _147_598 = (let _147_597 = (let _147_592 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_147_592), ((fun x y -> (int_as_const (x * y))))))
in (_147_597)::[])
in (_147_599)::_147_598))
in (_147_601)::_147_600))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _147_602))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _147_603))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let arith_op = (fun fv -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_572 -> (match (_53_572) with
| (l, _53_571) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) arith_ops)
end
| _53_574 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_582))::((a2, _53_578))::[]) -> begin
(match ((arith_op fv)) with
| None -> begin
tm
end
| Some (_53_589, op) -> begin
(

let norm = (fun i j -> (

let c = (let _147_660 = (FStar_Util.int_of_string i)
in (let _147_659 = (FStar_Util.int_of_string j)
in (op _147_660 _147_659)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _147_664 = (let _147_661 = (FStar_Syntax_Subst.compress a1)
in _147_661.FStar_Syntax_Syntax.n)
in (let _147_663 = (let _147_662 = (FStar_Syntax_Subst.compress a2)
in _147_662.FStar_Syntax_Syntax.n)
in ((_147_664), (_147_663))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _53_600))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _53_608))::[])) -> begin
(match ((let _147_672 = (let _147_665 = (FStar_Syntax_Subst.compress head1)
in _147_665.FStar_Syntax_Syntax.n)
in (let _147_671 = (let _147_666 = (FStar_Syntax_Subst.compress head2)
in _147_666.FStar_Syntax_Syntax.n)
in (let _147_670 = (let _147_667 = (FStar_Syntax_Subst.compress arg1)
in _147_667.FStar_Syntax_Syntax.n)
in (let _147_669 = (let _147_668 = (FStar_Syntax_Subst.compress arg2)
in _147_668.FStar_Syntax_Syntax.n)
in ((_147_672), (_147_671), (_147_670), (_147_669))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _147_676 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _147_675 = (let _147_674 = (let _147_673 = (norm i j)
in ((_147_673), (None)))
in (_147_674)::[])
in (FStar_Syntax_Util.mk_app _147_676 _147_675)))
end
| _53_630 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _53_643 -> begin
tm
end))
end)
end
| _53_645 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_650 = t
in {FStar_Syntax_Syntax.n = _53_650.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_650.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_650.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_659 -> begin
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
| _53_737 -> begin
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
| _53_780 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_807))::((_53_798, (arg, _53_801)))::[] -> begin
arg
end
| _53_811 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_815))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_821))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_825 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _147_687 = (FStar_Syntax_Subst.compress t)
in _147_687.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_843)::[], body, _53_847) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_855 -> begin
tm
end)
end
| _53_857 -> begin
tm
end)
end
| _53_859 -> begin
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
| _53_861 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_868 = (log cfg (fun _53_867 -> (match (()) with
| () -> begin
(let _147_720 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_719 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_720 _147_719)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_871) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_913; FStar_Syntax_Syntax.pos = _53_911; FStar_Syntax_Syntax.vars = _53_909}, ((tm, _53_919))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_925 = cfg
in {steps = s; tcenv = _53_925.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_934; FStar_Syntax_Syntax.pos = _53_932; FStar_Syntax_Syntax.vars = _53_930}, (a1)::(a2)::rest) -> begin
(

let _53_948 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_948) with
| (hd, _53_947) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_956; FStar_Syntax_Syntax.pos = _53_954; FStar_Syntax_Syntax.vars = _53_952}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_967 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_967) with
| (reify_head, _53_966) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _147_724 = (FStar_Syntax_Subst.compress e)
in _147_724.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_987 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_987) with
| (_53_985, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _147_729 = (let _147_728 = (let _147_727 = (let _147_725 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_725)::[])
in (let _147_726 = (FStar_Syntax_Util.mk_reify body)
in ((_147_727), (_147_726), (None))))
in FStar_Syntax_Syntax.Tm_abs (_147_728))
in (FStar_Syntax_Syntax.mk _147_729 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _147_743 = (let _147_742 = (let _147_741 = (let _147_740 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_739 = (let _147_738 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _147_737 = (let _147_736 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_735 = (let _147_734 = (FStar_Syntax_Syntax.as_arg head)
in (let _147_733 = (let _147_732 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_731 = (let _147_730 = (FStar_Syntax_Syntax.as_arg body)
in (_147_730)::[])
in (_147_732)::_147_731))
in (_147_734)::_147_733))
in (_147_736)::_147_735))
in (_147_738)::_147_737))
in (_147_740)::_147_739))
in ((bind_repr), (_147_741)))
in FStar_Syntax_Syntax.Tm_app (_147_742))
in (FStar_Syntax_Syntax.mk _147_743 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_994) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_997) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_1000 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_1009)); FStar_Syntax_Syntax.tk = _53_1007; FStar_Syntax_Syntax.pos = _53_1005; FStar_Syntax_Syntax.vars = _53_1003}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_1025 -> (match (_53_1025) with
| (pat, wopt, tm) -> begin
(let _147_745 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_147_745)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_1029 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _147_746 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_746)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _147_748 = (let _147_747 = (FStar_List.map (norm_universe cfg env) us)
in ((_147_747), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_147_748))
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

let _53_1056 = (log cfg (fun _53_1055 -> (match (()) with
| () -> begin
(let _147_752 = (FStar_Syntax_Print.term_to_string t0)
in (let _147_751 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _147_752 _147_751)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1062))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1070 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1072 -> begin
(let _147_756 = (let _147_755 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_755))
in (FStar_All.failwith _147_756))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1076) -> begin
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

let _53_1090 = (log cfg (fun _53_1089 -> (match (()) with
| () -> begin
(let _147_759 = (FStar_Syntax_Print.term_to_string t)
in (let _147_758 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_759 _147_758)))
end)))
in (match ((let _147_760 = (FStar_Syntax_Subst.compress t')
in _147_760.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1093) -> begin
(norm cfg env stack t')
end
| _53_1096 -> begin
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
| (UnivArgs (_53_1106))::_53_1104 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1112))::_53_1110 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1118, _53_1120))::stack_rest -> begin
(match (c) with
| Univ (_53_1125) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1128 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1131)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1135 = (log cfg (fun _53_1134 -> (match (()) with
| () -> begin
(let _147_762 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_762))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1141 = (log cfg (fun _53_1140 -> (match (()) with
| () -> begin
(let _147_764 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_764))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1147 = (log cfg (fun _53_1146 -> (match (()) with
| () -> begin
(let _147_766 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_766))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1150 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1152 -> begin
(

let cfg = (

let _53_1153 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1153.tcenv; delta_level = _53_1153.delta_level})
in (let _147_767 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_767)))
end)
end
| (_53_1158)::tl -> begin
(

let _53_1161 = (log cfg (fun _53_1160 -> (match (()) with
| () -> begin
(let _147_769 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_769))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1170 = cfg
in {steps = s; tcenv = _53_1170.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1176 = (set_memo r ((env), (t)))
in (

let _53_1179 = (log cfg (fun _53_1178 -> (match (()) with
| () -> begin
(let _147_771 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_771))
end)))
in (norm cfg env stack t)))
end
| ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_772 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_772))
end else begin
(

let _53_1209 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1209) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _147_778 = (let _147_776 = (let _147_774 = (let _147_773 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _147_773))
in (FStar_All.pipe_right _147_774 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_776 (fun _147_775 -> FStar_Util.Inl (_147_775))))
in (FStar_All.pipe_right _147_778 (fun _147_777 -> Some (_147_777))))
end
| _53_1214 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1217 -> (Dummy)::env) env))
in (

let _53_1221 = (log cfg (fun _53_1220 -> (match (()) with
| () -> begin
(let _147_782 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_782))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1229 stack -> (match (_53_1229) with
| (a, aq) -> begin
(let _147_789 = (let _147_788 = (let _147_787 = (let _147_786 = (let _147_785 = (FStar_Util.mk_ref None)
in ((env), (a), (_147_785), (false)))
in Clos (_147_786))
in ((_147_787), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_147_788))
in (_147_789)::stack)
end)) args))
in (

let _53_1233 = (log cfg (fun _53_1232 -> (match (()) with
| () -> begin
(let _147_791 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_791))
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

let _53_1243 = x
in {FStar_Syntax_Syntax.ppname = _53_1243.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1243.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1247 -> begin
(let _147_792 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_792))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1251 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1251) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _147_795 = (let _147_794 = (let _147_793 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1253 = x
in {FStar_Syntax_Syntax.ppname = _53_1253.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1253.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_147_793)))
in FStar_Syntax_Syntax.Tm_refine (_147_794))
in (mk _147_795 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_796 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_796))
end else begin
(

let _53_1262 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1262) with
| (bs, c) -> begin
(

let c = (let _147_799 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1264 -> (Dummy)::env) env))
in (norm_comp cfg _147_799 c))
in (

let t = (let _147_800 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_800 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1292 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1295 = (log cfg (fun _53_1294 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _147_802 = (norm cfg env [] t)
in FStar_Util.Inl (_147_802))
end
| FStar_Util.Inr (c) -> begin
(let _147_803 = (norm_comp cfg env c)
in FStar_Util.Inr (_147_803))
end)
in (let _147_804 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_804)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1308, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1320); FStar_Syntax_Syntax.lbunivs = _53_1318; FStar_Syntax_Syntax.lbtyp = _53_1316; FStar_Syntax_Syntax.lbeff = _53_1314; FStar_Syntax_Syntax.lbdef = _53_1312})::_53_1310), _53_1326) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _147_807 = (let _147_806 = (let _147_805 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_147_805), (false)))
in Clos (_147_806))
in (_147_807)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1340 = (let _147_810 = (let _147_809 = (let _147_808 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _147_808 FStar_Syntax_Syntax.mk_binder))
in (_147_809)::[])
in (FStar_Syntax_Subst.open_term _147_810 body))
in (match (_53_1340) with
| (bs, body) -> begin
(

let lb = (

let _53_1341 = lb
in (let _147_816 = (let _147_813 = (let _147_811 = (FStar_List.hd bs)
in (FStar_All.pipe_right _147_811 Prims.fst))
in (FStar_All.pipe_right _147_813 (fun _147_812 -> FStar_Util.Inl (_147_812))))
in (let _147_815 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_814 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _147_816; FStar_Syntax_Syntax.lbunivs = _53_1341.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_815; FStar_Syntax_Syntax.lbeff = _53_1341.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_814}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1345 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _147_819 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_819))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1371 = (FStar_List.fold_right (fun lb _53_1360 -> (match (_53_1360) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _147_822 = (

let _53_1361 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1361.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1361.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_822))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1371) with
| (rec_env, memos, _53_1370) -> begin
(

let _53_1374 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _147_829 = (let _147_828 = (let _147_827 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_147_827), (false)))
in Clos (_147_828))
in (_147_829)::env)) (Prims.snd lbs) env)
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

let _53_1389 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _53_1389.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m') -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1397 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _53_1397.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _53_1401 -> begin
(match (stack) with
| (_53_1405)::_53_1403 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1410) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1417 -> begin
(norm cfg env stack head)
end)
end
| _53_1419 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_830 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_830))
end
| _53_1424 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1432 -> (match (_53_1432) with
| (a, imp) -> begin
(let _147_835 = (norm cfg env [] a)
in ((_147_835), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1441 = comp
in (let _147_842 = (let _147_841 = (let _147_840 = (norm cfg env [] t)
in (let _147_839 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_840), (_147_839))))
in FStar_Syntax_Syntax.Total (_147_841))
in {FStar_Syntax_Syntax.n = _147_842; FStar_Syntax_Syntax.tk = _53_1441.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1441.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1441.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1447 = comp
in (let _147_846 = (let _147_845 = (let _147_844 = (norm cfg env [] t)
in (let _147_843 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_844), (_147_843))))
in FStar_Syntax_Syntax.GTotal (_147_845))
in {FStar_Syntax_Syntax.n = _147_846; FStar_Syntax_Syntax.tk = _53_1447.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1447.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1447.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1455 -> (match (_53_1455) with
| (a, i) -> begin
(let _147_850 = (norm cfg env [] a)
in ((_147_850), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_6 -> (match (_53_6) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_852 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_147_852))
end
| f -> begin
f
end))))
in (

let _53_1461 = comp
in (let _147_857 = (let _147_856 = (

let _53_1463 = ct
in (let _147_855 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _147_854 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_853 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _147_855; FStar_Syntax_Syntax.effect_name = _53_1463.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_854; FStar_Syntax_Syntax.effect_args = _147_853; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_147_856))
in {FStar_Syntax_Syntax.n = _147_857; FStar_Syntax_Syntax.tk = _53_1461.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1461.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1461.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1470 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1470.tcenv; delta_level = _53_1470.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _147_865 = (norm t)
in (FStar_Syntax_Util.non_informative _147_865)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1475) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1481 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1481.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1481.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1481.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1488 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1488.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1488.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1488.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1488.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1492 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1492.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1492.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1492.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1492.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1495 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1495.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1495.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1495.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1498 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1503 -> (match (_53_1503) with
| (x, imp) -> begin
(let _147_870 = (

let _53_1504 = x
in (let _147_869 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1504.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1504.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_869}))
in ((_147_870), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1517 = (FStar_List.fold_left (fun _53_1511 b -> (match (_53_1511) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1517) with
| (nbs, _53_1516) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _147_881 = (let _147_880 = (let _147_879 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _147_879))
in FStar_Util.Inl (_147_880))
in Some (_147_881))
end else begin
(let _147_884 = (let _147_883 = (let _147_882 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _147_882))
in FStar_Util.Inl (_147_883))
in Some (_147_884))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1526 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1538 = cfg
in {steps = s; tcenv = _53_1538.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1551 = (set_memo r ((env), (t)))
in (

let _53_1554 = (log cfg (fun _53_1553 -> (match (()) with
| () -> begin
(let _147_890 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_890))
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
in (let _147_891 = (

let _53_1577 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1577.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1577.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1577.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_891))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1613), aq, r))::stack -> begin
(

let _53_1622 = (log cfg (fun _53_1621 -> (match (()) with
| () -> begin
(let _147_893 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_893))
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
| Some (_53_1632, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _147_894 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_894)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1653 = (log cfg (fun _53_1652 -> (match (()) with
| () -> begin
(let _147_896 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _147_896))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _53_1657 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun _53_7 -> (match (_53_7) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _53_1663 -> begin
false
end))))
in (

let _53_1665 = cfg
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1665.tcenv; delta_level = new_delta}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1675) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1685 = (norm_pat env hd)
in (match (_53_1685) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_909 = (norm_pat env p)
in (Prims.fst _147_909)))))
in (((

let _53_1688 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1688.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1688.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1705 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1696 _53_1699 -> (match (((_53_1696), (_53_1699))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1702 = (norm_pat env p)
in (match (_53_1702) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1705) with
| (pats, env) -> begin
(((

let _53_1706 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1706.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1706.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1710 = x
in (let _147_912 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1710.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1710.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_912}))
in (((

let _53_1713 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1713.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1713.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1717 = x
in (let _147_913 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1717.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1717.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_913}))
in (((

let _53_1720 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1720.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1720.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1726 = x
in (let _147_914 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1726.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1726.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_914}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1730 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1730.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1730.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1734 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1739 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1739) with
| (p, wopt, e) -> begin
(

let _53_1742 = (norm_pat env p)
in (match (_53_1742) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_916 = (norm_or_whnf env w)
in Some (_147_916))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _147_917 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _147_917)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1753) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1778 -> begin
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

let _53_1795 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_53_1795) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_53_1801) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1818) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1825 -> begin
(let _147_934 = (not ((is_cons head)))
in FStar_Util.Inr (_147_934))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _147_935 = (FStar_Syntax_Util.un_uinst head)
in _147_935.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1833 -> begin
(let _147_936 = (not ((is_cons head)))
in FStar_Util.Inr (_147_936))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1843))::rest_a, ((p, _53_1849))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1857 -> begin
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

let _53_1875 = (log cfg (fun _53_1874 -> (match (()) with
| () -> begin
(let _147_947 = (FStar_Syntax_Print.pat_to_string p)
in (let _147_946 = (let _147_945 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _147_945 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _147_947 _147_946)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _147_952 = (let _147_951 = (let _147_950 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_147_950), (false)))
in Clos (_147_951))
in (_147_952)::env)) env s)
in (let _147_953 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_953))))
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
| _53_1888 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _53_1892 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_965 = (config s e)
in (norm _147_965 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_972 = (config s e)
in (norm_comp _147_972 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_977 = (config [] env)
in (norm_universe _147_977 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_982 = (config [] env)
in (ghost_to_pure_aux _147_982 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _147_989 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _147_989)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1911 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1911.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1911.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1913 -> (match (()) with
| () -> begin
(let _147_991 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _147_991))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_996 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_996)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_1002 = (let _147_1001 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_1001 [] c))
in (FStar_Syntax_Print.comp_to_string _147_1002)))


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
(let _147_1013 = (let _147_1012 = (let _147_1011 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_147_1011)))
in FStar_Syntax_Syntax.Tm_refine (_147_1012))
in (mk _147_1013 t0.FStar_Syntax_Syntax.pos))
end
| _53_1936 -> begin
t
end))
end
| _53_1938 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1945 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1945) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1948 -> begin
(

let _53_1951 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1951) with
| (binders, args) -> begin
(let _147_1024 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_1023 = (let _147_1022 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1020 -> FStar_Util.Inl (_147_1020)))
in (FStar_All.pipe_right _147_1022 (fun _147_1021 -> Some (_147_1021))))
in (FStar_Syntax_Util.abs binders _147_1024 _147_1023)))
end))
end)
end)))
in (match ((let _147_1025 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_147_1025), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1955) -> begin
(let _147_1026 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _147_1026))
end
| (_53_1958, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1963 -> begin
(

let _53_1966 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1966) with
| (head, args) -> begin
(match ((let _147_1027 = (FStar_Syntax_Subst.compress head)
in _147_1027.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1968, thead) -> begin
(

let _53_1974 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1974) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1982 = (env.FStar_TypeChecker_Env.type_of (

let _53_1975 = env
in {FStar_TypeChecker_Env.solver = _53_1975.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1975.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1975.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1975.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1975.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1975.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1975.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1975.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1975.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1975.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1975.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1975.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1975.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1975.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1975.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1975.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1975.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1975.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1975.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1975.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1975.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1982) with
| (_53_1978, ty, _53_1981) -> begin
(expand ty)
end))
end
end))
end
| _53_1984 -> begin
(

let _53_1992 = (env.FStar_TypeChecker_Env.type_of (

let _53_1985 = env
in {FStar_TypeChecker_Env.solver = _53_1985.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1985.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1985.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1985.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1985.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1985.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1985.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1985.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1985.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1985.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1985.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1985.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1985.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1985.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1985.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1985.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1985.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1985.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1985.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1985.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1985.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1992) with
| (_53_1988, ty, _53_1991) -> begin
(expand ty)
end))
end)
end))
end)))





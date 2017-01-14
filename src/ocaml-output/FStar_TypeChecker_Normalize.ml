
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
| Exclude (_56_3) -> begin
_56_3
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_56_6) -> begin
_56_6
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
| Clos (_56_9) -> begin
_56_9
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_56_12) -> begin
_56_12
end))


let closure_to_string : closure  ->  Prims.string = (fun uu___257 -> (match (uu___257) with
| Clos (_56_15, t, _56_18, _56_20) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (_56_24) -> begin
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
| Arg (_56_33) -> begin
_56_33
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_56_36) -> begin
_56_36
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_56_39) -> begin
_56_39
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_56_42) -> begin
_56_42
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_56_45) -> begin
_56_45
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_56_48) -> begin
_56_48
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_56_51) -> begin
_56_51
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_56_54) -> begin
_56_54
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_56_57) -> begin
_56_57
end))


let ___Debug____0 = (fun projectee -> (match (projectee) with
| Debug (_56_60) -> begin
_56_60
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_56_66) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _157_231 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _157_231 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___258 -> (match (uu___258) with
| Arg (c, _56_73, _56_75) -> begin
(let _157_234 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" _157_234))
end
| MemoLazy (_56_79) -> begin
"MemoLazy"
end
| Abs (_56_82, bs, _56_85, _56_87, _56_89) -> begin
(let _157_235 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _157_235))
end
| UnivArgs (_56_93) -> begin
"UnivArgs"
end
| Match (_56_96) -> begin
"Match"
end
| App (t, _56_100, _56_102) -> begin
(let _157_236 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" _157_236))
end
| Meta (m, _56_107) -> begin
"Meta"
end
| Let (_56_111) -> begin
"Let"
end
| Steps (s, _56_115) -> begin
"Steps"
end
| Debug (t) -> begin
(let _157_237 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" _157_237))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _157_240 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _157_240 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun uu___259 -> (match (uu___259) with
| [] -> begin
true
end
| _56_126 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _56_131 -> begin
(let _157_256 = (let _157_255 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _157_255))
in (failwith _157_256))
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
| _56_147 -> begin
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

let _56_159 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_56_159) with
| (binders, cdef) -> begin
(

let _56_160 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(let _157_271 = (let _157_270 = (let _157_269 = (let _157_268 = (FStar_Util.string_of_int (FStar_List.length binders))
in (let _157_267 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (let _157_266 = (let _157_265 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string _157_265))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" _157_268 _157_267 _157_266))))
in ((_157_269), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (_157_270))
in (Prims.raise _157_271))
end else begin
()
end
in (

let inst = (let _157_275 = (let _157_274 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_157_274)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _56_165 _56_169 -> (match (((_56_165), (_56_169))) with
| ((x, _56_164), (t, _56_168)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _157_275))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _157_276 = (

let _56_172 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _56_172.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _56_172.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _56_172.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _56_172.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _157_276 FStar_Syntax_Syntax.mk_Comp))
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

let _56_194 = (FStar_List.fold_left (fun _56_185 u -> (match (_56_185) with
| (cur_kernel, cur_max, out) -> begin
(

let _56_189 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_189) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_56_194) with
| (_56_191, u, out) -> begin
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
| _56_209 -> begin
(failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _56_202 -> begin
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

let us = (let _157_293 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _157_293 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _56_236 = (FStar_Syntax_Util.univ_kernel u)
in (match (_56_236) with
| (_56_234, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _56_238 -> begin
us
end))
end
| _56_240 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _157_296 = (aux u)
in (FStar_List.map (fun _157_295 -> FStar_Syntax_Syntax.U_succ (_157_295)) _157_296))
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

let _56_259 = (log cfg (fun _56_258 -> (match (()) with
| () -> begin
(let _157_321 = (FStar_Syntax_Print.tag_of_term t)
in (let _157_320 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _157_321 _157_320)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _56_263 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_56_266) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_56_279) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _157_326 = (let _157_325 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_157_325))
in (mk _157_326 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _157_327 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _157_327))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_56_290) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _56_297) -> begin
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

let _56_313 = (closures_as_binders_delayed cfg env bs)
in (match (_56_313) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _157_330 = (let _157_329 = (let _157_328 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_157_328)))
in FStar_Syntax_Syntax.Tm_abs (_157_329))
in (mk _157_330 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _56_321 = (closures_as_binders_delayed cfg env bs)
in (match (_56_321) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _56_329 = (let _157_332 = (let _157_331 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_331)::[])
in (closures_as_binders_delayed cfg env _157_332))
in (match (_56_329) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _157_336 = (let _157_335 = (let _157_334 = (let _157_333 = (FStar_List.hd x)
in (FStar_All.pipe_right _157_333 Prims.fst))
in ((_157_334), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_157_335))
in (mk _157_336 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _157_342 = (let _157_341 = (let _157_340 = (closure_as_term_delayed cfg env t1)
in (let _157_339 = (let _157_338 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _157_337 -> FStar_Util.Inl (_157_337)) _157_338))
in ((_157_340), (_157_339), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_157_341))
in (mk _157_342 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _157_348 = (let _157_347 = (let _157_346 = (closure_as_term_delayed cfg env t1)
in (let _157_345 = (let _157_344 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _157_343 -> FStar_Util.Inr (_157_343)) _157_344))
in ((_157_346), (_157_345), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_157_347))
in (mk _157_348 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _157_353 = (let _157_352 = (let _157_351 = (closure_as_term_delayed cfg env t')
in (let _157_350 = (let _157_349 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_157_349))
in ((_157_351), (_157_350))))
in FStar_Syntax_Syntax.Tm_meta (_157_352))
in (mk _157_353 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _157_359 = (let _157_358 = (let _157_357 = (closure_as_term_delayed cfg env t')
in (let _157_356 = (let _157_355 = (let _157_354 = (closure_as_term_delayed cfg env tbody)
in ((m), (_157_354)))
in FStar_Syntax_Syntax.Meta_monadic (_157_355))
in ((_157_357), (_157_356))))
in FStar_Syntax_Syntax.Tm_meta (_157_358))
in (mk _157_359 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(let _157_365 = (let _157_364 = (let _157_363 = (closure_as_term_delayed cfg env t')
in (let _157_362 = (let _157_361 = (let _157_360 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (_157_360)))
in FStar_Syntax_Syntax.Meta_monadic_lift (_157_361))
in ((_157_363), (_157_362))))
in FStar_Syntax_Syntax.Tm_meta (_157_364))
in (mk _157_365 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _157_368 = (let _157_367 = (let _157_366 = (closure_as_term_delayed cfg env t')
in ((_157_366), (m)))
in FStar_Syntax_Syntax.Tm_meta (_157_367))
in (mk _157_368 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _56_376 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_56_382) -> begin
body
end
| FStar_Util.Inl (_56_385) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _56_388 = lb
in {FStar_Syntax_Syntax.lbname = _56_388.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _56_388.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _56_388.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_56_392, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _56_401 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _56_405 env -> (Dummy)::env) lbs env_univs)
end
in (

let _56_409 = lb
in (let _157_380 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _157_379 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _56_409.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _56_409.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _157_380; FStar_Syntax_Syntax.lbeff = _56_409.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _157_379}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _56_412 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _56_427 -> (match (_56_427) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_56_432) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _56_442 = (norm_pat env hd)
in (match (_56_442) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _157_392 = (norm_pat env p)
in (Prims.fst _157_392)))))
in (((

let _56_445 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _56_445.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_445.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_462 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_453 _56_456 -> (match (((_56_453), (_56_456))) with
| ((pats, env), (p, b)) -> begin
(

let _56_459 = (norm_pat env p)
in (match (_56_459) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_56_462) with
| (pats, env) -> begin
(((

let _56_463 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _56_463.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_463.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _56_467 = x
in (let _157_395 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_467.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_467.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_395}))
in (((

let _56_470 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _56_470.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_470.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _56_474 = x
in (let _157_396 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_474.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_474.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_396}))
in (((

let _56_477 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _56_477.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_477.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _56_483 = x
in (let _157_397 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_483.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_483.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_397}))
in (

let t = (closure_as_term cfg env t)
in (((

let _56_487 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _56_487.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_487.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _56_491 = (norm_pat env pat)
in (match (_56_491) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _157_398 = (closure_as_term cfg env w)
in Some (_157_398))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _157_401 = (let _157_400 = (let _157_399 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_157_399)))
in FStar_Syntax_Syntax.Tm_match (_157_400))
in (mk _157_401 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _56_502 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _56_508 -> begin
(FStar_List.map (fun _56_511 -> (match (_56_511) with
| (x, imp) -> begin
(let _157_409 = (closure_as_term_delayed cfg env x)
in ((_157_409), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _56_527 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _56_517 _56_520 -> (match (((_56_517), (_56_520))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _56_521 = b
in (let _157_415 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_521.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_521.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_415}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_56_527) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _56_533 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _157_420 = (closure_as_term_delayed cfg env t)
in (let _157_419 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _157_420 _157_419)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _157_422 = (closure_as_term_delayed cfg env t)
in (let _157_421 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _157_422 _157_421)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___260 -> (match (uu___260) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _157_424 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_157_424))
end
| f -> begin
f
end))))
in (let _157_426 = (

let _56_551 = c
in (let _157_425 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _157_425; FStar_Syntax_Syntax.effect_name = _56_551.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _157_426)))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun uu___261 -> (match (uu___261) with
| FStar_Syntax_Syntax.DECREASES (_56_556) -> begin
false
end
| _56_559 -> begin
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
| _56_568 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _157_441 = (let _157_440 = (FStar_Util.string_of_int i)
in ((_157_440), (None)))
in FStar_Const.Const_int (_157_441)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _157_637 = (let _157_636 = (FStar_List.map (fun m -> (let _157_635 = (let _157_604 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_157_604), ((fun x y -> (int_as_const (x + y))))))
in (let _157_634 = (let _157_633 = (let _157_615 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_157_615), ((fun x y -> (int_as_const (x - y))))))
in (let _157_632 = (let _157_631 = (let _157_626 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_157_626), ((fun x y -> (int_as_const (x * y))))))
in (_157_631)::[])
in (_157_633)::_157_632))
in (_157_635)::_157_634))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _157_636))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _157_637))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (let _157_647 = (let _157_646 = (let _157_645 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _157_645 FStar_Syntax_Syntax.Delta_constant None))
in FStar_Syntax_Syntax.Tm_fvar (_157_646))
in (mk _157_647)))
in (

let ctor = (fun x -> (let _157_652 = (let _157_651 = (let _157_650 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _157_650 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in FStar_Syntax_Syntax.Tm_fvar (_157_651))
in (mk _157_652)))
in (let _157_682 = (let _157_679 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_157_679), ((fun s -> (let _157_678 = (FStar_String.list_of_string s)
in (let _157_677 = (let _157_676 = (let _157_675 = (let _157_674 = (let _157_670 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_670 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _157_673 = (let _157_672 = (let _157_671 = (name (("FStar")::("Char")::("char")::[]))
in ((_157_671), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_157_672)::[])
in ((_157_674), (_157_673))))
in FStar_Syntax_Syntax.Tm_app (_157_675))
in (mk _157_676))
in (FStar_List.fold_right (fun c a -> (let _157_669 = (let _157_668 = (let _157_667 = (let _157_660 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_660 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _157_666 = (let _157_665 = (let _157_661 = (name (("FStar")::("Char")::("char")::[]))
in ((_157_661), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _157_664 = (let _157_663 = (let _157_662 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_157_662), (None)))
in (_157_663)::(((a), (None)))::[])
in (_157_665)::_157_664))
in ((_157_667), (_157_666))))
in FStar_Syntax_Syntax.Tm_app (_157_668))
in (mk _157_669))) _157_678 _157_677)))))))
in (_157_682)::[]))))


let reduce_equality : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun tm -> (

let is_decidable_equality = (fun t -> (match ((let _157_687 = (FStar_Syntax_Util.un_uinst t)
in _157_687.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq)
end
| _56_613 -> begin
false
end))
in (

let is_propositional_equality = (fun t -> (match ((let _157_690 = (FStar_Syntax_Util.un_uinst t)
in _157_690.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)
end
| _56_619 -> begin
false
end))
in (match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (op_eq_inst, ((_typ, _56_631))::((a1, _56_627))::((a2, _56_623))::[]) when (is_decidable_equality op_eq_inst) -> begin
(

let tt = (match ((FStar_Syntax_Util.eq_tm a1 a2)) with
| FStar_Syntax_Util.Equal -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) tm.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Util.NotEqual -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) tm.FStar_Syntax_Syntax.pos)
end
| _56_639 -> begin
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
| _56_667 -> begin
tm
end)
in tt)
end
| _56_670 -> begin
tm
end))))


let find_fv = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _56_679 -> (match (_56_679) with
| (l, _56_678) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| _56_681 -> begin
None
end))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _56_691))::((a2, _56_687))::[]) -> begin
(match ((find_fv fv arith_ops)) with
| None -> begin
tm
end
| Some (_56_698, op) -> begin
(

let norm = (fun i j -> (

let c = (let _157_707 = (FStar_Util.int_of_string i)
in (let _157_706 = (FStar_Util.int_of_string j)
in (op _157_707 _157_706)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _157_711 = (let _157_708 = (FStar_Syntax_Subst.compress a1)
in _157_708.FStar_Syntax_Syntax.n)
in (let _157_710 = (let _157_709 = (FStar_Syntax_Subst.compress a2)
in _157_709.FStar_Syntax_Syntax.n)
in ((_157_711), (_157_710))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _56_709))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _56_717))::[])) -> begin
(match ((let _157_719 = (let _157_712 = (FStar_Syntax_Subst.compress head1)
in _157_712.FStar_Syntax_Syntax.n)
in (let _157_718 = (let _157_713 = (FStar_Syntax_Subst.compress head2)
in _157_713.FStar_Syntax_Syntax.n)
in (let _157_717 = (let _157_714 = (FStar_Syntax_Subst.compress arg1)
in _157_714.FStar_Syntax_Syntax.n)
in (let _157_716 = (let _157_715 = (FStar_Syntax_Subst.compress arg2)
in _157_715.FStar_Syntax_Syntax.n)
in ((_157_719), (_157_718), (_157_717), (_157_716))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _157_723 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _157_722 = (let _157_721 = (let _157_720 = (norm i j)
in ((_157_720), (None)))
in (_157_721)::[])
in (FStar_Syntax_Util.mk_app _157_723 _157_722)))
end
| _56_739 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _56_752 -> begin
tm
end))
end)
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _56_756))::[]) -> begin
(match ((find_fv fv un_ops)) with
| None -> begin
tm
end
| Some (_56_763, op) -> begin
(match ((let _157_726 = (FStar_Syntax_Subst.compress a1)
in _157_726.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, _56_769)) -> begin
(let _157_727 = (FStar_Bytes.unicode_bytes_as_string b)
in (op _157_727))
end
| _56_774 -> begin
tm
end)
end)
end
| _56_776 -> begin
(reduce_equality tm)
end)
end)


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _56_781 = t
in {FStar_Syntax_Syntax.n = _56_781.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_781.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_781.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _56_790 -> begin
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
| _56_868 -> begin
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
| _56_911 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _56_938))::((_56_929, (arg, _56_932)))::[] -> begin
arg
end
| _56_942 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _56_946))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _56_952))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _56_956 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _157_738 = (FStar_Syntax_Subst.compress t)
in _157_738.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_56_974)::[], body, _56_978) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _56_986 -> begin
tm
end)
end
| _56_988 -> begin
tm
end)
end
| _56_990 -> begin
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
| _56_992 -> begin
tm
end)
end))))


let is_norm_request = (fun hd args -> (match ((let _157_742 = (let _157_741 = (FStar_Syntax_Util.un_uinst hd)
in _157_741.FStar_Syntax_Syntax.n)
in ((_157_742), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_56_1000)::(_56_998)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_56_1006)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| _56_1010 -> begin
false
end))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| _56_1024 -> begin
(failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _56_1031 = (log cfg (fun _56_1030 -> (match (()) with
| () -> begin
(let _157_782 = (FStar_Syntax_Print.tag_of_term t)
in (let _157_781 = (FStar_Syntax_Print.term_to_string t)
in (let _157_780 = (stack_to_string stack)
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" _157_782 _157_781 _157_780))))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_56_1034) -> begin
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

let _56_1077 = cfg
in {steps = s; tcenv = _56_1077.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _56_1086; FStar_Syntax_Syntax.pos = _56_1084; FStar_Syntax_Syntax.vars = _56_1082}, (a1)::(a2)::rest) -> begin
(

let _56_1100 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_1100) with
| (hd, _56_1099) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _56_1108; FStar_Syntax_Syntax.pos = _56_1106; FStar_Syntax_Syntax.vars = _56_1104}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _56_1119 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_1119) with
| (reify_head, _56_1118) -> begin
(

let a = (let _157_786 = (FStar_All.pipe_left FStar_Syntax_Util.unascribe (Prims.fst a))
in (FStar_Syntax_Subst.compress _157_786))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_56_1128)); FStar_Syntax_Syntax.tk = _56_1126; FStar_Syntax_Syntax.pos = _56_1124; FStar_Syntax_Syntax.vars = _56_1122}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| _56_1137 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _157_787 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _157_787)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _157_789 = (let _157_788 = (FStar_List.map (norm_universe cfg env) us)
in ((_157_788), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_157_789))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___262 -> (match (uu___262) with
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

let r_env = (let _157_791 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _157_791))
in (match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _56_1161 = (log cfg (fun _56_1160 -> (match (()) with
| () -> begin
(FStar_Util.print "Tm_fvar case 2\n" [])
end)))
in (rebuild cfg env stack t))
end
| Some (us, t) -> begin
(

let _56_1168 = (log cfg (fun _56_1167 -> (match (()) with
| () -> begin
(let _157_795 = (FStar_Syntax_Print.term_to_string t0)
in (let _157_794 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _157_795 _157_794)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _56_1174))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _56_1182 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _56_1184 -> begin
(let _157_799 = (let _157_798 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _157_798))
in (failwith _157_799))
end)
end else begin
(norm cfg env stack t)
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_56_1188) -> begin
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

let _56_1202 = (log cfg (fun _56_1201 -> (match (()) with
| () -> begin
(let _157_802 = (FStar_Syntax_Print.term_to_string t)
in (let _157_801 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _157_802 _157_801)))
end)))
in (match ((let _157_803 = (FStar_Syntax_Subst.compress t')
in _157_803.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_56_1205) -> begin
(norm cfg env stack t')
end
| _56_1208 -> begin
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
| (UnivArgs (_56_1218))::_56_1216 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_56_1224))::_56_1222 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _56_1230, _56_1232))::stack_rest -> begin
(match (c) with
| Univ (_56_1237) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _56_1240 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (_56_1243)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _56_1247 = (log cfg (fun _56_1246 -> (match (()) with
| () -> begin
(let _157_805 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _157_805))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun uu___263 -> (match (uu___263) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _56_1257 -> begin
false
end))))) -> begin
(

let _56_1259 = (log cfg (fun _56_1258 -> (match (()) with
| () -> begin
(let _157_808 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _157_808))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _56_1265 = (log cfg (fun _56_1264 -> (match (()) with
| () -> begin
(let _157_810 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _157_810))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _56_1268 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _56_1270 -> begin
(

let cfg = (

let _56_1271 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _56_1271.tcenv; delta_level = _56_1271.delta_level})
in (let _157_811 = (closure_as_term cfg env t)
in (rebuild cfg env stack _157_811)))
end)
end
| (_56_1276)::tl -> begin
(

let _56_1279 = (log cfg (fun _56_1278 -> (match (()) with
| () -> begin
(let _157_813 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _157_813))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _56_1288 = cfg
in {steps = s; tcenv = _56_1288.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _56_1294 = (set_memo r ((env), (t)))
in (

let _56_1297 = (log cfg (fun _56_1296 -> (match (()) with
| () -> begin
(let _157_815 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _157_815))
end)))
in (norm cfg env stack t)))
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _157_816 = (closure_as_term cfg env t)
in (rebuild cfg env stack _157_816))
end else begin
(

let _56_1333 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_56_1333) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _157_822 = (let _157_820 = (let _157_818 = (let _157_817 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _157_817))
in (FStar_All.pipe_right _157_818 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _157_820 (fun _157_819 -> FStar_Util.Inl (_157_819))))
in (FStar_All.pipe_right _157_822 (fun _157_821 -> Some (_157_821))))
end
| _56_1338 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _56_1341 -> (Dummy)::env) env))
in (

let _56_1345 = (log cfg (fun _56_1344 -> (match (()) with
| () -> begin
(let _157_826 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _157_826))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _56_1353 stack -> (match (_56_1353) with
| (a, aq) -> begin
(let _157_833 = (let _157_832 = (let _157_831 = (let _157_830 = (let _157_829 = (FStar_Util.mk_ref None)
in ((env), (a), (_157_829), (false)))
in Clos (_157_830))
in ((_157_831), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_157_832))
in (_157_833)::stack)
end)) args))
in (

let _56_1357 = (log cfg (fun _56_1356 -> (match (()) with
| () -> begin
(let _157_835 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _157_835))
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

let _56_1367 = x
in {FStar_Syntax_Syntax.ppname = _56_1367.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1367.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _56_1371 -> begin
(let _157_836 = (closure_as_term cfg env t)
in (rebuild cfg env stack _157_836))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _56_1375 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_56_1375) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _157_839 = (let _157_838 = (let _157_837 = (FStar_Syntax_Subst.close closing f)
in (((

let _56_1377 = x
in {FStar_Syntax_Syntax.ppname = _56_1377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_157_837)))
in FStar_Syntax_Syntax.Tm_refine (_157_838))
in (mk _157_839 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _157_840 = (closure_as_term cfg env t)
in (rebuild cfg env stack _157_840))
end else begin
(

let _56_1386 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_56_1386) with
| (bs, c) -> begin
(

let c = (let _157_843 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _56_1388 -> (Dummy)::env) env))
in (norm_comp cfg _157_843 c))
in (

let t = (let _157_844 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _157_844 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _, _))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _56_1434 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _56_1437 = (log cfg (fun _56_1436 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _157_846 = (norm cfg env [] t)
in FStar_Util.Inl (_157_846))
end
| FStar_Util.Inr (c) -> begin
(let _157_847 = (norm_comp cfg env c)
in FStar_Util.Inr (_157_847))
end)
in (let _157_848 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _157_848)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_56_1450, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_56_1462); FStar_Syntax_Syntax.lbunivs = _56_1460; FStar_Syntax_Syntax.lbtyp = _56_1458; FStar_Syntax_Syntax.lbeff = _56_1456; FStar_Syntax_Syntax.lbdef = _56_1454})::_56_1452), _56_1468) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))))))) then begin
(

let env = (let _157_851 = (let _157_850 = (let _157_849 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_157_849), (false)))
in Clos (_157_850))
in (_157_851)::env)
in (norm cfg env stack body))
end else begin
(

let _56_1482 = (let _157_854 = (let _157_853 = (let _157_852 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _157_852 FStar_Syntax_Syntax.mk_binder))
in (_157_853)::[])
in (FStar_Syntax_Subst.open_term _157_854 body))
in (match (_56_1482) with
| (bs, body) -> begin
(

let lb = (

let _56_1483 = lb
in (let _157_860 = (let _157_857 = (let _157_855 = (FStar_List.hd bs)
in (FStar_All.pipe_right _157_855 Prims.fst))
in (FStar_All.pipe_right _157_857 (fun _157_856 -> FStar_Util.Inl (_157_856))))
in (let _157_859 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _157_858 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _157_860; FStar_Syntax_Syntax.lbunivs = _56_1483.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _157_859; FStar_Syntax_Syntax.lbeff = _56_1483.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _157_858}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _56_1487 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _157_863 = (closure_as_term cfg env t)
in (rebuild cfg env stack _157_863))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _56_1513 = (FStar_List.fold_right (fun lb _56_1502 -> (match (_56_1502) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _157_866 = (

let _56_1503 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _56_1503.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _56_1503.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _157_866))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_56_1513) with
| (rec_env, memos, _56_1512) -> begin
(

let _56_1516 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _157_873 = (let _157_872 = (let _157_871 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_157_871), (false)))
in Clos (_157_872))
in (_157_873)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _56_1536; FStar_Syntax_Syntax.pos = _56_1534; FStar_Syntax_Syntax.vars = _56_1532}, _56_1541, _56_1543))::_56_1530 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| _56_1548 -> begin
false
end)
in if (not (should_reify)) then begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _56_1552 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _56_1552.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end else begin
(match ((let _157_874 = (FStar_Syntax_Subst.compress head)
in _157_874.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _56_1566 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_56_1566) with
| (_56_1564, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body = (let _157_878 = (let _157_877 = (let _157_876 = (let _157_875 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_875)::[])
in ((_157_876), (body), (None)))
in FStar_Syntax_Syntax.Tm_abs (_157_877))
in (FStar_Syntax_Syntax.mk _157_878 None body.FStar_Syntax_Syntax.pos))
in (

let bind_inst = (match ((let _157_879 = (FStar_Syntax_Subst.compress bind_repr)
in _157_879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (_56_1576)::(_56_1574)::[]) -> begin
(let _157_885 = (let _157_884 = (let _157_883 = (let _157_882 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv lb.FStar_Syntax_Syntax.lbtyp)
in (let _157_881 = (let _157_880 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_157_880)::[])
in (_157_882)::_157_881))
in ((bind), (_157_883)))
in FStar_Syntax_Syntax.Tm_uinst (_157_884))
in (FStar_Syntax_Syntax.mk _157_885 None t.FStar_Syntax_Syntax.pos))
end
| _56_1581 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (

let reified = (let _157_899 = (let _157_898 = (let _157_897 = (let _157_896 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _157_895 = (let _157_894 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_893 = (let _157_892 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _157_891 = (let _157_890 = (FStar_Syntax_Syntax.as_arg head)
in (let _157_889 = (let _157_888 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _157_887 = (let _157_886 = (FStar_Syntax_Syntax.as_arg body)
in (_157_886)::[])
in (_157_888)::_157_887))
in (_157_890)::_157_889))
in (_157_892)::_157_891))
in (_157_894)::_157_893))
in (_157_896)::_157_895))
in ((bind_inst), (_157_897)))
in FStar_Syntax_Syntax.Tm_app (_157_898))
in (FStar_Syntax_Syntax.mk _157_899 None t.FStar_Syntax_Syntax.pos))
in (let _157_900 = (FStar_List.tl stack)
in (norm cfg env _157_900 reified)))))))
end
| FStar_Util.Inr (_56_1585) -> begin
(failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _56_1595 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_56_1595) with
| (_56_1593, bind_repr) -> begin
(

let maybe_unfold_action = (fun head -> (

let maybe_extract_fv = (fun t -> (

let t = (match ((let _157_905 = (FStar_Syntax_Subst.compress t)
in _157_905.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (t, _56_1602) -> begin
t
end
| _56_1606 -> begin
head
end)
in (match ((let _157_906 = (FStar_Syntax_Subst.compress t)
in _157_906.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
Some (x)
end
| _56_1611 -> begin
None
end)))
in (match ((maybe_extract_fv head)) with
| Some (x) when (let _157_907 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv _157_907)) -> begin
(

let head = (norm cfg env [] head)
in (

let action_unfolded = (match ((maybe_extract_fv head)) with
| Some (_56_1616) -> begin
Some (true)
end
| _56_1619 -> begin
Some (false)
end)
in ((head), (action_unfolded))))
end
| _56_1622 -> begin
((head), (None))
end)))
in (

let rec bind_on_lift = (fun args acc -> (match (args) with
| [] -> begin
(match ((FStar_List.rev acc)) with
| [] -> begin
(failwith "bind_on_lift should be always called with a non-empty list")
end
| ((head, _56_1631))::args -> begin
(

let _56_1636 = (maybe_unfold_action head)
in (match (_56_1636) with
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
(match ((let _157_914 = (FStar_Syntax_Subst.compress e)
in _157_914.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) when (not ((FStar_Syntax_Util.is_pure_effect m1))) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "monadic_app_var" None t')
in (

let body = (let _157_917 = (let _157_916 = (let _157_915 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_157_915), (q)))
in (_157_916)::acc)
in (bind_on_lift es _157_917))
in (

let lifted_e0 = (reify_lift cfg.tcenv e0 m1 m2 t')
in (

let continuation = (FStar_Syntax_Util.abs ((((x), (None)))::[]) body (Some (FStar_Util.Inr (((m2), ([]))))))
in (

let bind_inst = (match ((let _157_918 = (FStar_Syntax_Subst.compress bind_repr)
in _157_918.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (_56_1666)::(_56_1664)::[]) -> begin
(let _157_924 = (let _157_923 = (let _157_922 = (let _157_921 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t')
in (let _157_920 = (let _157_919 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_157_919)::[])
in (_157_921)::_157_920))
in ((bind), (_157_922)))
in FStar_Syntax_Syntax.Tm_uinst (_157_923))
in (FStar_Syntax_Syntax.mk _157_924 None e0.FStar_Syntax_Syntax.pos))
end
| _56_1671 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (let _157_938 = (let _157_937 = (let _157_936 = (let _157_935 = (FStar_Syntax_Syntax.as_arg t')
in (let _157_934 = (let _157_933 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_932 = (let _157_931 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _157_930 = (let _157_929 = (FStar_Syntax_Syntax.as_arg lifted_e0)
in (let _157_928 = (let _157_927 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _157_926 = (let _157_925 = (FStar_Syntax_Syntax.as_arg continuation)
in (_157_925)::[])
in (_157_927)::_157_926))
in (_157_929)::_157_928))
in (_157_931)::_157_930))
in (_157_933)::_157_932))
in (_157_935)::_157_934))
in ((bind_inst), (_157_936)))
in FStar_Syntax_Syntax.Tm_app (_157_937))
in (FStar_Syntax_Syntax.mk _157_938 None e0.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (_56_1675)) -> begin
(bind_on_lift es ((((e0), (q)))::acc))
end
| _56_1680 -> begin
(bind_on_lift es ((((e), (q)))::acc))
end)
end))
in (

let binded_head = (let _157_940 = (let _157_939 = (FStar_Syntax_Syntax.as_arg head)
in (_157_939)::args)
in (bind_on_lift _157_940 []))
in (let _157_941 = (FStar_List.tl stack)
in (norm cfg env _157_941 binded_head)))))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (reify_lift cfg.tcenv e msrc mtgt t')
in (norm cfg env stack lifted))
end
| _56_1692 -> begin
(norm cfg env stack head)
end)
end)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _56_1705; FStar_Syntax_Syntax.pos = _56_1703; FStar_Syntax_Syntax.vars = _56_1701}, _56_1710, _56_1712))::_56_1699 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| _56_1717 -> begin
false
end)
in if should_reify then begin
(let _157_943 = (FStar_List.tl stack)
in (let _157_942 = (reify_lift cfg.tcenv head m m' t)
in (norm cfg env _157_943 _157_942)))
end else begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _56_1720 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _56_1720.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end)
end
| _56_1724 -> begin
(match (stack) with
| (_56_1728)::_56_1726 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _56_1733) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _56_1740 -> begin
(norm cfg env stack head)
end)
end
| _56_1742 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _157_944 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_157_944))
end
| _56_1747 -> begin
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

let _56_1759 = ed.FStar_Syntax_Syntax.return_repr
in (match (_56_1759) with
| (_56_1757, return_repr) -> begin
(

let return_inst = (match ((let _157_950 = (FStar_Syntax_Subst.compress return_repr)
in _157_950.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (_56_1762)::[]) -> begin
(let _157_954 = (let _157_953 = (let _157_952 = (let _157_951 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_157_951)::[])
in ((return_tm), (_157_952)))
in FStar_Syntax_Syntax.Tm_uinst (_157_953))
in (FStar_Syntax_Syntax.mk _157_954 None e.FStar_Syntax_Syntax.pos))
end
| _56_1767 -> begin
(failwith "NIY : Reification of indexed effects")
end)
in (let _157_960 = (let _157_959 = (let _157_958 = (let _157_957 = (FStar_Syntax_Syntax.as_arg t)
in (let _157_956 = (let _157_955 = (FStar_Syntax_Syntax.as_arg e)
in (_157_955)::[])
in (_157_957)::_157_956))
in ((return_inst), (_157_958)))
in FStar_Syntax_Syntax.Tm_app (_157_959))
in (FStar_Syntax_Syntax.mk _157_960 None e.FStar_Syntax_Syntax.pos)))
end)))
end else begin
(failwith "NYI: non pure monadic lift normalisation")
end)
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _56_1774 -> (match (_56_1774) with
| (a, imp) -> begin
(let _157_965 = (norm cfg env [] a)
in ((_157_965), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _56_1783 = comp
in (let _157_972 = (let _157_971 = (let _157_970 = (norm cfg env [] t)
in (let _157_969 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_157_970), (_157_969))))
in FStar_Syntax_Syntax.Total (_157_971))
in {FStar_Syntax_Syntax.n = _157_972; FStar_Syntax_Syntax.tk = _56_1783.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _56_1783.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1783.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _56_1789 = comp
in (let _157_976 = (let _157_975 = (let _157_974 = (norm cfg env [] t)
in (let _157_973 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_157_974), (_157_973))))
in FStar_Syntax_Syntax.GTotal (_157_975))
in {FStar_Syntax_Syntax.n = _157_976; FStar_Syntax_Syntax.tk = _56_1789.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _56_1789.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1789.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _56_1797 -> (match (_56_1797) with
| (a, i) -> begin
(let _157_980 = (norm cfg env [] a)
in ((_157_980), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___264 -> (match (uu___264) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _157_982 = (norm cfg env [] t)
in FStar_Syntax_Syntax.DECREASES (_157_982))
end
| f -> begin
f
end))))
in (

let _56_1803 = comp
in (let _157_987 = (let _157_986 = (

let _56_1805 = ct
in (let _157_985 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _157_984 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _157_983 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _157_985; FStar_Syntax_Syntax.effect_name = _56_1805.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _157_984; FStar_Syntax_Syntax.effect_args = _157_983; FStar_Syntax_Syntax.flags = flags}))))
in FStar_Syntax_Syntax.Comp (_157_986))
in {FStar_Syntax_Syntax.n = _157_987; FStar_Syntax_Syntax.tk = _56_1803.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _56_1803.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1803.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _56_1812 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _56_1812.tcenv; delta_level = _56_1812.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _157_995 = (norm t)
in (FStar_Syntax_Util.non_informative _157_995)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_56_1817) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _56_1823 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _56_1823.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _56_1823.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1823.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _56_1830 = ct
in {FStar_Syntax_Syntax.comp_univs = _56_1830.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _56_1830.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _56_1830.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _56_1830.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _56_1834 = ct
in {FStar_Syntax_Syntax.comp_univs = _56_1834.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _56_1834.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _56_1834.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _56_1834.FStar_Syntax_Syntax.flags}))
end)
in (

let _56_1837 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _56_1837.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _56_1837.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _56_1837.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _56_1840 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _56_1845 -> (match (_56_1845) with
| (x, imp) -> begin
(let _157_1000 = (

let _56_1846 = x
in (let _157_999 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_1846.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1846.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_999}))
in ((_157_1000), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _56_1859 = (FStar_List.fold_left (fun _56_1853 b -> (match (_56_1853) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_56_1859) with
| (nbs, _56_1858) -> begin
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
(let _157_1012 = (let _157_1011 = (let _157_1010 = (let _157_1009 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags _157_1009 flags))
in (FStar_Syntax_Util.lcomp_of_comp _157_1010))
in FStar_Util.Inl (_157_1011))
in Some (_157_1012))
end else begin
(let _157_1016 = (let _157_1015 = (let _157_1014 = (let _157_1013 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags _157_1013 flags))
in (FStar_Syntax_Util.lcomp_of_comp _157_1014))
in FStar_Util.Inl (_157_1015))
in Some (_157_1016))
end)
end else begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)
end
| _56_1869 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
(

let _56_1879 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms"))) then begin
(let _157_1022 = (FStar_Syntax_Print.term_to_string tm)
in (let _157_1021 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _157_1022 _157_1021)))
end else begin
()
end
in (rebuild cfg env stack t))
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _56_1887 = cfg
in {steps = s; tcenv = _56_1887.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _56_1900 = (set_memo r ((env), (t)))
in (

let _56_1903 = (log cfg (fun _56_1902 -> (match (()) with
| () -> begin
(let _157_1024 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _157_1024))
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
in (let _157_1025 = (

let _56_1926 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _56_1926.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_1926.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _56_1926.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _157_1025))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _56_1962), aq, r))::stack -> begin
(

let _56_1971 = (log cfg (fun _56_1970 -> (match (()) with
| () -> begin
(let _157_1027 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _157_1027))
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
| Some (_56_1981, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _157_1028 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _157_1028)))
end
| (Match (env, branches, r))::stack -> begin
(

let _56_2002 = (log cfg (fun _56_2001 -> (match (()) with
| () -> begin
(let _157_1030 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _157_1030))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _56_2006 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___265 -> (match (uu___265) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| _56_2012 -> begin
false
end))))
in (

let steps' = if (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)) then begin
(Exclude (Zeta))::[]
end else begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end
in (

let _56_2015 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = _56_2015.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg_exclude_iota_zeta env t)
end else begin
(norm cfg_exclude_iota_zeta env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_56_2025) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _56_2035 = (norm_pat env hd)
in (match (_56_2035) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _157_1043 = (norm_pat env p)
in (Prims.fst _157_1043)))))
in (((

let _56_2038 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _56_2038.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_2038.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _56_2055 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _56_2046 _56_2049 -> (match (((_56_2046), (_56_2049))) with
| ((pats, env), (p, b)) -> begin
(

let _56_2052 = (norm_pat env p)
in (match (_56_2052) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_56_2055) with
| (pats, env) -> begin
(((

let _56_2056 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _56_2056.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_2056.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _56_2060 = x
in (let _157_1046 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_2060.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2060.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_1046}))
in (((

let _56_2063 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _56_2063.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_2063.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _56_2067 = x
in (let _157_1047 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_2067.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2067.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_1047}))
in (((

let _56_2070 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _56_2070.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_2070.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _56_2076 = x
in (let _157_1048 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _56_2076.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2076.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_1048}))
in (

let t = (norm_or_whnf env t)
in (((

let _56_2080 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _56_2080.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _56_2080.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _56_2084 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _56_2089 = (FStar_Syntax_Subst.open_branch branch)
in (match (_56_2089) with
| (p, wopt, e) -> begin
(

let _56_2092 = (norm_pat env p)
in (match (_56_2092) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _157_1050 = (norm_or_whnf env w)
in Some (_157_1050))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _157_1051 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _157_1051)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _56_2103) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _56_2128 -> begin
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

let _56_2145 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_56_2145) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_56_2151) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_56_2168) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _56_2175 -> begin
(let _157_1068 = (not ((is_cons head)))
in FStar_Util.Inr (_157_1068))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _157_1069 = (FStar_Syntax_Util.un_uinst head)
in _157_1069.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _56_2183 -> begin
(let _157_1070 = (not ((is_cons head)))
in FStar_Util.Inr (_157_1070))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _56_2193))::rest_a, ((p, _56_2199))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _56_2207 -> begin
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

let _56_2225 = (log cfg (fun _56_2224 -> (match (()) with
| () -> begin
(let _157_1081 = (FStar_Syntax_Print.pat_to_string p)
in (let _157_1080 = (let _157_1079 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _157_1079 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _157_1081 _157_1080)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _157_1086 = (let _157_1085 = (let _157_1084 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_157_1084), (false)))
in Clos (_157_1085))
in (_157_1086)::env)) env s)
in (let _157_1087 = (guard_when_clause wopt b rest)
in (norm cfg env stack _157_1087))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___266 -> (match (uu___266) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| _56_2238 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| _56_2242 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _157_1099 = (config s e)
in (norm _157_1099 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _157_1106 = (config s e)
in (norm_comp _157_1106 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _157_1111 = (config [] env)
in (norm_universe _157_1111 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _157_1116 = (config [] env)
in (ghost_to_pure_aux _157_1116 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _157_1123 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _157_1123)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _56_2261 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _56_2261.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _56_2261.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _56_2263 -> (match (()) with
| () -> begin
(let _157_1125 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _157_1125))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _157_1130 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _157_1130)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _157_1136 = (let _157_1135 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _157_1135 [] c))
in (FStar_Syntax_Print.comp_to_string _157_1136)))


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
(let _157_1147 = (let _157_1146 = (let _157_1145 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_157_1145)))
in FStar_Syntax_Syntax.Tm_refine (_157_1146))
in (mk _157_1147 t0.FStar_Syntax_Syntax.pos))
end
| _56_2286 -> begin
t
end))
end
| _56_2288 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let _56_2293 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_56_2293) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _56_2296 -> begin
(

let _56_2299 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_56_2299) with
| (binders, args) -> begin
(let _157_1156 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _157_1155 = (let _157_1154 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _157_1152 -> FStar_Util.Inl (_157_1152)))
in (FStar_All.pipe_right _157_1154 (fun _157_1153 -> Some (_157_1153))))
in (FStar_Syntax_Util.abs binders _157_1156 _157_1155)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (match ((let _157_1161 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_157_1161), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _56_2305) -> begin
(let _157_1162 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _157_1162))
end
| (_56_2308, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| _56_2313 -> begin
(

let _56_2316 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_2316) with
| (head, args) -> begin
(match ((let _157_1163 = (FStar_Syntax_Subst.compress head)
in _157_1163.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_56_2318, thead) -> begin
(

let _56_2324 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_56_2324) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _56_2332 = (env.FStar_TypeChecker_Env.type_of (

let _56_2325 = env
in {FStar_TypeChecker_Env.solver = _56_2325.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_2325.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_2325.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_2325.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_2325.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_2325.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _56_2325.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_2325.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_2325.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_2325.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_2325.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_2325.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_2325.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_2325.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _56_2325.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _56_2325.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_2325.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _56_2325.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _56_2325.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_2325.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _56_2325.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_56_2332) with
| (_56_2328, ty, _56_2331) -> begin
(eta_expand_with_type t ty)
end))
end
end))
end
| _56_2334 -> begin
(

let _56_2342 = (env.FStar_TypeChecker_Env.type_of (

let _56_2335 = env
in {FStar_TypeChecker_Env.solver = _56_2335.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _56_2335.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _56_2335.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _56_2335.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _56_2335.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _56_2335.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _56_2335.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _56_2335.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _56_2335.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _56_2335.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _56_2335.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _56_2335.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _56_2335.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _56_2335.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _56_2335.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _56_2335.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _56_2335.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _56_2335.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _56_2335.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _56_2335.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _56_2335.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_56_2342) with
| (_56_2338, ty, _56_2341) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end))





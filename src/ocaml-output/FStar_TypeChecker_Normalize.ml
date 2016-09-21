
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Primops
| Inline
| NoInline
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
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


let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoInline = (fun _discr_ -> (match (_discr_) with
| NoInline (_) -> begin
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
| Exclude (_53_8) -> begin
_53_8
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_11) -> begin
_53_11
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
| Clos (_53_14) -> begin
_53_14
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_17) -> begin
_53_17
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_20, t, _53_23, _53_25) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_29 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}


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
| Steps of (steps * FStar_TypeChecker_Env.delta_level)


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
| Arg (_53_36) -> begin
_53_36
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_39) -> begin
_53_39
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_42) -> begin
_53_42
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_45) -> begin
_53_45
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_48) -> begin
_53_48
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_51) -> begin
_53_51
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_54) -> begin
_53_54
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_57) -> begin
_53_57
end))


let ___Steps____0 = (fun projectee -> (match (projectee) with
| Steps (_53_60) -> begin
_53_60
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_66) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_214 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_214 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_73, _53_75) -> begin
(closure_to_string c)
end
| MemoLazy (_53_79) -> begin
"MemoLazy"
end
| Abs (_53_82, bs, _53_85, _53_87, _53_89) -> begin
(let _147_217 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_217))
end
| _53_93 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_220 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_220 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_100 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_107 -> begin
(let _147_236 = (let _147_235 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_235))
in (FStar_All.failwith _147_236))
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
| _53_123 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (match ((let _147_245 = (FStar_List.hd c.FStar_Syntax_Syntax.comp_univs)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _147_245 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_135 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_135) with
| (binders, cdef) -> begin
(

let inst = (let _147_249 = (let _147_248 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_248)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_139 _53_143 -> (match (((_53_139), (_53_143))) with
| ((x, _53_138), (t, _53_142)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _147_249))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _147_250 = (

let _53_146 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_146.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_146.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_146.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_146.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _147_250 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c))))
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

let _53_168 = (FStar_List.fold_left (fun _53_159 u -> (match (_53_159) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_163 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_163) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_168) with
| (_53_165, u, out) -> begin
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
| _53_185 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_178 -> begin
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

let us = (let _147_267 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_267 norm_univs))
in (match (us) with
| (u_k)::rest -> begin
(match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_209 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_209) with
| (_53_207, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_211 -> begin
us
end)
end
| _53_213 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_270 = (aux u)
in (FStar_List.map (fun _147_269 -> FStar_Syntax_Syntax.U_succ (_147_269)) _147_270))
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

let _53_232 = (log cfg (fun _53_231 -> (match (()) with
| () -> begin
(let _147_294 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_293 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _147_294 _147_293)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_236 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_239) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_252) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_299 = (let _147_298 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_298))
in (mk _147_299 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_300 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_300))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_263) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_270) -> begin
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

let _53_286 = (closures_as_binders_delayed cfg env bs)
in (match (_53_286) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _147_303 = (let _147_302 = (let _147_301 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_147_301)))
in FStar_Syntax_Syntax.Tm_abs (_147_302))
in (mk _147_303 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_294 = (closures_as_binders_delayed cfg env bs)
in (match (_53_294) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_302 = (let _147_305 = (let _147_304 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_304)::[])
in (closures_as_binders_delayed cfg env _147_305))
in (match (_53_302) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _147_309 = (let _147_308 = (let _147_307 = (let _147_306 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_306 Prims.fst))
in ((_147_307), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_147_308))
in (mk _147_309 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _147_315 = (let _147_314 = (let _147_313 = (closure_as_term_delayed cfg env t1)
in (let _147_312 = (let _147_311 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _147_310 -> FStar_Util.Inl (_147_310)) _147_311))
in ((_147_313), (_147_312), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_314))
in (mk _147_315 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _147_321 = (let _147_320 = (let _147_319 = (closure_as_term_delayed cfg env t1)
in (let _147_318 = (let _147_317 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _147_316 -> FStar_Util.Inr (_147_316)) _147_317))
in ((_147_319), (_147_318), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_320))
in (mk _147_321 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _147_326 = (let _147_325 = (let _147_324 = (closure_as_term_delayed cfg env t')
in (let _147_323 = (let _147_322 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_147_322))
in ((_147_324), (_147_323))))
in FStar_Syntax_Syntax.Tm_meta (_147_325))
in (mk _147_326 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _147_332 = (let _147_331 = (let _147_330 = (closure_as_term_delayed cfg env t')
in (let _147_329 = (let _147_328 = (let _147_327 = (closure_as_term_delayed cfg env tbody)
in ((m), (_147_327)))
in FStar_Syntax_Syntax.Meta_monadic (_147_328))
in ((_147_330), (_147_329))))
in FStar_Syntax_Syntax.Tm_meta (_147_331))
in (mk _147_332 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_335 = (let _147_334 = (let _147_333 = (closure_as_term_delayed cfg env t')
in ((_147_333), (m)))
in FStar_Syntax_Syntax.Tm_meta (_147_334))
in (mk _147_335 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_341 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_347) -> begin
body
end
| FStar_Util.Inl (_53_350) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_353 = lb
in {FStar_Syntax_Syntax.lbname = _53_353.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_353.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_353.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_357, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_366 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_370 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_374 = lb
in (let _147_347 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_346 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_374.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_374.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_347; FStar_Syntax_Syntax.lbeff = _53_374.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_346}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_377 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_392 -> (match (_53_392) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_397) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_407 = (norm_pat env hd)
in (match (_53_407) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_359 = (norm_pat env p)
in (Prims.fst _147_359)))))
in (((

let _53_410 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_410.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_410.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_427 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_418 _53_421 -> (match (((_53_418), (_53_421))) with
| ((pats, env), (p, b)) -> begin
(

let _53_424 = (norm_pat env p)
in (match (_53_424) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_427) with
| (pats, env) -> begin
(((

let _53_428 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_428.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_428.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_432 = x
in (let _147_362 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_432.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_432.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_362}))
in (((

let _53_435 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_435.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_435.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_439 = x
in (let _147_363 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_439.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_439.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_363}))
in (((

let _53_442 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_442.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_442.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_448 = x
in (let _147_364 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_448.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_448.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_364}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_452 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_452.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_452.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_456 = (norm_pat env pat)
in (match (_53_456) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_365 = (closure_as_term cfg env w)
in Some (_147_365))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _147_368 = (let _147_367 = (let _147_366 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_147_366)))
in FStar_Syntax_Syntax.Tm_match (_147_367))
in (mk _147_368 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_467 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_473 -> begin
(FStar_List.map (fun _53_476 -> (match (_53_476) with
| (x, imp) -> begin
(let _147_376 = (closure_as_term_delayed cfg env x)
in ((_147_376), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_492 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_482 _53_485 -> (match (((_53_482), (_53_485))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_486 = b
in (let _147_382 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_486.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_486.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_382}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_492) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_498 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _147_387 = (closure_as_term_delayed cfg env t)
in (let _147_386 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _147_387 _147_386)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _147_389 = (closure_as_term_delayed cfg env t)
in (let _147_388 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _147_389 _147_388)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_391 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_391))
end
| f -> begin
f
end))))
in (let _147_393 = (

let _53_516 = c
in (let _147_392 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _147_392; FStar_Syntax_Syntax.effect_name = _53_516.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
in (FStar_Syntax_Syntax.mk_Comp _147_393)))))
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
| _53_525 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _147_406 = (let _147_405 = (FStar_Util.string_of_int i)
in ((_147_405), (None)))
in FStar_Const.Const_int (_147_406)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]))


let reduce_primops = (fun steps tm -> (

let arith_op = (fun fv -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_557 -> (match (_53_557) with
| (l, _53_556) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) arith_ops)
end
| _53_559 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_567))::((a2, _53_563))::[]) -> begin
(match ((arith_op fv)) with
| None -> begin
tm
end
| Some (_53_574, op) -> begin
(match ((let _147_588 = (let _147_585 = (FStar_Syntax_Subst.compress a1)
in _147_585.FStar_Syntax_Syntax.n)
in (let _147_587 = (let _147_586 = (FStar_Syntax_Subst.compress a2)
in _147_586.FStar_Syntax_Syntax.n)
in ((_147_588), (_147_587))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(

let c = (let _147_590 = (FStar_Util.int_of_string i)
in (let _147_589 = (FStar_Util.int_of_string j)
in (op _147_590 _147_589)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos))
end
| _53_591 -> begin
tm
end)
end)
end
| _53_593 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_598 = t
in {FStar_Syntax_Syntax.n = _53_598.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_598.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_598.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_607 -> begin
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
| _53_685 -> begin
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
| _53_728 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_755))::((_53_746, (arg, _53_749)))::[] -> begin
arg
end
| _53_759 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_763))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_769))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_773 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _147_601 = (FStar_Syntax_Subst.compress t)
in _147_601.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_791)::[], body, _53_795) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_803 -> begin
tm
end)
end
| _53_805 -> begin
tm
end)
end
| _53_807 -> begin
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
| _53_809 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_816 = (log cfg (fun _53_815 -> (match (()) with
| () -> begin
(let _147_634 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_633 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_634 _147_633)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_819) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_861; FStar_Syntax_Syntax.pos = _53_859; FStar_Syntax_Syntax.vars = _53_857}, ((tm, _53_867))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_873 = cfg
in {steps = s; tcenv = _53_873.tcenv; delta_level = FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)})
in (

let stack' = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_882; FStar_Syntax_Syntax.pos = _53_880; FStar_Syntax_Syntax.vars = _53_878}, (a1)::(a2)::rest) -> begin
(

let _53_896 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_896) with
| (hd, _53_895) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_904; FStar_Syntax_Syntax.pos = _53_902; FStar_Syntax_Syntax.vars = _53_900}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_915 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_915) with
| (reify_head, _53_914) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _147_638 = (FStar_Syntax_Subst.compress e)
in _147_638.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_935 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_935) with
| (_53_933, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _147_643 = (let _147_642 = (let _147_641 = (let _147_639 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_639)::[])
in (let _147_640 = (FStar_Syntax_Util.mk_reify body)
in ((_147_641), (_147_640), (None))))
in FStar_Syntax_Syntax.Tm_abs (_147_642))
in (FStar_Syntax_Syntax.mk _147_643 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _147_657 = (let _147_656 = (let _147_655 = (let _147_654 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_653 = (let _147_652 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _147_651 = (let _147_650 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_649 = (let _147_648 = (FStar_Syntax_Syntax.as_arg head)
in (let _147_647 = (let _147_646 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_645 = (let _147_644 = (FStar_Syntax_Syntax.as_arg body)
in (_147_644)::[])
in (_147_646)::_147_645))
in (_147_648)::_147_647))
in (_147_650)::_147_649))
in (_147_652)::_147_651))
in (_147_654)::_147_653))
in ((bind_repr), (_147_655)))
in FStar_Syntax_Syntax.Tm_app (_147_656))
in (FStar_Syntax_Syntax.mk _147_657 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_942) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_945) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_948 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_957)); FStar_Syntax_Syntax.tk = _53_955; FStar_Syntax_Syntax.pos = _53_953; FStar_Syntax_Syntax.vars = _53_951}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_973 -> (match (_53_973) with
| (pat, wopt, tm) -> begin
(let _147_659 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_147_659)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_977 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _147_660 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_660)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _147_662 = (let _147_661 = (FStar_List.map (norm_universe cfg env) us)
in ((_147_661), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_147_662))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (match (cfg.delta_level) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| FStar_TypeChecker_Env.OnlyInline -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end)
in if (not (should_delta)) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_1002 = (log cfg (fun _53_1001 -> (match (()) with
| () -> begin
(let _147_665 = (FStar_Syntax_Print.term_to_string t0)
in (let _147_664 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _147_665 _147_664)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1008))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1016 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1018 -> begin
(let _147_669 = (let _147_668 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_668))
in (FStar_All.failwith _147_669))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1022) -> begin
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

let _53_1036 = (log cfg (fun _53_1035 -> (match (()) with
| () -> begin
(let _147_672 = (FStar_Syntax_Print.term_to_string t)
in (let _147_671 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_672 _147_671)))
end)))
in (match ((let _147_673 = (FStar_Syntax_Subst.compress t')
in _147_673.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1039) -> begin
(norm cfg env stack t')
end
| _53_1042 -> begin
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
| (Meta (_53_1052))::_53_1050 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_1058))::_53_1056 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1064))::_53_1062 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1070, _53_1072))::stack_rest -> begin
(match (c) with
| Univ (_53_1077) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1080 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1083)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1087 = (log cfg (fun _53_1086 -> (match (()) with
| () -> begin
(let _147_675 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_675))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1093 = (log cfg (fun _53_1092 -> (match (()) with
| () -> begin
(let _147_677 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_677))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1099 = (log cfg (fun _53_1098 -> (match (()) with
| () -> begin
(let _147_679 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_679))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1102 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1104 -> begin
(

let cfg = (

let _53_1105 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1105.tcenv; delta_level = _53_1105.delta_level})
in (let _147_680 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_680)))
end)
end
| (_53_1110)::tl -> begin
(

let _53_1113 = (log cfg (fun _53_1112 -> (match (()) with
| () -> begin
(let _147_682 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_682))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1122 = cfg
in {steps = s; tcenv = _53_1122.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1128 = (set_memo r ((env), (t)))
in (

let _53_1131 = (log cfg (fun _53_1130 -> (match (()) with
| () -> begin
(let _147_684 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_684))
end)))
in (norm cfg env stack t)))
end
| ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_685 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_685))
end else begin
(

let _53_1155 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1155) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _147_691 = (let _147_689 = (let _147_687 = (let _147_686 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _147_686))
in (FStar_All.pipe_right _147_687 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_689 (fun _147_688 -> FStar_Util.Inl (_147_688))))
in (FStar_All.pipe_right _147_691 (fun _147_690 -> Some (_147_690))))
end
| _53_1160 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1163 -> (Dummy)::env) env))
in (

let _53_1167 = (log cfg (fun _53_1166 -> (match (()) with
| () -> begin
(let _147_695 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_695))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1175 stack -> (match (_53_1175) with
| (a, aq) -> begin
(let _147_702 = (let _147_701 = (let _147_700 = (let _147_699 = (let _147_698 = (FStar_Util.mk_ref None)
in ((env), (a), (_147_698), (false)))
in Clos (_147_699))
in ((_147_700), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_147_701))
in (_147_702)::stack)
end)) args))
in (

let _53_1179 = (log cfg (fun _53_1178 -> (match (()) with
| () -> begin
(let _147_704 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_704))
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

let _53_1189 = x
in {FStar_Syntax_Syntax.ppname = _53_1189.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1189.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1193 -> begin
(let _147_705 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_705))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1197 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1197) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _147_708 = (let _147_707 = (let _147_706 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1199 = x
in {FStar_Syntax_Syntax.ppname = _53_1199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_147_706)))
in FStar_Syntax_Syntax.Tm_refine (_147_707))
in (mk _147_708 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_709 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_709))
end else begin
(

let _53_1208 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1208) with
| (bs, c) -> begin
(

let c = (let _147_712 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1210 -> (Dummy)::env) env))
in (norm_comp cfg _147_712 c))
in (

let t = (let _147_713 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_713 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1238 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1241 = (log cfg (fun _53_1240 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _147_715 = (norm cfg env [] t)
in FStar_Util.Inl (_147_715))
end
| FStar_Util.Inr (c) -> begin
(let _147_716 = (norm_comp cfg env c)
in FStar_Util.Inr (_147_716))
end)
in (let _147_717 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_717)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1254, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1266); FStar_Syntax_Syntax.lbunivs = _53_1264; FStar_Syntax_Syntax.lbtyp = _53_1262; FStar_Syntax_Syntax.lbeff = _53_1260; FStar_Syntax_Syntax.lbdef = _53_1258})::_53_1256), _53_1272) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _147_720 = (let _147_719 = (let _147_718 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_147_718), (false)))
in Clos (_147_719))
in (_147_720)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1286 = (let _147_723 = (let _147_722 = (let _147_721 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _147_721 FStar_Syntax_Syntax.mk_binder))
in (_147_722)::[])
in (FStar_Syntax_Subst.open_term _147_723 body))
in (match (_53_1286) with
| (bs, body) -> begin
(

let lb = (

let _53_1287 = lb
in (let _147_729 = (let _147_726 = (let _147_724 = (FStar_List.hd bs)
in (FStar_All.pipe_right _147_724 Prims.fst))
in (FStar_All.pipe_right _147_726 (fun _147_725 -> FStar_Util.Inl (_147_725))))
in (let _147_728 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_727 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _147_729; FStar_Syntax_Syntax.lbunivs = _53_1287.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_728; FStar_Syntax_Syntax.lbeff = _53_1287.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_727}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1291 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _147_732 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_732))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1317 = (FStar_List.fold_right (fun lb _53_1306 -> (match (_53_1306) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _147_735 = (

let _53_1307 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1307.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1307.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_735))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1317) with
| (rec_env, memos, _53_1316) -> begin
(

let _53_1320 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _147_742 = (let _147_741 = (let _147_740 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_147_740), (false)))
in Clos (_147_741))
in (_147_742)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_1332)::_53_1330 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1337) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let t = (norm cfg env [] t)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1349 -> begin
(norm cfg env stack head)
end)
end
| _53_1351 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_743 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_743))
end
| _53_1356 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1364 -> (match (_53_1364) with
| (a, imp) -> begin
(let _147_748 = (norm cfg env [] a)
in ((_147_748), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1373 = comp
in (let _147_755 = (let _147_754 = (let _147_753 = (norm cfg env [] t)
in (let _147_752 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_753), (_147_752))))
in FStar_Syntax_Syntax.Total (_147_754))
in {FStar_Syntax_Syntax.n = _147_755; FStar_Syntax_Syntax.tk = _53_1373.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1373.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1373.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1379 = comp
in (let _147_759 = (let _147_758 = (let _147_757 = (norm cfg env [] t)
in (let _147_756 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_757), (_147_756))))
in FStar_Syntax_Syntax.GTotal (_147_758))
in {FStar_Syntax_Syntax.n = _147_759; FStar_Syntax_Syntax.tk = _53_1379.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1379.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1379.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1387 -> (match (_53_1387) with
| (a, i) -> begin
(let _147_763 = (norm cfg env [] a)
in ((_147_763), (i)))
end)))))
in (

let _53_1388 = comp
in (let _147_768 = (let _147_767 = (

let _53_1390 = ct
in (let _147_766 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _147_765 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_764 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _147_766; FStar_Syntax_Syntax.effect_name = _53_1390.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_765; FStar_Syntax_Syntax.effect_args = _147_764; FStar_Syntax_Syntax.flags = _53_1390.FStar_Syntax_Syntax.flags}))))
in FStar_Syntax_Syntax.Comp (_147_767))
in {FStar_Syntax_Syntax.n = _147_768; FStar_Syntax_Syntax.tk = _53_1388.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1388.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1388.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1397 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1397.tcenv; delta_level = _53_1397.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _147_776 = (norm t)
in (FStar_Syntax_Util.non_informative _147_776)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1402) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1408 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1408.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1408.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1408.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1415 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1415.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1415.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1415.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1415.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1419 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1419.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1419.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1419.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1419.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1422 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1422.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1422.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1422.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1425 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1430 -> (match (_53_1430) with
| (x, imp) -> begin
(let _147_781 = (

let _53_1431 = x
in (let _147_780 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1431.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1431.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_780}))
in ((_147_781), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1444 = (FStar_List.fold_left (fun _53_1438 b -> (match (_53_1438) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1444) with
| (nbs, _53_1443) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _147_792 = (let _147_791 = (let _147_790 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _147_790))
in FStar_Util.Inl (_147_791))
in Some (_147_792))
end else begin
(let _147_795 = (let _147_794 = (let _147_793 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _147_793))
in FStar_Util.Inl (_147_794))
in Some (_147_795))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1453 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1465 = cfg
in {steps = s; tcenv = _53_1465.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1478 = (set_memo r ((env), (t)))
in (

let _53_1481 = (log cfg (fun _53_1480 -> (match (()) with
| () -> begin
(let _147_801 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_801))
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
in (let _147_802 = (

let _53_1504 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1504.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1504.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1504.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_802))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1540), aq, r))::stack -> begin
(

let _53_1549 = (log cfg (fun _53_1548 -> (match (()) with
| () -> begin
(let _147_804 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_804))
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
| Some (_53_1559, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _147_805 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_805)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1580 = (log cfg (fun _53_1579 -> (match (()) with
| () -> begin
(let _147_807 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _147_807))
end)))
in (

let norm_and_rebuild_match = (fun _53_1583 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1585 = cfg
in (let _147_810 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1585.tcenv; delta_level = _147_810}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1595) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1605 = (norm_pat env hd)
in (match (_53_1605) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_820 = (norm_pat env p)
in (Prims.fst _147_820)))))
in (((

let _53_1608 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1608.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1608.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1625 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1616 _53_1619 -> (match (((_53_1616), (_53_1619))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1622 = (norm_pat env p)
in (match (_53_1622) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1625) with
| (pats, env) -> begin
(((

let _53_1626 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1626.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1626.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1630 = x
in (let _147_823 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1630.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1630.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_823}))
in (((

let _53_1633 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1633.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1633.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1637 = x
in (let _147_824 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1637.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1637.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_824}))
in (((

let _53_1640 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1640.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1640.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1646 = x
in (let _147_825 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1646.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1646.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_825}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1650 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1650.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1650.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1654 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1659 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1659) with
| (p, wopt, e) -> begin
(

let _53_1662 = (norm_pat env p)
in (match (_53_1662) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_827 = (norm_or_whnf env w)
in Some (_147_827))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _147_828 = (mk (FStar_Syntax_Syntax.Tm_match (((t), (branches)))) r)
in (rebuild cfg env stack _147_828)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1673) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1698 -> begin
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

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((t), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun t p -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_1715 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1715) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1721) -> begin
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
FStar_Util.Inl ((t)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (_53_1738) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1745 -> begin
(let _147_845 = (not ((is_cons head)))
in FStar_Util.Inr (_147_845))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _147_846 = (FStar_Syntax_Util.un_uinst head)
in _147_846.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1753 -> begin
(let _147_847 = (not ((is_cons head)))
in FStar_Util.Inr (_147_847))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1763))::rest_a, ((p, _53_1769))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1777 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun t p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inr (false) -> begin
(matches t rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _53_1795 = (log cfg (fun _53_1794 -> (match (()) with
| () -> begin
(let _147_858 = (FStar_Syntax_Print.pat_to_string p)
in (let _147_857 = (let _147_856 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _147_856 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _147_858 _147_857)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _147_863 = (let _147_862 = (let _147_861 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_147_861), (false)))
in Clos (_147_862))
in (_147_863)::env)) env s)
in (let _147_864 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_864))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches t branches)
end))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (match ((FStar_Util.find_map s (fun _53_5 -> (match (_53_5) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1806 -> begin
None
end)))) with
| Some (k) -> begin
FStar_TypeChecker_Env.Unfold (k)
end
| None -> begin
if (FStar_List.contains Inline s) then begin
FStar_TypeChecker_Env.OnlyInline
end else begin
FStar_TypeChecker_Env.NoDelta
end
end)
in {steps = s; tcenv = e; delta_level = d}))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_876 = (config s e)
in (norm _147_876 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_883 = (config s e)
in (norm_comp _147_883 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_888 = (config [] env)
in (norm_universe _147_888 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_893 = (config [] env)
in (ghost_to_pure_aux _147_893 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _147_900 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _147_900)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1828 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1828.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1828.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1830 -> (match (()) with
| () -> begin
(let _147_902 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _147_902))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_907 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_907)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_913 = (let _147_912 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_912 [] c))
in (FStar_Syntax_Print.comp_to_string _147_913)))


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
(let _147_924 = (let _147_923 = (let _147_922 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_147_922)))
in FStar_Syntax_Syntax.Tm_refine (_147_923))
in (mk _147_924 t0.FStar_Syntax_Syntax.pos))
end
| _53_1853 -> begin
t
end))
end
| _53_1855 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1862 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1862) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1865 -> begin
(

let _53_1868 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1868) with
| (binders, args) -> begin
(let _147_935 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_934 = (let _147_933 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_931 -> FStar_Util.Inl (_147_931)))
in (FStar_All.pipe_right _147_933 (fun _147_932 -> Some (_147_932))))
in (FStar_Syntax_Util.abs binders _147_935 _147_934)))
end))
end)
end)))
in (match ((let _147_936 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_147_936), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1872) -> begin
(let _147_937 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _147_937))
end
| (_53_1875, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1880 -> begin
(

let _53_1883 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1883) with
| (head, args) -> begin
(match ((let _147_938 = (FStar_Syntax_Subst.compress head)
in _147_938.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1885, thead) -> begin
(

let _53_1891 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1891) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1899 = (env.FStar_TypeChecker_Env.type_of (

let _53_1892 = env
in {FStar_TypeChecker_Env.solver = _53_1892.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1892.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1892.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1892.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1892.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1892.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1892.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1892.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1892.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1892.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1892.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1892.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1892.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1892.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1892.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1892.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1892.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1892.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1892.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1892.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1892.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1899) with
| (_53_1895, ty, _53_1898) -> begin
(expand ty)
end))
end
end))
end
| _53_1901 -> begin
(

let _53_1909 = (env.FStar_TypeChecker_Env.type_of (

let _53_1902 = env
in {FStar_TypeChecker_Env.solver = _53_1902.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1902.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1902.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1902.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1902.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1902.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1902.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1902.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1902.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1902.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1902.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1902.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1902.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1902.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1902.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1902.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1902.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1902.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1902.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1902.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1902.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1909) with
| (_53_1905, ty, _53_1908) -> begin
(expand ty)
end))
end)
end))
end)))





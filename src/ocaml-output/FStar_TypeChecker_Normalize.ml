
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Inline
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| BetaUVars
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| DeltaComp
| SNComp
| Eta
| EtaArgs
| Unmeta
| Unlabel 
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


let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
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


let is_BetaUVars = (fun _discr_ -> (match (_discr_) with
| BetaUVars (_) -> begin
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


let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))


let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
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


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_60) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _145_190 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _145_190 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_67, _53_69) -> begin
(closure_to_string c)
end
| MemoLazy (_53_73) -> begin
"MemoLazy"
end
| Abs (_53_76, bs, _53_79, _53_81, _53_83) -> begin
(let _145_193 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _145_193))
end
| _53_87 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _145_196 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _145_196 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_94 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_101 -> begin
(let _145_212 = (let _145_211 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _145_211))
in (FStar_All.failwith _145_212))
end)


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _145_217 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _145_217 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_114 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_114) with
| (binders, cdef) -> begin
(

let inst = (let _145_221 = (let _145_220 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_145_220)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_118 _53_122 -> (match ((_53_118, _53_122)) with
| ((x, _53_117), (t, _53_121)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _145_221))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _53_125 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_125.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_125.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_125.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
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

let _53_147 = (FStar_List.fold_left (fun _53_138 u -> (match (_53_138) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_142 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_142) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_53_147) with
| (_53_144, u, out) -> begin
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
(u)::[]
end
| Dummy -> begin
(u)::[]
end
| _53_164 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_157 -> begin
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
(let _145_238 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _145_238 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _145_240 = (aux u)
in (FStar_List.map (fun _145_239 -> FStar_Syntax_Syntax.U_succ (_145_239)) _145_240))
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

let _53_195 = (log cfg (fun _53_194 -> (match (()) with
| () -> begin
(let _145_264 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_263 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _145_264 _145_263)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _53_199 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_202) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_215) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _145_269 = (let _145_268 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_145_268))
in (mk _145_269 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _145_270 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _145_270))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_226) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_233) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_53_241) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _53_247) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _145_276 = (FStar_List.fold_left (fun env' _53_254 -> (match (_53_254) with
| (t, _53_253) -> begin
(let _145_275 = (let _145_274 = (let _145_273 = (FStar_Util.mk_ref None)
in (env, t, _145_273, false))
in Clos (_145_274))
in (_145_275)::env')
end)) env args)
in (closure_as_term cfg _145_276 body))
end
| _53_256 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _53_258 -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _53_268 = (closures_as_binders_delayed cfg env bs)
in (match (_53_268) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _145_279 = (let _145_278 = (let _145_277 = (close_lcomp_opt cfg env lopt)
in (bs, body, _145_277))
in FStar_Syntax_Syntax.Tm_abs (_145_278))
in (mk _145_279 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_276 = (closures_as_binders_delayed cfg env bs)
in (match (_53_276) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_284 = (let _145_281 = (let _145_280 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_280)::[])
in (closures_as_binders_delayed cfg env _145_281))
in (match (_53_284) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _145_285 = (let _145_284 = (let _145_283 = (let _145_282 = (FStar_List.hd x)
in (FStar_All.pipe_right _145_282 Prims.fst))
in (_145_283, phi))
in FStar_Syntax_Syntax.Tm_refine (_145_284))
in (mk _145_285 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _145_291 = (let _145_290 = (let _145_289 = (closure_as_term_delayed cfg env t1)
in (let _145_288 = (let _145_287 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _145_286 -> FStar_Util.Inl (_145_286)) _145_287))
in (_145_289, _145_288, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_145_290))
in (mk _145_291 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _145_297 = (let _145_296 = (let _145_295 = (closure_as_term_delayed cfg env t1)
in (let _145_294 = (let _145_293 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _145_292 -> FStar_Util.Inr (_145_292)) _145_293))
in (_145_295, _145_294, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_145_296))
in (mk _145_297 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _145_302 = (let _145_301 = (let _145_300 = (closure_as_term_delayed cfg env t')
in (let _145_299 = (let _145_298 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_145_298))
in (_145_300, _145_299)))
in FStar_Syntax_Syntax.Tm_meta (_145_301))
in (mk _145_302 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _145_305 = (let _145_304 = (let _145_303 = (closure_as_term_delayed cfg env t')
in (_145_303, m))
in FStar_Syntax_Syntax.Tm_meta (_145_304))
in (mk _145_305 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_316 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_322) -> begin
body
end
| FStar_Util.Inl (_53_325) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_328 = lb
in {FStar_Syntax_Syntax.lbname = _53_328.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_328.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_328.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_332, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_341 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_345 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_349 = lb
in (let _145_317 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _145_316 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_349.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_349.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _145_317; FStar_Syntax_Syntax.lbeff = _53_349.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _145_316}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_352 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_367 -> (match (_53_367) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_372) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_382 = (norm_pat env hd)
in (match (_53_382) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _145_329 = (norm_pat env p)
in (Prims.fst _145_329)))))
in ((

let _53_385 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_385.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_385.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_402 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_393 _53_396 -> (match ((_53_393, _53_396)) with
| ((pats, env), (p, b)) -> begin
(

let _53_399 = (norm_pat env p)
in (match (_53_399) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_53_402) with
| (pats, env) -> begin
((

let _53_403 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _53_403.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_403.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_407 = x
in (let _145_332 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_407.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_407.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_332}))
in ((

let _53_410 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_410.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_410.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_414 = x
in (let _145_333 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_414.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_414.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_333}))
in ((

let _53_417 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_417.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_417.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_423 = x
in (let _145_334 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_423.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_423.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_334}))
in (

let t = (closure_as_term cfg env t)
in ((

let _53_427 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _53_427.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_427.FStar_Syntax_Syntax.p}), env)))
end))
in (

let _53_431 = (norm_pat env pat)
in (match (_53_431) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_335 = (closure_as_term cfg env w)
in Some (_145_335))
end)
in (

let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _145_338 = (let _145_337 = (let _145_336 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _145_336))
in FStar_Syntax_Syntax.Tm_match (_145_337))
in (mk _145_338 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| _53_441 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _53_444 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _53_450 -> begin
(FStar_List.map (fun _53_453 -> (match (_53_453) with
| (x, imp) -> begin
(let _145_346 = (closure_as_term_delayed cfg env x)
in (_145_346, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_469 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_459 _53_462 -> (match ((_53_459, _53_462)) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_463 = b
in (let _145_352 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_463.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_463.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_352}))
in (

let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_53_469) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _53_475 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _145_356 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _145_356))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _145_357 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _145_357))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _145_359 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_145_359))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let _53_489 = c
in {FStar_Syntax_Syntax.effect_name = _53_489.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
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
| _53_498 -> begin
lopt
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_503 = t
in {FStar_Syntax_Syntax.n = _53_503.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_503.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_503.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_512 -> begin
None
end))
in (

let simplify = (fun arg -> ((simp_t (Prims.fst arg)), arg))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
tm
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
| _53_590 -> begin
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
| _53_633 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_660))::((_53_651, (arg, _53_654)))::[] -> begin
arg
end
| _53_664 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_668))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_674))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_678 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _145_373 = (FStar_Syntax_Subst.compress t)
in _145_373.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_696)::[], body, _53_700) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_708 -> begin
tm
end)
end
| _53_710 -> begin
tm
end)
end
| _53_712 -> begin
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
| _53_714 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_721 = (log cfg (fun _53_720 -> (match (()) with
| () -> begin
(let _145_406 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_405 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _145_406 _145_405)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_724) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_766; FStar_Syntax_Syntax.pos = _53_764; FStar_Syntax_Syntax.vars = _53_762}, (a1)::(a2)::rest) -> begin
(

let _53_780 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_780) with
| (hd, _53_779) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, (a1)::[]))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((t', (a2)::rest))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_788; FStar_Syntax_Syntax.pos = _53_786; FStar_Syntax_Syntax.vars = _53_784}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_799 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_799) with
| (reify_head, _53_798) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m)) -> begin
(match ((let _145_410 = (FStar_Syntax_Subst.compress e)
in _145_410.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_817 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_817) with
| (_53_815, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _145_415 = (let _145_414 = (let _145_413 = (let _145_411 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_411)::[])
in (let _145_412 = (FStar_Syntax_Util.mk_reify body)
in (_145_413, _145_412, None)))
in FStar_Syntax_Syntax.Tm_abs (_145_414))
in (FStar_Syntax_Syntax.mk _145_415 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _145_429 = (let _145_428 = (let _145_427 = (let _145_426 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_425 = (let _145_424 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_423 = (let _145_422 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_421 = (let _145_420 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_419 = (let _145_418 = (FStar_Syntax_Syntax.as_arg head)
in (let _145_417 = (let _145_416 = (FStar_Syntax_Syntax.as_arg body)
in (_145_416)::[])
in (_145_418)::_145_417))
in (_145_420)::_145_419))
in (_145_422)::_145_421))
in (_145_424)::_145_423))
in (_145_426)::_145_425))
in (bind_repr, _145_427))
in FStar_Syntax_Syntax.Tm_app (_145_428))
in (FStar_Syntax_Syntax.mk _145_429 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_824) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_827) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_830 -> begin
(

let stack = (App ((reify_head, None, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_839)); FStar_Syntax_Syntax.tk = _53_837; FStar_Syntax_Syntax.pos = _53_835; FStar_Syntax_Syntax.vars = _53_833}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_855 -> (match (_53_855) with
| (pat, wopt, tm) -> begin
(let _145_431 = (FStar_Syntax_Util.mk_reify tm)
in (pat, wopt, _145_431))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match ((e, branches))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_859 -> begin
(

let stack = (App ((reify_head, None, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _145_432 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_432)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _145_434 = (let _145_433 = (FStar_List.map (norm_universe cfg env) us)
in (_145_433, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_145_434))
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

let _53_884 = (log cfg (fun _53_883 -> (match (()) with
| () -> begin
(let _145_437 = (FStar_Syntax_Print.term_to_string t0)
in (let _145_436 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _145_437 _145_436)))
end)))
in (

let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| (UnivArgs (us', _53_890))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_898 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_900 -> begin
(let _145_441 = (let _145_440 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _145_440))
in (FStar_All.failwith _145_441))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_904) -> begin
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

let _53_918 = (log cfg (fun _53_917 -> (match (()) with
| () -> begin
(let _145_444 = (FStar_Syntax_Print.term_to_string t)
in (let _145_443 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _145_444 _145_443)))
end)))
in (match ((let _145_445 = (FStar_Syntax_Subst.compress t')
in _145_445.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_921) -> begin
(norm cfg env stack t')
end
| _53_924 -> begin
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
| (Meta (_53_934))::_53_932 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_940))::_53_938 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_946))::_53_944 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_952, _53_954))::stack -> begin
(match (c) with
| Univ (_53_959) -> begin
(norm cfg ((c)::env) stack t)
end
| _53_962 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_965)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_969 = (log cfg (fun _53_968 -> (match (()) with
| () -> begin
(let _145_447 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_447))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_975 = (log cfg (fun _53_974 -> (match (()) with
| () -> begin
(let _145_449 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_449))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_981 = (log cfg (fun _53_980 -> (match (()) with
| () -> begin
(let _145_451 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_451))
end)))
in (norm cfg ((c)::env) stack body))
end
| _53_984 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack body)
end
| _53_986 -> begin
(

let cfg = (

let _53_987 = cfg
in {steps = (WHNF)::cfg.steps; tcenv = _53_987.tcenv; delta_level = _53_987.delta_level})
in (let _145_452 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_452)))
end)
end
| (_53_992)::tl -> begin
(

let _53_995 = (log cfg (fun _53_994 -> (match (()) with
| () -> begin
(let _145_454 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_454))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack body)))
end)
end)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1002 = (set_memo r (env, t))
in (

let _53_1005 = (log cfg (fun _53_1004 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _145_456 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_456))
end else begin
(

let _53_1023 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1023) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _145_462 = (let _145_460 = (let _145_458 = (let _145_457 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _145_457))
in (FStar_All.pipe_right _145_458 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _145_460 (fun _145_459 -> FStar_Util.Inl (_145_459))))
in (FStar_All.pipe_right _145_462 (fun _145_461 -> Some (_145_461))))
end
| _53_1028 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1031 -> (Dummy)::env) env))
in (

let _53_1035 = (log cfg (fun _53_1034 -> (match (()) with
| () -> begin
(let _145_466 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _145_466))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1043 stack -> (match (_53_1043) with
| (a, aq) -> begin
(let _145_473 = (let _145_472 = (let _145_471 = (let _145_470 = (let _145_469 = (FStar_Util.mk_ref None)
in (env, a, _145_469, false))
in Clos (_145_470))
in (_145_471, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_145_472))
in (_145_473)::stack)
end)) args))
in (

let _53_1047 = (log cfg (fun _53_1046 -> (match (()) with
| () -> begin
(let _145_475 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _145_475))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine (((

let _53_1057 = x
in {FStar_Syntax_Syntax.ppname = _53_1057.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1057.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1061 -> begin
(let _145_476 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_476))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1065 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_53_1065) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _145_479 = (let _145_478 = (let _145_477 = (FStar_Syntax_Subst.close closing f)
in ((

let _53_1067 = x
in {FStar_Syntax_Syntax.ppname = _53_1067.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1067.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _145_477))
in FStar_Syntax_Syntax.Tm_refine (_145_478))
in (mk _145_479 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _145_480 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_480))
end else begin
(

let _53_1076 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1076) with
| (bs, c) -> begin
(

let c = (let _145_483 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1078 -> (Dummy)::env) env))
in (norm_comp cfg _145_483 c))
in (

let t = (let _145_484 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _145_484 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1106 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1109 = (log cfg (fun _53_1108 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _145_486 = (norm cfg env [] t)
in FStar_Util.Inl (_145_486))
end
| FStar_Util.Inr (c) -> begin
(let _145_487 = (norm_comp cfg env c)
in FStar_Util.Inr (_145_487))
end)
in (let _145_488 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, tc, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_488)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env = (let _145_491 = (let _145_490 = (let _145_489 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _145_489, false))
in Clos (_145_490))
in (_145_491)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1130, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1142); FStar_Syntax_Syntax.lbunivs = _53_1140; FStar_Syntax_Syntax.lbtyp = _53_1138; FStar_Syntax_Syntax.lbeff = _53_1136; FStar_Syntax_Syntax.lbdef = _53_1134})::_53_1132), _53_1148) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1174 = (FStar_List.fold_right (fun lb _53_1163 -> (match (_53_1163) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _145_494 = (

let _53_1164 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1164.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1164.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _145_494))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos ((env, fix_f_i, memo, true)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_53_1174) with
| (rec_env, memos, _53_1173) -> begin
(

let _53_1177 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _145_501 = (let _145_500 = (let _145_499 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _145_499, false))
in Clos (_145_500))
in (_145_501)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_1189)::_53_1187 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1194) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _53_1201 -> begin
(norm cfg env stack head)
end)
end
| _53_1203 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _145_502 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_145_502))
end
| _53_1208 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1216 -> (match (_53_1216) with
| (a, imp) -> begin
(let _145_507 = (norm cfg env [] a)
in (_145_507, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _53_1223 = comp
in (let _145_512 = (let _145_511 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_145_511))
in {FStar_Syntax_Syntax.n = _145_512; FStar_Syntax_Syntax.tk = _53_1223.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1223.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1223.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _53_1227 = comp
in (let _145_514 = (let _145_513 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_145_513))
in {FStar_Syntax_Syntax.n = _145_514; FStar_Syntax_Syntax.tk = _53_1227.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1227.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1227.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1235 -> (match (_53_1235) with
| (a, i) -> begin
(let _145_518 = (norm cfg env [] a)
in (_145_518, i))
end)))))
in (

let _53_1236 = comp
in (let _145_522 = (let _145_521 = (

let _53_1238 = ct
in (let _145_520 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _145_519 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1238.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_520; FStar_Syntax_Syntax.effect_args = _145_519; FStar_Syntax_Syntax.flags = _53_1238.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_145_521))
in {FStar_Syntax_Syntax.n = _145_522; FStar_Syntax_Syntax.tk = _53_1236.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1236.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1236.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1245 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]; tcenv = _53_1245.tcenv; delta_level = _53_1245.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _145_530 = (norm t)
in (FStar_Syntax_Util.non_informative _145_530)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1250) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(

let _53_1254 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_1254.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1254.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1254.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1261 = ct
in {FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1261.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1261.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1261.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1265 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1265.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1265.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1265.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1268 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1268.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1268.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1268.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1271 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1276 -> (match (_53_1276) with
| (x, imp) -> begin
(let _145_535 = (

let _53_1277 = x
in (let _145_534 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1277.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1277.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_534}))
in (_145_535, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1290 = (FStar_List.fold_left (fun _53_1284 b -> (match (_53_1284) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_53_1290) with
| (nbs, _53_1289) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _145_546 = (let _145_545 = (let _145_544 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _145_544))
in FStar_Util.Inl (_145_545))
in Some (_145_546))
end else begin
(let _145_549 = (let _145_548 = (let _145_547 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _145_547))
in FStar_Util.Inl (_145_548))
in Some (_145_549))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1299 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1316 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _145_554 = (

let _53_1329 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1329.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1329.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1329.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _145_554))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1365), aq, r))::stack -> begin
(

let _53_1374 = (log cfg (fun _53_1373 -> (match (()) with
| () -> begin
(let _145_556 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _145_556))
end)))
in if (FStar_List.contains (Exclude (Iota)) cfg.steps) then begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(

let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1384, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _145_557 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _145_557)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1405 = (log cfg (fun _53_1404 -> (match (()) with
| () -> begin
(let _145_559 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _145_559))
end)))
in (

let norm_and_rebuild_match = (fun _53_1408 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1410 = cfg
in (let _145_562 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1410.tcenv; delta_level = _145_562}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1418 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1423 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1423) with
| (p, wopt, e) -> begin
(

let env = (let _145_570 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _145_570 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_571 = (norm_or_whnf env w)
in Some (_145_571))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _145_572 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _145_572))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1437) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1462 -> begin
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

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun t p -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_1479 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1479) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1485) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1502) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1509 -> begin
(let _145_589 = (not ((is_cons head)))
in FStar_Util.Inr (_145_589))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _145_590 = (FStar_Syntax_Util.un_uinst head)
in _145_590.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1517 -> begin
(let _145_591 = (not ((is_cons head)))
in FStar_Util.Inr (_145_591))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1527))::rest_a, ((p, _53_1533))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1541 -> begin
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

let _53_1559 = (log cfg (fun _53_1558 -> (match (()) with
| () -> begin
(let _145_602 = (FStar_Syntax_Print.pat_to_string p)
in (let _145_601 = (let _145_600 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _145_600 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _145_602 _145_601)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _145_607 = (let _145_606 = (let _145_605 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _145_605, false))
in Clos (_145_606))
in (_145_607)::env)) env s)
in (let _145_608 = (guard_when_clause wopt b rest)
in (norm cfg env stack _145_608))))
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
| _53_1570 -> begin
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


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _145_620 = (config s e)
in (norm _145_620 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _145_627 = (config s e)
in (norm_comp _145_627 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _145_632 = (config [] env)
in (norm_universe _145_632 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _145_637 = (config [] env)
in (ghost_to_pure_aux _145_637 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _145_644 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _145_644)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1592 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1592.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1592.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1594 -> (match (()) with
| () -> begin
(let _145_646 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _145_646))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _145_651 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _145_651)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _145_657 = (let _145_656 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _145_656 [] c))
in (FStar_Syntax_Print.comp_to_string _145_657)))


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
(let _145_668 = (let _145_667 = (let _145_666 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _145_666))
in FStar_Syntax_Syntax.Tm_refine (_145_667))
in (mk _145_668 t0.FStar_Syntax_Syntax.pos))
end
| _53_1617 -> begin
t
end))
end
| _53_1619 -> begin
t
end)))
in (aux t))))


let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _53_1620 _53_1622 _53_1624 -> (FStar_All.failwith "NYI: normalize_sigelt"))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _53_1626 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let _53_1633 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_53_1633) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1636 -> begin
(

let _53_1639 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1639) with
| (binders, args) -> begin
(let _145_683 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _145_682 = (let _145_681 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_679 -> FStar_Util.Inl (_145_679)))
in (FStar_All.pipe_right _145_681 (fun _145_680 -> Some (_145_680))))
in (FStar_Syntax_Util.abs binders _145_683 _145_682)))
end))
end)
end))
end
| _53_1641 -> begin
(let _145_686 = (let _145_685 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_684 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _145_685 _145_684)))
in (FStar_All.failwith _145_686))
end))





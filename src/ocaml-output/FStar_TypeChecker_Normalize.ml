
open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
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


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_63) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _145_199 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _145_199 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_70, _53_72) -> begin
(closure_to_string c)
end
| MemoLazy (_53_76) -> begin
"MemoLazy"
end
| Abs (_53_79, bs, _53_82, _53_84, _53_86) -> begin
(let _145_202 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _145_202))
end
| _53_90 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _145_205 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _145_205 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_97 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_104 -> begin
(let _145_221 = (let _145_220 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _145_220))
in (FStar_All.failwith _145_221))
end)


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _145_226 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _145_226 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_117 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_117) with
| (binders, cdef) -> begin
(

let inst = (let _145_230 = (let _145_229 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_145_229)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_121 _53_125 -> (match (((_53_121), (_53_125))) with
| ((x, _53_120), (t, _53_124)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _145_230))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _53_128 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_128.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_128.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_128.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
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

let _53_150 = (FStar_List.fold_left (fun _53_141 u -> (match (_53_141) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_145 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_145) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_150) with
| (_53_147, u, out) -> begin
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
| _53_167 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_160 -> begin
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
(let _145_247 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _145_247 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _145_249 = (aux u)
in (FStar_List.map (fun _145_248 -> FStar_Syntax_Syntax.U_succ (_145_248)) _145_249))
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

let _53_198 = (log cfg (fun _53_197 -> (match (()) with
| () -> begin
(let _145_273 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_272 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _145_273 _145_272)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_202 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_205) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_218) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _145_278 = (let _145_277 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_145_277))
in (mk _145_278 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _145_279 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _145_279))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_229) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_236) -> begin
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

let _53_252 = (closures_as_binders_delayed cfg env bs)
in (match (_53_252) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _145_282 = (let _145_281 = (let _145_280 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_145_280)))
in FStar_Syntax_Syntax.Tm_abs (_145_281))
in (mk _145_282 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_260 = (closures_as_binders_delayed cfg env bs)
in (match (_53_260) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_268 = (let _145_284 = (let _145_283 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_283)::[])
in (closures_as_binders_delayed cfg env _145_284))
in (match (_53_268) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _145_288 = (let _145_287 = (let _145_286 = (let _145_285 = (FStar_List.hd x)
in (FStar_All.pipe_right _145_285 Prims.fst))
in ((_145_286), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_145_287))
in (mk _145_288 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _145_294 = (let _145_293 = (let _145_292 = (closure_as_term_delayed cfg env t1)
in (let _145_291 = (let _145_290 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _145_289 -> FStar_Util.Inl (_145_289)) _145_290))
in ((_145_292), (_145_291), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_145_293))
in (mk _145_294 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _145_300 = (let _145_299 = (let _145_298 = (closure_as_term_delayed cfg env t1)
in (let _145_297 = (let _145_296 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _145_295 -> FStar_Util.Inr (_145_295)) _145_296))
in ((_145_298), (_145_297), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_145_299))
in (mk _145_300 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _145_305 = (let _145_304 = (let _145_303 = (closure_as_term_delayed cfg env t')
in (let _145_302 = (let _145_301 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_145_301))
in ((_145_303), (_145_302))))
in FStar_Syntax_Syntax.Tm_meta (_145_304))
in (mk _145_305 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _145_311 = (let _145_310 = (let _145_309 = (closure_as_term_delayed cfg env t')
in (let _145_308 = (let _145_307 = (let _145_306 = (closure_as_term_delayed cfg env tbody)
in ((m), (_145_306)))
in FStar_Syntax_Syntax.Meta_monadic (_145_307))
in ((_145_309), (_145_308))))
in FStar_Syntax_Syntax.Tm_meta (_145_310))
in (mk _145_311 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _145_314 = (let _145_313 = (let _145_312 = (closure_as_term_delayed cfg env t')
in ((_145_312), (m)))
in FStar_Syntax_Syntax.Tm_meta (_145_313))
in (mk _145_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_307 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_313) -> begin
body
end
| FStar_Util.Inl (_53_316) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_319 = lb
in {FStar_Syntax_Syntax.lbname = _53_319.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_319.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_319.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_323, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_332 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_336 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_340 = lb
in (let _145_326 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _145_325 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_340.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_340.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _145_326; FStar_Syntax_Syntax.lbeff = _53_340.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _145_325}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_343 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_358 -> (match (_53_358) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_363) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_373 = (norm_pat env hd)
in (match (_53_373) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _145_338 = (norm_pat env p)
in (Prims.fst _145_338)))))
in (((

let _53_376 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_376.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_376.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_393 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_384 _53_387 -> (match (((_53_384), (_53_387))) with
| ((pats, env), (p, b)) -> begin
(

let _53_390 = (norm_pat env p)
in (match (_53_390) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_393) with
| (pats, env) -> begin
(((

let _53_394 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_394.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_394.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_398 = x
in (let _145_341 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_398.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_398.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_341}))
in (((

let _53_401 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_401.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_401.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_405 = x
in (let _145_342 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_405.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_405.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_342}))
in (((

let _53_408 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_408.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_408.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_414 = x
in (let _145_343 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_414.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_414.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_343}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_418 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_418.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_418.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_422 = (norm_pat env pat)
in (match (_53_422) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_344 = (closure_as_term cfg env w)
in Some (_145_344))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _145_347 = (let _145_346 = (let _145_345 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_145_345)))
in FStar_Syntax_Syntax.Tm_match (_145_346))
in (mk _145_347 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_433 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_439 -> begin
(FStar_List.map (fun _53_442 -> (match (_53_442) with
| (x, imp) -> begin
(let _145_355 = (closure_as_term_delayed cfg env x)
in ((_145_355), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_458 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_448 _53_451 -> (match (((_53_448), (_53_451))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_452 = b
in (let _145_361 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_452.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_452.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_361}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_458) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_464 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _145_365 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _145_365))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _145_366 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _145_366))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _145_368 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_145_368))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let _53_478 = c
in {FStar_Syntax_Syntax.effect_name = _53_478.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
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
| _53_487 -> begin
lopt
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_492 = t
in {FStar_Syntax_Syntax.n = _53_492.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_492.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_492.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_501 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
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
| _53_579 -> begin
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
| _53_622 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_649))::((_53_640, (arg, _53_643)))::[] -> begin
arg
end
| _53_653 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_657))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_663))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_667 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _145_382 = (FStar_Syntax_Subst.compress t)
in _145_382.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_685)::[], body, _53_689) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_697 -> begin
tm
end)
end
| _53_699 -> begin
tm
end)
end
| _53_701 -> begin
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
| _53_703 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_710 = (log cfg (fun _53_709 -> (match (()) with
| () -> begin
(let _145_415 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_414 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _145_415 _145_414)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_713) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_755; FStar_Syntax_Syntax.pos = _53_753; FStar_Syntax_Syntax.vars = _53_751}, (a1)::(a2)::rest) -> begin
(

let _53_769 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_769) with
| (hd, _53_768) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_777; FStar_Syntax_Syntax.pos = _53_775; FStar_Syntax_Syntax.vars = _53_773}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_788 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_788) with
| (reify_head, _53_787) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _145_419 = (FStar_Syntax_Subst.compress e)
in _145_419.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_808 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_808) with
| (_53_806, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _145_424 = (let _145_423 = (let _145_422 = (let _145_420 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_420)::[])
in (let _145_421 = (FStar_Syntax_Util.mk_reify body)
in ((_145_422), (_145_421), (None))))
in FStar_Syntax_Syntax.Tm_abs (_145_423))
in (FStar_Syntax_Syntax.mk _145_424 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _145_438 = (let _145_437 = (let _145_436 = (let _145_435 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _145_434 = (let _145_433 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _145_432 = (let _145_431 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_430 = (let _145_429 = (FStar_Syntax_Syntax.as_arg head)
in (let _145_428 = (let _145_427 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_426 = (let _145_425 = (FStar_Syntax_Syntax.as_arg body)
in (_145_425)::[])
in (_145_427)::_145_426))
in (_145_429)::_145_428))
in (_145_431)::_145_430))
in (_145_433)::_145_432))
in (_145_435)::_145_434))
in ((bind_repr), (_145_436)))
in FStar_Syntax_Syntax.Tm_app (_145_437))
in (FStar_Syntax_Syntax.mk _145_438 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_815) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_818) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_821 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_830)); FStar_Syntax_Syntax.tk = _53_828; FStar_Syntax_Syntax.pos = _53_826; FStar_Syntax_Syntax.vars = _53_824}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_846 -> (match (_53_846) with
| (pat, wopt, tm) -> begin
(let _145_440 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_145_440)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_850 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _145_441 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_441)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _145_443 = (let _145_442 = (FStar_List.map (norm_universe cfg env) us)
in ((_145_442), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_145_443))
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

let _53_875 = (log cfg (fun _53_874 -> (match (()) with
| () -> begin
(let _145_446 = (FStar_Syntax_Print.term_to_string t0)
in (let _145_445 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _145_446 _145_445)))
end)))
in (

let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| (UnivArgs (us', _53_881))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_889 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_891 -> begin
(let _145_450 = (let _145_449 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _145_449))
in (FStar_All.failwith _145_450))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_895) -> begin
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

let _53_909 = (log cfg (fun _53_908 -> (match (()) with
| () -> begin
(let _145_453 = (FStar_Syntax_Print.term_to_string t)
in (let _145_452 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _145_453 _145_452)))
end)))
in (match ((let _145_454 = (FStar_Syntax_Subst.compress t')
in _145_454.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_912) -> begin
(norm cfg env stack t')
end
| _53_915 -> begin
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
| (Meta (_53_925))::_53_923 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_931))::_53_929 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_937))::_53_935 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_943, _53_945))::stack_rest -> begin
(match (c) with
| Univ (_53_950) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_953 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_956)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_960 = (log cfg (fun _53_959 -> (match (()) with
| () -> begin
(let _145_456 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_456))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_966 = (log cfg (fun _53_965 -> (match (()) with
| () -> begin
(let _145_458 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_458))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_972 = (log cfg (fun _53_971 -> (match (()) with
| () -> begin
(let _145_460 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_460))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_975 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_977 -> begin
(

let cfg = (

let _53_978 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_978.tcenv; delta_level = _53_978.delta_level})
in (let _145_461 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_461)))
end)
end
| (_53_983)::tl -> begin
(

let _53_986 = (log cfg (fun _53_985 -> (match (()) with
| () -> begin
(let _145_463 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_463))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (MemoLazy (r))::stack -> begin
(

let _53_993 = (set_memo r ((env), (t)))
in (

let _53_996 = (log cfg (fun _53_995 -> (match (()) with
| () -> begin
(let _145_465 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _145_465))
end)))
in (norm cfg env stack t)))
end
| ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _145_466 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_466))
end else begin
(

let _53_1020 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1020) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _145_472 = (let _145_470 = (let _145_468 = (let _145_467 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _145_467))
in (FStar_All.pipe_right _145_468 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _145_470 (fun _145_469 -> FStar_Util.Inl (_145_469))))
in (FStar_All.pipe_right _145_472 (fun _145_471 -> Some (_145_471))))
end
| _53_1025 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1028 -> (Dummy)::env) env))
in (

let _53_1032 = (log cfg (fun _53_1031 -> (match (()) with
| () -> begin
(let _145_476 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _145_476))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1040 stack -> (match (_53_1040) with
| (a, aq) -> begin
(let _145_483 = (let _145_482 = (let _145_481 = (let _145_480 = (let _145_479 = (FStar_Util.mk_ref None)
in ((env), (a), (_145_479), (false)))
in Clos (_145_480))
in ((_145_481), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_145_482))
in (_145_483)::stack)
end)) args))
in (

let _53_1044 = (log cfg (fun _53_1043 -> (match (()) with
| () -> begin
(let _145_485 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _145_485))
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

let _53_1054 = x
in {FStar_Syntax_Syntax.ppname = _53_1054.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1054.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1058 -> begin
(let _145_486 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_486))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1062 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1062) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _145_489 = (let _145_488 = (let _145_487 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1064 = x
in {FStar_Syntax_Syntax.ppname = _53_1064.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1064.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_145_487)))
in FStar_Syntax_Syntax.Tm_refine (_145_488))
in (mk _145_489 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _145_490 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_490))
end else begin
(

let _53_1073 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1073) with
| (bs, c) -> begin
(

let c = (let _145_493 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1075 -> (Dummy)::env) env))
in (norm_comp cfg _145_493 c))
in (

let t = (let _145_494 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _145_494 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1103 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1106 = (log cfg (fun _53_1105 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _145_496 = (norm cfg env [] t)
in FStar_Util.Inl (_145_496))
end
| FStar_Util.Inr (c) -> begin
(let _145_497 = (norm_comp cfg env c)
in FStar_Util.Inr (_145_497))
end)
in (let _145_498 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_498)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1119, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1131); FStar_Syntax_Syntax.lbunivs = _53_1129; FStar_Syntax_Syntax.lbtyp = _53_1127; FStar_Syntax_Syntax.lbeff = _53_1125; FStar_Syntax_Syntax.lbdef = _53_1123})::_53_1121), _53_1137) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _145_501 = (let _145_500 = (let _145_499 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_145_499), (false)))
in Clos (_145_500))
in (_145_501)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1151 = (let _145_504 = (let _145_503 = (let _145_502 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _145_502 FStar_Syntax_Syntax.mk_binder))
in (_145_503)::[])
in (FStar_Syntax_Subst.open_term _145_504 body))
in (match (_53_1151) with
| (bs, body) -> begin
(

let lb = (

let _53_1152 = lb
in (let _145_510 = (let _145_507 = (let _145_505 = (FStar_List.hd bs)
in (FStar_All.pipe_right _145_505 Prims.fst))
in (FStar_All.pipe_right _145_507 (fun _145_506 -> FStar_Util.Inl (_145_506))))
in (let _145_509 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _145_508 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _145_510; FStar_Syntax_Syntax.lbunivs = _53_1152.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _145_509; FStar_Syntax_Syntax.lbeff = _53_1152.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _145_508}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1156 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _145_513 = (closure_as_term cfg env t)
in (rebuild cfg env stack _145_513))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1182 = (FStar_List.fold_right (fun lb _53_1171 -> (match (_53_1171) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _145_516 = (

let _53_1172 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1172.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _145_516))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + 1)))))))
end)) (Prims.snd lbs) ((env), ([]), (0)))
in (match (_53_1182) with
| (rec_env, memos, _53_1181) -> begin
(

let _53_1185 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _145_523 = (let _145_522 = (let _145_521 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_145_521), (false)))
in Clos (_145_522))
in (_145_523)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_1197)::_53_1195 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1202) -> begin
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
| _53_1214 -> begin
(norm cfg env stack head)
end)
end
| _53_1216 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _145_524 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_145_524))
end
| _53_1221 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1229 -> (match (_53_1229) with
| (a, imp) -> begin
(let _145_529 = (norm cfg env [] a)
in ((_145_529), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _53_1236 = comp
in (let _145_534 = (let _145_533 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_145_533))
in {FStar_Syntax_Syntax.n = _145_534; FStar_Syntax_Syntax.tk = _53_1236.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1236.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1236.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _53_1240 = comp
in (let _145_536 = (let _145_535 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_145_535))
in {FStar_Syntax_Syntax.n = _145_536; FStar_Syntax_Syntax.tk = _53_1240.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1240.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1240.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1248 -> (match (_53_1248) with
| (a, i) -> begin
(let _145_540 = (norm cfg env [] a)
in ((_145_540), (i)))
end)))))
in (

let _53_1249 = comp
in (let _145_544 = (let _145_543 = (

let _53_1251 = ct
in (let _145_542 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _145_541 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1251.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_542; FStar_Syntax_Syntax.effect_args = _145_541; FStar_Syntax_Syntax.flags = _53_1251.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_145_543))
in {FStar_Syntax_Syntax.n = _145_544; FStar_Syntax_Syntax.tk = _53_1249.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1249.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1249.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1258 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1258.tcenv; delta_level = _53_1258.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _145_552 = (norm t)
in (FStar_Syntax_Util.non_informative _145_552)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1263) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(

let _53_1267 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_1267.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1267.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1267.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1274 = ct
in {FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1274.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1274.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1274.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1278 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1278.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1278.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1278.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1281 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1281.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1281.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1281.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1284 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1289 -> (match (_53_1289) with
| (x, imp) -> begin
(let _145_557 = (

let _53_1290 = x
in (let _145_556 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_556}))
in ((_145_557), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1303 = (FStar_List.fold_left (fun _53_1297 b -> (match (_53_1297) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1303) with
| (nbs, _53_1302) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _145_568 = (let _145_567 = (let _145_566 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _145_566))
in FStar_Util.Inl (_145_567))
in Some (_145_568))
end else begin
(let _145_571 = (let _145_570 = (let _145_569 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _145_569))
in FStar_Util.Inl (_145_570))
in Some (_145_571))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1312 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1329 = (set_memo r ((env), (t)))
in (

let _53_1332 = (log cfg (fun _53_1331 -> (match (()) with
| () -> begin
(let _145_577 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _145_577))
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
in (let _145_578 = (

let _53_1355 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1355.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1355.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1355.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _145_578))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1391), aq, r))::stack -> begin
(

let _53_1400 = (log cfg (fun _53_1399 -> (match (()) with
| () -> begin
(let _145_580 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _145_580))
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
| Some (_53_1410, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _145_581 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _145_581)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1431 = (log cfg (fun _53_1430 -> (match (()) with
| () -> begin
(let _145_583 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _145_583))
end)))
in (

let norm_and_rebuild_match = (fun _53_1434 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1436 = cfg
in (let _145_586 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1436.tcenv; delta_level = _145_586}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1446) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1456 = (norm_pat env hd)
in (match (_53_1456) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _145_596 = (norm_pat env p)
in (Prims.fst _145_596)))))
in (((

let _53_1459 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1459.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1459.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1476 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1467 _53_1470 -> (match (((_53_1467), (_53_1470))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1473 = (norm_pat env p)
in (match (_53_1473) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1476) with
| (pats, env) -> begin
(((

let _53_1477 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1477.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1477.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1481 = x
in (let _145_599 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_599}))
in (((

let _53_1484 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1484.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1484.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1488 = x
in (let _145_600 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1488.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1488.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_600}))
in (((

let _53_1491 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1491.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1491.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1497 = x
in (let _145_601 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1497.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1497.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_601}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1501 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1501.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1501.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1505 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1510 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1510) with
| (p, wopt, e) -> begin
(

let _53_1513 = (norm_pat env p)
in (match (_53_1513) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_603 = (norm_or_whnf env w)
in Some (_145_603))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _145_604 = (mk (FStar_Syntax_Syntax.Tm_match (((t), (branches)))) r)
in (rebuild cfg env stack _145_604)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1524) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1549 -> begin
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

let _53_1566 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1566) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1572) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1589) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1596 -> begin
(let _145_621 = (not ((is_cons head)))
in FStar_Util.Inr (_145_621))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _145_622 = (FStar_Syntax_Util.un_uinst head)
in _145_622.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1604 -> begin
(let _145_623 = (not ((is_cons head)))
in FStar_Util.Inr (_145_623))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1614))::rest_a, ((p, _53_1620))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1628 -> begin
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

let _53_1646 = (log cfg (fun _53_1645 -> (match (()) with
| () -> begin
(let _145_634 = (FStar_Syntax_Print.pat_to_string p)
in (let _145_633 = (let _145_632 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _145_632 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _145_634 _145_633)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _145_639 = (let _145_638 = (let _145_637 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_145_637), (false)))
in Clos (_145_638))
in (_145_639)::env)) env s)
in (let _145_640 = (guard_when_clause wopt b rest)
in (norm cfg env stack _145_640))))
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
| _53_1657 -> begin
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


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _145_652 = (config s e)
in (norm _145_652 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _145_659 = (config s e)
in (norm_comp _145_659 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _145_664 = (config [] env)
in (norm_universe _145_664 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _145_669 = (config [] env)
in (ghost_to_pure_aux _145_669 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _145_676 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _145_676)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1679 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1679.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1679.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1681 -> (match (()) with
| () -> begin
(let _145_678 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _145_678))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _145_683 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _145_683)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _145_689 = (let _145_688 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _145_688 [] c))
in (FStar_Syntax_Print.comp_to_string _145_689)))


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
(let _145_700 = (let _145_699 = (let _145_698 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_145_698)))
in FStar_Syntax_Syntax.Tm_refine (_145_699))
in (mk _145_700 t0.FStar_Syntax_Syntax.pos))
end
| _53_1704 -> begin
t
end))
end
| _53_1706 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1713 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1713) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1716 -> begin
(

let _53_1719 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1719) with
| (binders, args) -> begin
(let _145_711 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _145_710 = (let _145_709 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_707 -> FStar_Util.Inl (_145_707)))
in (FStar_All.pipe_right _145_709 (fun _145_708 -> Some (_145_708))))
in (FStar_Syntax_Util.abs binders _145_711 _145_710)))
end))
end)
end)))
in (match ((let _145_712 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_145_712), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1723) -> begin
(let _145_713 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _145_713))
end
| (_53_1726, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1731 -> begin
(

let _53_1734 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1734) with
| (head, args) -> begin
(match ((let _145_714 = (FStar_Syntax_Subst.compress head)
in _145_714.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1736, thead) -> begin
(

let _53_1742 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1742) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1750 = (env.FStar_TypeChecker_Env.type_of (

let _53_1743 = env
in {FStar_TypeChecker_Env.solver = _53_1743.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1743.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1743.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1743.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1743.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1743.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1743.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1743.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1743.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1743.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1743.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1743.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1743.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1743.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1743.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1743.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1743.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1743.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1743.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) t)
in (match (_53_1750) with
| (_53_1746, ty, _53_1749) -> begin
(expand ty)
end))
end
end))
end
| _53_1752 -> begin
(

let _53_1760 = (env.FStar_TypeChecker_Env.type_of (

let _53_1753 = env
in {FStar_TypeChecker_Env.solver = _53_1753.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1753.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1753.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1753.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1753.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1753.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1753.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1753.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1753.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1753.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1753.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1753.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1753.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1753.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1753.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1753.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1753.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1753.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1753.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true}) t)
in (match (_53_1760) with
| (_53_1756, ty, _53_1759) -> begin
(expand ty)
end))
end)
end))
end)))





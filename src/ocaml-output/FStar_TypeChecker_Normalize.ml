
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


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _147_241 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _147_241 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_120 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_120) with
| (binders, cdef) -> begin
(

let inst = (let _147_245 = (let _147_244 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_244)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_124 _53_128 -> (match (((_53_124), (_53_128))) with
| ((x, _53_123), (t, _53_127)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _147_245))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _53_131 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_131.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_131.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_131.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
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

let _53_153 = (FStar_List.fold_left (fun _53_144 u -> (match (_53_144) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_148 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_148) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_153) with
| (_53_150, u, out) -> begin
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
| _53_170 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_163 -> begin
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

let us = (let _147_262 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_262 norm_univs))
in (match (us) with
| (u_k)::rest -> begin
(match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_194 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_194) with
| (_53_192, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_196 -> begin
us
end)
end
| _53_198 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_265 = (aux u)
in (FStar_List.map (fun _147_264 -> FStar_Syntax_Syntax.U_succ (_147_264)) _147_265))
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

let _53_217 = (log cfg (fun _53_216 -> (match (()) with
| () -> begin
(let _147_289 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_288 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _147_289 _147_288)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_221 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_224) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_237) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_294 = (let _147_293 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_293))
in (mk _147_294 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_295 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_295))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_248) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_255) -> begin
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

let _53_271 = (closures_as_binders_delayed cfg env bs)
in (match (_53_271) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _147_298 = (let _147_297 = (let _147_296 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_147_296)))
in FStar_Syntax_Syntax.Tm_abs (_147_297))
in (mk _147_298 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _53_279 = (closures_as_binders_delayed cfg env bs)
in (match (_53_279) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_287 = (let _147_300 = (let _147_299 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_299)::[])
in (closures_as_binders_delayed cfg env _147_300))
in (match (_53_287) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _147_304 = (let _147_303 = (let _147_302 = (let _147_301 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_301 Prims.fst))
in ((_147_302), (phi)))
in FStar_Syntax_Syntax.Tm_refine (_147_303))
in (mk _147_304 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _147_310 = (let _147_309 = (let _147_308 = (closure_as_term_delayed cfg env t1)
in (let _147_307 = (let _147_306 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _147_305 -> FStar_Util.Inl (_147_305)) _147_306))
in ((_147_308), (_147_307), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_309))
in (mk _147_310 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _147_316 = (let _147_315 = (let _147_314 = (closure_as_term_delayed cfg env t1)
in (let _147_313 = (let _147_312 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _147_311 -> FStar_Util.Inr (_147_311)) _147_312))
in ((_147_314), (_147_313), (lopt))))
in FStar_Syntax_Syntax.Tm_ascribed (_147_315))
in (mk _147_316 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _147_321 = (let _147_320 = (let _147_319 = (closure_as_term_delayed cfg env t')
in (let _147_318 = (let _147_317 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_147_317))
in ((_147_319), (_147_318))))
in FStar_Syntax_Syntax.Tm_meta (_147_320))
in (mk _147_321 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _147_327 = (let _147_326 = (let _147_325 = (closure_as_term_delayed cfg env t')
in (let _147_324 = (let _147_323 = (let _147_322 = (closure_as_term_delayed cfg env tbody)
in ((m), (_147_322)))
in FStar_Syntax_Syntax.Meta_monadic (_147_323))
in ((_147_325), (_147_324))))
in FStar_Syntax_Syntax.Tm_meta (_147_326))
in (mk _147_327 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_330 = (let _147_329 = (let _147_328 = (closure_as_term_delayed cfg env t')
in ((_147_328), (m)))
in FStar_Syntax_Syntax.Tm_meta (_147_329))
in (mk _147_330 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _53_326 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_332) -> begin
body
end
| FStar_Util.Inl (_53_335) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_338 = lb
in {FStar_Syntax_Syntax.lbname = _53_338.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_338.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_338.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_342, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_351 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_355 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_359 = lb
in (let _147_342 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_341 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_359.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_359.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_342; FStar_Syntax_Syntax.lbeff = _53_359.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_341}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_362 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_377 -> (match (_53_377) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_382) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_392 = (norm_pat env hd)
in (match (_53_392) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_354 = (norm_pat env p)
in (Prims.fst _147_354)))))
in (((

let _53_395 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_395.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_395.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_412 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_403 _53_406 -> (match (((_53_403), (_53_406))) with
| ((pats, env), (p, b)) -> begin
(

let _53_409 = (norm_pat env p)
in (match (_53_409) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_412) with
| (pats, env) -> begin
(((

let _53_413 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_413.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_413.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_417 = x
in (let _147_357 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_357}))
in (((

let _53_420 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_420.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_420.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_424 = x
in (let _147_358 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_424.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_424.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_358}))
in (((

let _53_427 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_427.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_427.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_433 = x
in (let _147_359 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_359}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_437 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_437.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_437.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_441 = (norm_pat env pat)
in (match (_53_441) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_360 = (closure_as_term cfg env w)
in Some (_147_360))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _147_363 = (let _147_362 = (let _147_361 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_147_361)))
in FStar_Syntax_Syntax.Tm_match (_147_362))
in (mk _147_363 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_452 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_458 -> begin
(FStar_List.map (fun _53_461 -> (match (_53_461) with
| (x, imp) -> begin
(let _147_371 = (closure_as_term_delayed cfg env x)
in ((_147_371), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_477 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_467 _53_470 -> (match (((_53_467), (_53_470))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_471 = b
in (let _147_377 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_471.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_471.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_377}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_477) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_483 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _147_381 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _147_381))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _147_382 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _147_382))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_384 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_384))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let _53_497 = c
in {FStar_Syntax_Syntax.effect_name = _53_497.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
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
| _53_506 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _147_397 = (let _147_396 = (FStar_Util.string_of_int i)
in ((_147_396), (None)))
in FStar_Const.Const_int (_147_397)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]))


let reduce_primops = (fun steps tm -> (

let arith_op = (fun fv -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_538 -> (match (_53_538) with
| (l, _53_537) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) arith_ops)
end
| _53_540 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_548))::((a2, _53_544))::[]) -> begin
(match ((arith_op fv)) with
| None -> begin
tm
end
| Some (_53_555, op) -> begin
(match ((let _147_579 = (let _147_576 = (FStar_Syntax_Subst.compress a1)
in _147_576.FStar_Syntax_Syntax.n)
in (let _147_578 = (let _147_577 = (FStar_Syntax_Subst.compress a2)
in _147_577.FStar_Syntax_Syntax.n)
in ((_147_579), (_147_578))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(

let c = (let _147_581 = (FStar_Util.int_of_string i)
in (let _147_580 = (FStar_Util.int_of_string j)
in (op _147_581 _147_580)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos))
end
| _53_572 -> begin
tm
end)
end)
end
| _53_574 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_579 = t
in {FStar_Syntax_Syntax.n = _53_579.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_579.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_579.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_588 -> begin
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
| _53_666 -> begin
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
| _53_709 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_736))::((_53_727, (arg, _53_730)))::[] -> begin
arg
end
| _53_740 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_744))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_750))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_754 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _147_592 = (FStar_Syntax_Subst.compress t)
in _147_592.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_772)::[], body, _53_776) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_784 -> begin
tm
end)
end
| _53_786 -> begin
tm
end)
end
| _53_788 -> begin
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
| _53_790 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_797 = (log cfg (fun _53_796 -> (match (()) with
| () -> begin
(let _147_625 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_624 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_625 _147_624)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_800) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_842; FStar_Syntax_Syntax.pos = _53_840; FStar_Syntax_Syntax.vars = _53_838}, ((tm, _53_848))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_854 = cfg
in {steps = s; tcenv = _53_854.tcenv; delta_level = FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)})
in (

let stack' = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_863; FStar_Syntax_Syntax.pos = _53_861; FStar_Syntax_Syntax.vars = _53_859}, (a1)::(a2)::rest) -> begin
(

let _53_877 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_877) with
| (hd, _53_876) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_885; FStar_Syntax_Syntax.pos = _53_883; FStar_Syntax_Syntax.vars = _53_881}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_896 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_896) with
| (reify_head, _53_895) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _147_629 = (FStar_Syntax_Subst.compress e)
in _147_629.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_916 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_916) with
| (_53_914, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _147_634 = (let _147_633 = (let _147_632 = (let _147_630 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_630)::[])
in (let _147_631 = (FStar_Syntax_Util.mk_reify body)
in ((_147_632), (_147_631), (None))))
in FStar_Syntax_Syntax.Tm_abs (_147_633))
in (FStar_Syntax_Syntax.mk _147_634 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _147_648 = (let _147_647 = (let _147_646 = (let _147_645 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_644 = (let _147_643 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _147_642 = (let _147_641 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_640 = (let _147_639 = (FStar_Syntax_Syntax.as_arg head)
in (let _147_638 = (let _147_637 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_636 = (let _147_635 = (FStar_Syntax_Syntax.as_arg body)
in (_147_635)::[])
in (_147_637)::_147_636))
in (_147_639)::_147_638))
in (_147_641)::_147_640))
in (_147_643)::_147_642))
in (_147_645)::_147_644))
in ((bind_repr), (_147_646)))
in FStar_Syntax_Syntax.Tm_app (_147_647))
in (FStar_Syntax_Syntax.mk _147_648 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_923) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_926) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_929 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_938)); FStar_Syntax_Syntax.tk = _53_936; FStar_Syntax_Syntax.pos = _53_934; FStar_Syntax_Syntax.vars = _53_932}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_954 -> (match (_53_954) with
| (pat, wopt, tm) -> begin
(let _147_650 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_147_650)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_958 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _147_651 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_651)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _147_653 = (let _147_652 = (FStar_List.map (norm_universe cfg env) us)
in ((_147_652), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_147_653))
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

let _53_983 = (log cfg (fun _53_982 -> (match (()) with
| () -> begin
(let _147_656 = (FStar_Syntax_Print.term_to_string t0)
in (let _147_655 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _147_656 _147_655)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_989))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_997 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_999 -> begin
(let _147_660 = (let _147_659 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_659))
in (FStar_All.failwith _147_660))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1003) -> begin
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

let _53_1017 = (log cfg (fun _53_1016 -> (match (()) with
| () -> begin
(let _147_663 = (FStar_Syntax_Print.term_to_string t)
in (let _147_662 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_663 _147_662)))
end)))
in (match ((let _147_664 = (FStar_Syntax_Subst.compress t')
in _147_664.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1020) -> begin
(norm cfg env stack t')
end
| _53_1023 -> begin
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
| (Meta (_53_1033))::_53_1031 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_1039))::_53_1037 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1045))::_53_1043 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1051, _53_1053))::stack_rest -> begin
(match (c) with
| Univ (_53_1058) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1061 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1064)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1068 = (log cfg (fun _53_1067 -> (match (()) with
| () -> begin
(let _147_666 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_666))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1074 = (log cfg (fun _53_1073 -> (match (()) with
| () -> begin
(let _147_668 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_668))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1080 = (log cfg (fun _53_1079 -> (match (()) with
| () -> begin
(let _147_670 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_670))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1083 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1085 -> begin
(

let cfg = (

let _53_1086 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1086.tcenv; delta_level = _53_1086.delta_level})
in (let _147_671 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_671)))
end)
end
| (_53_1091)::tl -> begin
(

let _53_1094 = (log cfg (fun _53_1093 -> (match (()) with
| () -> begin
(let _147_673 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_673))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1103 = cfg
in {steps = s; tcenv = _53_1103.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1109 = (set_memo r ((env), (t)))
in (

let _53_1112 = (log cfg (fun _53_1111 -> (match (()) with
| () -> begin
(let _147_675 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_675))
end)))
in (norm cfg env stack t)))
end
| ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_676 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_676))
end else begin
(

let _53_1136 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1136) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _147_682 = (let _147_680 = (let _147_678 = (let _147_677 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _147_677))
in (FStar_All.pipe_right _147_678 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_680 (fun _147_679 -> FStar_Util.Inl (_147_679))))
in (FStar_All.pipe_right _147_682 (fun _147_681 -> Some (_147_681))))
end
| _53_1141 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1144 -> (Dummy)::env) env))
in (

let _53_1148 = (log cfg (fun _53_1147 -> (match (()) with
| () -> begin
(let _147_686 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_686))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1156 stack -> (match (_53_1156) with
| (a, aq) -> begin
(let _147_693 = (let _147_692 = (let _147_691 = (let _147_690 = (let _147_689 = (FStar_Util.mk_ref None)
in ((env), (a), (_147_689), (false)))
in Clos (_147_690))
in ((_147_691), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_147_692))
in (_147_693)::stack)
end)) args))
in (

let _53_1160 = (log cfg (fun _53_1159 -> (match (()) with
| () -> begin
(let _147_695 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_695))
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

let _53_1170 = x
in {FStar_Syntax_Syntax.ppname = _53_1170.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1170.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1174 -> begin
(let _147_696 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_696))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1178 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1178) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _147_699 = (let _147_698 = (let _147_697 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1180 = x
in {FStar_Syntax_Syntax.ppname = _53_1180.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1180.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_147_697)))
in FStar_Syntax_Syntax.Tm_refine (_147_698))
in (mk _147_699 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_700 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_700))
end else begin
(

let _53_1189 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1189) with
| (bs, c) -> begin
(

let c = (let _147_703 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1191 -> (Dummy)::env) env))
in (norm_comp cfg _147_703 c))
in (

let t = (let _147_704 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_704 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1219 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1222 = (log cfg (fun _53_1221 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _147_706 = (norm cfg env [] t)
in FStar_Util.Inl (_147_706))
end
| FStar_Util.Inr (c) -> begin
(let _147_707 = (norm_comp cfg env c)
in FStar_Util.Inr (_147_707))
end)
in (let _147_708 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_708)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1235, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1247); FStar_Syntax_Syntax.lbunivs = _53_1245; FStar_Syntax_Syntax.lbtyp = _53_1243; FStar_Syntax_Syntax.lbeff = _53_1241; FStar_Syntax_Syntax.lbdef = _53_1239})::_53_1237), _53_1253) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _147_711 = (let _147_710 = (let _147_709 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_147_709), (false)))
in Clos (_147_710))
in (_147_711)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1267 = (let _147_714 = (let _147_713 = (let _147_712 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _147_712 FStar_Syntax_Syntax.mk_binder))
in (_147_713)::[])
in (FStar_Syntax_Subst.open_term _147_714 body))
in (match (_53_1267) with
| (bs, body) -> begin
(

let lb = (

let _53_1268 = lb
in (let _147_720 = (let _147_717 = (let _147_715 = (FStar_List.hd bs)
in (FStar_All.pipe_right _147_715 Prims.fst))
in (FStar_All.pipe_right _147_717 (fun _147_716 -> FStar_Util.Inl (_147_716))))
in (let _147_719 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_718 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _147_720; FStar_Syntax_Syntax.lbunivs = _53_1268.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_719; FStar_Syntax_Syntax.lbeff = _53_1268.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_718}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1272 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _147_723 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_723))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1298 = (FStar_List.fold_right (fun lb _53_1287 -> (match (_53_1287) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _147_726 = (

let _53_1288 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1288.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1288.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_726))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1298) with
| (rec_env, memos, _53_1297) -> begin
(

let _53_1301 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _147_733 = (let _147_732 = (let _147_731 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_147_731), (false)))
in Clos (_147_732))
in (_147_733)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_1313)::_53_1311 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1318) -> begin
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
| _53_1330 -> begin
(norm cfg env stack head)
end)
end
| _53_1332 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_734 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_734))
end
| _53_1337 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1345 -> (match (_53_1345) with
| (a, imp) -> begin
(let _147_739 = (norm cfg env [] a)
in ((_147_739), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _53_1352 = comp
in (let _147_744 = (let _147_743 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_147_743))
in {FStar_Syntax_Syntax.n = _147_744; FStar_Syntax_Syntax.tk = _53_1352.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1352.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1352.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _53_1356 = comp
in (let _147_746 = (let _147_745 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_147_745))
in {FStar_Syntax_Syntax.n = _147_746; FStar_Syntax_Syntax.tk = _53_1356.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1356.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1356.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1364 -> (match (_53_1364) with
| (a, i) -> begin
(let _147_750 = (norm cfg env [] a)
in ((_147_750), (i)))
end)))))
in (

let _53_1365 = comp
in (let _147_754 = (let _147_753 = (

let _53_1367 = ct
in (let _147_752 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_751 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1367.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_752; FStar_Syntax_Syntax.effect_args = _147_751; FStar_Syntax_Syntax.flags = _53_1367.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_147_753))
in {FStar_Syntax_Syntax.n = _147_754; FStar_Syntax_Syntax.tk = _53_1365.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1365.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1365.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1374 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1374.tcenv; delta_level = _53_1374.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _147_762 = (norm t)
in (FStar_Syntax_Util.non_informative _147_762)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1379) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(

let _53_1383 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_1383.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1383.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1383.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1390 = ct
in {FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1390.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1390.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1390.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1394 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1394.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1394.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1394.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1397 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1397.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1397.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1397.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1400 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1405 -> (match (_53_1405) with
| (x, imp) -> begin
(let _147_767 = (

let _53_1406 = x
in (let _147_766 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1406.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1406.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_766}))
in ((_147_767), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1419 = (FStar_List.fold_left (fun _53_1413 b -> (match (_53_1413) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1419) with
| (nbs, _53_1418) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _147_778 = (let _147_777 = (let _147_776 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _147_776))
in FStar_Util.Inl (_147_777))
in Some (_147_778))
end else begin
(let _147_781 = (let _147_780 = (let _147_779 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _147_779))
in FStar_Util.Inl (_147_780))
in Some (_147_781))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1428 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1440 = cfg
in {steps = s; tcenv = _53_1440.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1453 = (set_memo r ((env), (t)))
in (

let _53_1456 = (log cfg (fun _53_1455 -> (match (()) with
| () -> begin
(let _147_787 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_787))
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
in (let _147_788 = (

let _53_1479 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1479.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1479.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1479.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_788))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1515), aq, r))::stack -> begin
(

let _53_1524 = (log cfg (fun _53_1523 -> (match (()) with
| () -> begin
(let _147_790 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_790))
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
| Some (_53_1534, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _147_791 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_791)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1555 = (log cfg (fun _53_1554 -> (match (()) with
| () -> begin
(let _147_793 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _147_793))
end)))
in (

let norm_and_rebuild_match = (fun _53_1558 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1560 = cfg
in (let _147_796 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1560.tcenv; delta_level = _147_796}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1570) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1580 = (norm_pat env hd)
in (match (_53_1580) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_806 = (norm_pat env p)
in (Prims.fst _147_806)))))
in (((

let _53_1583 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1583.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1583.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1600 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1591 _53_1594 -> (match (((_53_1591), (_53_1594))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1597 = (norm_pat env p)
in (match (_53_1597) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1600) with
| (pats, env) -> begin
(((

let _53_1601 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1601.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1601.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1605 = x
in (let _147_809 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1605.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1605.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_809}))
in (((

let _53_1608 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1608.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1608.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1612 = x
in (let _147_810 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1612.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1612.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_810}))
in (((

let _53_1615 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1615.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1615.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1621 = x
in (let _147_811 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1621.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1621.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_811}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1625 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1625.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1625.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1629 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1634 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1634) with
| (p, wopt, e) -> begin
(

let _53_1637 = (norm_pat env p)
in (match (_53_1637) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_813 = (norm_or_whnf env w)
in Some (_147_813))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _147_814 = (mk (FStar_Syntax_Syntax.Tm_match (((t), (branches)))) r)
in (rebuild cfg env stack _147_814)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1648) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1673 -> begin
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

let _53_1690 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1690) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1696) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1713) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1720 -> begin
(let _147_831 = (not ((is_cons head)))
in FStar_Util.Inr (_147_831))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _147_832 = (FStar_Syntax_Util.un_uinst head)
in _147_832.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1728 -> begin
(let _147_833 = (not ((is_cons head)))
in FStar_Util.Inr (_147_833))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1738))::rest_a, ((p, _53_1744))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1752 -> begin
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

let _53_1770 = (log cfg (fun _53_1769 -> (match (()) with
| () -> begin
(let _147_844 = (FStar_Syntax_Print.pat_to_string p)
in (let _147_843 = (let _147_842 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _147_842 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _147_844 _147_843)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _147_849 = (let _147_848 = (let _147_847 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_147_847), (false)))
in Clos (_147_848))
in (_147_849)::env)) env s)
in (let _147_850 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_850))))
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
| _53_1781 -> begin
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


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_862 = (config s e)
in (norm _147_862 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_869 = (config s e)
in (norm_comp _147_869 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_874 = (config [] env)
in (norm_universe _147_874 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_879 = (config [] env)
in (ghost_to_pure_aux _147_879 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _147_886 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _147_886)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1803 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1803.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1803.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1805 -> (match (()) with
| () -> begin
(let _147_888 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _147_888))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_893 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_893)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_899 = (let _147_898 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_898 [] c))
in (FStar_Syntax_Print.comp_to_string _147_899)))


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
(let _147_910 = (let _147_909 = (let _147_908 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_147_908)))
in FStar_Syntax_Syntax.Tm_refine (_147_909))
in (mk _147_910 t0.FStar_Syntax_Syntax.pos))
end
| _53_1828 -> begin
t
end))
end
| _53_1830 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1837 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1837) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1840 -> begin
(

let _53_1843 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1843) with
| (binders, args) -> begin
(let _147_921 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_920 = (let _147_919 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_917 -> FStar_Util.Inl (_147_917)))
in (FStar_All.pipe_right _147_919 (fun _147_918 -> Some (_147_918))))
in (FStar_Syntax_Util.abs binders _147_921 _147_920)))
end))
end)
end)))
in (match ((let _147_922 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_147_922), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1847) -> begin
(let _147_923 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _147_923))
end
| (_53_1850, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1855 -> begin
(

let _53_1858 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1858) with
| (head, args) -> begin
(match ((let _147_924 = (FStar_Syntax_Subst.compress head)
in _147_924.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1860, thead) -> begin
(

let _53_1866 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1866) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1874 = (env.FStar_TypeChecker_Env.type_of (

let _53_1867 = env
in {FStar_TypeChecker_Env.solver = _53_1867.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1867.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1867.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1867.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1867.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1867.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1867.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1867.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1867.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1867.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1867.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1867.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1867.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1867.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1867.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1867.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1867.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1867.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1867.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1867.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1874) with
| (_53_1870, ty, _53_1873) -> begin
(expand ty)
end))
end
end))
end
| _53_1876 -> begin
(

let _53_1884 = (env.FStar_TypeChecker_Env.type_of (

let _53_1877 = env
in {FStar_TypeChecker_Env.solver = _53_1877.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1877.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1877.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1877.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1877.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1877.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1877.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1877.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1877.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1877.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1877.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1877.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1877.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1877.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1877.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1877.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1877.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _53_1877.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1877.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1877.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1884) with
| (_53_1880, ty, _53_1883) -> begin
(expand ty)
end))
end)
end))
end)))





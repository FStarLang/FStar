
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


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_215 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_215 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_73, _53_75) -> begin
(closure_to_string c)
end
| MemoLazy (_53_79) -> begin
"MemoLazy"
end
| Abs (_53_82, bs, _53_85, _53_87, _53_89) -> begin
(let _147_218 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_218))
end
| _53_93 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_221 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_221 (FStar_String.concat "; "))))


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
(let _147_237 = (let _147_236 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_236))
in (FStar_All.failwith _147_237))
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
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_135 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_135) with
| (binders, cdef) -> begin
(

let _53_136 = if ((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1"))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Effect constructor is not fully applied"), (comp.FStar_Syntax_Syntax.pos)))))
end else begin
()
end
in (

let inst = (let _147_249 = (let _147_248 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_248)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_141 _53_145 -> (match (((_53_141), (_53_145))) with
| ((x, _53_140), (t, _53_144)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _147_249))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _147_250 = (

let _53_148 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = _53_148.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = _53_148.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_148.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_148.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _147_250 FStar_Syntax_Syntax.mk_Comp))
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

let _53_170 = (FStar_List.fold_left (fun _53_161 u -> (match (_53_161) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_165 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_165) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_170) with
| (_53_167, u, out) -> begin
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
| _53_187 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_180 -> begin
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
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (match ((FStar_Syntax_Util.univ_kernel u_k)) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
if (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let _53_214 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_214) with
| (_53_212, m) -> begin
(n <= m)
end))))) then begin
rest
end else begin
us
end
end
| _53_216 -> begin
us
end))
end
| _53_218 -> begin
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

let _53_237 = (log cfg (fun _53_236 -> (match (()) with
| () -> begin
(let _147_294 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_293 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _147_294 _147_293)))
end)))
in (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| _53_241 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_244) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (_53_257) -> begin
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
| Univ (_53_268) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, _53_275) -> begin
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

let _53_291 = (closures_as_binders_delayed cfg env bs)
in (match (_53_291) with
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

let _53_299 = (closures_as_binders_delayed cfg env bs)
in (match (_53_299) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _53_307 = (let _147_305 = (let _147_304 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_304)::[])
in (closures_as_binders_delayed cfg env _147_305))
in (match (_53_307) with
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

let env = (FStar_List.fold_left (fun env _53_346 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_352) -> begin
body
end
| FStar_Util.Inl (_53_355) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _53_358 = lb
in {FStar_Syntax_Syntax.lbname = _53_358.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_358.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_358.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_362, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _53_371 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_375 env -> (Dummy)::env) lbs env_univs)
end
in (

let _53_379 = lb
in (let _147_347 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_346 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_379.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_379.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_347; FStar_Syntax_Syntax.lbeff = _53_379.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_346}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _53_382 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _53_397 -> (match (_53_397) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_402) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_412 = (norm_pat env hd)
in (match (_53_412) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_359 = (norm_pat env p)
in (Prims.fst _147_359)))))
in (((

let _53_415 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_415.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_415.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_432 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_423 _53_426 -> (match (((_53_423), (_53_426))) with
| ((pats, env), (p, b)) -> begin
(

let _53_429 = (norm_pat env p)
in (match (_53_429) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_432) with
| (pats, env) -> begin
(((

let _53_433 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_433.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_433.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_437 = x
in (let _147_362 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_437.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_437.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_362}))
in (((

let _53_440 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_440.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_440.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_444 = x
in (let _147_363 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_444.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_444.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_363}))
in (((

let _53_447 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_447.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_447.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_453 = x
in (let _147_364 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_453.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_453.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_364}))
in (

let t = (closure_as_term cfg env t)
in (((

let _53_457 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_457.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_457.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let _53_461 = (norm_pat env pat)
in (match (_53_461) with
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
| _53_472 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| _53_478 -> begin
(FStar_List.map (fun _53_481 -> (match (_53_481) with
| (x, imp) -> begin
(let _147_376 = (closure_as_term_delayed cfg env x)
in ((_147_376), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _53_497 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_487 _53_490 -> (match (((_53_487), (_53_490))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _53_491 = b
in (let _147_382 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_382}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (_53_497) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| _53_503 -> begin
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

let _53_521 = c
in (let _147_392 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _147_392; FStar_Syntax_Syntax.effect_name = _53_521.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))
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
| _53_530 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> (let _147_406 = (let _147_405 = (FStar_Util.string_of_int i)
in ((_147_405), (None)))
in FStar_Const.Const_int (_147_406)))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _147_602 = (let _147_601 = (FStar_List.map (fun m -> (let _147_600 = (let _147_569 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_147_569), ((fun x y -> (int_as_const (x + y))))))
in (let _147_599 = (let _147_598 = (let _147_580 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_147_580), ((fun x y -> (int_as_const (x - y))))))
in (let _147_597 = (let _147_596 = (let _147_591 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_147_591), ((fun x y -> (int_as_const (x * y))))))
in (_147_596)::[])
in (_147_598)::_147_597))
in (_147_600)::_147_599))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[]))
in (FStar_List.flatten _147_601))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _147_602))))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let arith_op = (fun fv -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun _53_569 -> (match (_53_569) with
| (l, _53_568) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) arith_ops)
end
| _53_571 -> begin
None
end))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, _53_579))::((a2, _53_575))::[]) -> begin
(match ((arith_op fv)) with
| None -> begin
tm
end
| Some (_53_586, op) -> begin
(

let norm = (fun i j -> (

let c = (let _147_659 = (FStar_Util.int_of_string i)
in (let _147_658 = (FStar_Util.int_of_string j)
in (op _147_659 _147_658)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (match ((let _147_663 = (let _147_660 = (FStar_Syntax_Subst.compress a1)
in _147_660.FStar_Syntax_Syntax.n)
in (let _147_662 = (let _147_661 = (FStar_Syntax_Subst.compress a2)
in _147_661.FStar_Syntax_Syntax.n)
in ((_147_663), (_147_662))))) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, _53_597))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, _53_605))::[])) -> begin
(match ((let _147_671 = (let _147_664 = (FStar_Syntax_Subst.compress head1)
in _147_664.FStar_Syntax_Syntax.n)
in (let _147_670 = (let _147_665 = (FStar_Syntax_Subst.compress head2)
in _147_665.FStar_Syntax_Syntax.n)
in (let _147_669 = (let _147_666 = (FStar_Syntax_Subst.compress arg1)
in _147_666.FStar_Syntax_Syntax.n)
in (let _147_668 = (let _147_667 = (FStar_Syntax_Subst.compress arg2)
in _147_667.FStar_Syntax_Syntax.n)
in ((_147_671), (_147_670), (_147_669), (_147_668))))))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _147_675 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _147_674 = (let _147_673 = (let _147_672 = (norm i j)
in ((_147_672), (None)))
in (_147_673)::[])
in (FStar_Syntax_Util.mk_app _147_675 _147_674)))
end
| _53_627 -> begin
tm
end)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| _53_640 -> begin
tm
end))
end)
end
| _53_642 -> begin
tm
end)
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_647 = t
in {FStar_Syntax_Syntax.n = _53_647.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_647.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_647.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_656 -> begin
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
| _53_734 -> begin
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
| _53_777 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_804))::((_53_795, (arg, _53_798)))::[] -> begin
arg
end
| _53_808 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_812))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_818))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_822 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _147_686 = (FStar_Syntax_Subst.compress t)
in _147_686.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_840)::[], body, _53_844) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_852 -> begin
tm
end)
end
| _53_854 -> begin
tm
end)
end
| _53_856 -> begin
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
| _53_858 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_865 = (log cfg (fun _53_864 -> (match (()) with
| () -> begin
(let _147_719 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_718 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_719 _147_718)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_868) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _53_910; FStar_Syntax_Syntax.pos = _53_908; FStar_Syntax_Syntax.vars = _53_906}, ((tm, _53_916))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let s = (Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let _53_922 = cfg
in {steps = s; tcenv = _53_922.tcenv; delta_level = FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant)})
in (

let stack' = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_931; FStar_Syntax_Syntax.pos = _53_929; FStar_Syntax_Syntax.vars = _53_927}, (a1)::(a2)::rest) -> begin
(

let _53_945 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_945) with
| (hd, _53_944) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_953; FStar_Syntax_Syntax.pos = _53_951; FStar_Syntax_Syntax.vars = _53_949}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_964 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_964) with
| (reify_head, _53_963) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m, t_body)) -> begin
(match ((let _147_723 = (FStar_Syntax_Subst.compress e)
in _147_723.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_984 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_984) with
| (_53_982, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _147_728 = (let _147_727 = (let _147_726 = (let _147_724 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_724)::[])
in (let _147_725 = (FStar_Syntax_Util.mk_reify body)
in ((_147_726), (_147_725), (None))))
in FStar_Syntax_Syntax.Tm_abs (_147_727))
in (FStar_Syntax_Syntax.mk _147_728 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _147_742 = (let _147_741 = (let _147_740 = (let _147_739 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_738 = (let _147_737 = (FStar_Syntax_Syntax.as_arg t_body)
in (let _147_736 = (let _147_735 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_734 = (let _147_733 = (FStar_Syntax_Syntax.as_arg head)
in (let _147_732 = (let _147_731 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _147_730 = (let _147_729 = (FStar_Syntax_Syntax.as_arg body)
in (_147_729)::[])
in (_147_731)::_147_730))
in (_147_733)::_147_732))
in (_147_735)::_147_734))
in (_147_737)::_147_736))
in (_147_739)::_147_738))
in ((bind_repr), (_147_740)))
in FStar_Syntax_Syntax.Tm_app (_147_741))
in (FStar_Syntax_Syntax.mk _147_742 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_991) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_994) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_997 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_1006)); FStar_Syntax_Syntax.tk = _53_1004; FStar_Syntax_Syntax.pos = _53_1002; FStar_Syntax_Syntax.vars = _53_1000}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_1022 -> (match (_53_1022) with
| (pat, wopt, tm) -> begin
(let _147_744 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_147_744)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_1026 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _147_745 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_745)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _147_747 = (let _147_746 = (FStar_List.map (norm_universe cfg env) us)
in ((_147_746), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_147_747))
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

let _53_1051 = (log cfg (fun _53_1050 -> (match (()) with
| () -> begin
(let _147_750 = (FStar_Syntax_Print.term_to_string t0)
in (let _147_749 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _147_750 _147_749)))
end)))
in (

let n = (FStar_List.length us)
in if (n > (Prims.parse_int "0")) then begin
(match (stack) with
| (UnivArgs (us', _53_1057))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_1065 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_1067 -> begin
(let _147_754 = (let _147_753 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_753))
in (FStar_All.failwith _147_754))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_1071) -> begin
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

let _53_1085 = (log cfg (fun _53_1084 -> (match (()) with
| () -> begin
(let _147_757 = (FStar_Syntax_Print.term_to_string t)
in (let _147_756 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_757 _147_756)))
end)))
in (match ((let _147_758 = (FStar_Syntax_Subst.compress t')
in _147_758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_1088) -> begin
(norm cfg env stack t')
end
| _53_1091 -> begin
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
| (UnivArgs (_53_1101))::_53_1099 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_1107))::_53_1105 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_1113, _53_1115))::stack_rest -> begin
(match (c) with
| Univ (_53_1120) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| _53_1123 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_1126)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_1130 = (log cfg (fun _53_1129 -> (match (()) with
| () -> begin
(let _147_760 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_760))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_1136 = (log cfg (fun _53_1135 -> (match (()) with
| () -> begin
(let _147_762 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_762))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_1142 = (log cfg (fun _53_1141 -> (match (()) with
| () -> begin
(let _147_764 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_764))
end)))
in (norm cfg ((c)::env) stack_rest body))
end
| _53_1145 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| _53_1147 -> begin
(

let cfg = (

let _53_1148 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1148.tcenv; delta_level = _53_1148.delta_level})
in (let _147_765 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_765)))
end)
end
| (_53_1153)::tl -> begin
(

let _53_1156 = (log cfg (fun _53_1155 -> (match (()) with
| () -> begin
(let _147_767 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_767))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body)))
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let _53_1165 = cfg
in {steps = s; tcenv = _53_1165.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
(

let _53_1171 = (set_memo r ((env), (t)))
in (

let _53_1174 = (log cfg (fun _53_1173 -> (match (()) with
| () -> begin
(let _147_769 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_769))
end)))
in (norm cfg env stack t)))
end
| ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_770 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_770))
end else begin
(

let _53_1204 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_1204) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _147_776 = (let _147_774 = (let _147_772 = (let _147_771 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _147_771))
in (FStar_All.pipe_right _147_772 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _147_774 (fun _147_773 -> FStar_Util.Inl (_147_773))))
in (FStar_All.pipe_right _147_776 (fun _147_775 -> Some (_147_775))))
end
| _53_1209 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1212 -> (Dummy)::env) env))
in (

let _53_1216 = (log cfg (fun _53_1215 -> (match (()) with
| () -> begin
(let _147_780 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_780))
end)))
in (norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_1224 stack -> (match (_53_1224) with
| (a, aq) -> begin
(let _147_787 = (let _147_786 = (let _147_785 = (let _147_784 = (let _147_783 = (FStar_Util.mk_ref None)
in ((env), (a), (_147_783), (false)))
in Clos (_147_784))
in ((_147_785), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_147_786))
in (_147_787)::stack)
end)) args))
in (

let _53_1228 = (log cfg (fun _53_1227 -> (match (()) with
| () -> begin
(let _147_789 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_789))
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

let _53_1238 = x
in {FStar_Syntax_Syntax.ppname = _53_1238.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1238.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_1242 -> begin
(let _147_790 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_790))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _53_1246 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_53_1246) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _147_793 = (let _147_792 = (let _147_791 = (FStar_Syntax_Subst.close closing f)
in (((

let _53_1248 = x
in {FStar_Syntax_Syntax.ppname = _53_1248.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1248.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_147_791)))
in FStar_Syntax_Syntax.Tm_refine (_147_792))
in (mk _147_793 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_794 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_794))
end else begin
(

let _53_1257 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_1257) with
| (bs, c) -> begin
(

let c = (let _147_797 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1259 -> (Dummy)::env) env))
in (norm_comp cfg _147_797 c))
in (

let t = (let _147_798 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_798 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_1287 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_1290 = (log cfg (fun _53_1289 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _147_800 = (norm cfg env [] t)
in FStar_Util.Inl (_147_800))
end
| FStar_Util.Inr (c) -> begin
(let _147_801 = (norm_comp cfg env c)
in FStar_Util.Inr (_147_801))
end)
in (let _147_802 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_802)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1303, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1315); FStar_Syntax_Syntax.lbunivs = _53_1313; FStar_Syntax_Syntax.lbtyp = _53_1311; FStar_Syntax_Syntax.lbeff = _53_1309; FStar_Syntax_Syntax.lbdef = _53_1307})::_53_1305), _53_1321) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline)))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _147_805 = (let _147_804 = (let _147_803 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_147_803), (false)))
in Clos (_147_804))
in (_147_805)::env)
in (norm cfg env stack body))
end else begin
(

let _53_1335 = (let _147_808 = (let _147_807 = (let _147_806 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _147_806 FStar_Syntax_Syntax.mk_binder))
in (_147_807)::[])
in (FStar_Syntax_Subst.open_term _147_808 body))
in (match (_53_1335) with
| (bs, body) -> begin
(

let lb = (

let _53_1336 = lb
in (let _147_814 = (let _147_811 = (let _147_809 = (FStar_List.hd bs)
in (FStar_All.pipe_right _147_809 Prims.fst))
in (FStar_All.pipe_right _147_811 (fun _147_810 -> FStar_Util.Inl (_147_810))))
in (let _147_813 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_812 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _147_814; FStar_Syntax_Syntax.lbunivs = _53_1336.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_813; FStar_Syntax_Syntax.lbeff = _53_1336.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_812}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_1340 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _147_817 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_817))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_1366 = (FStar_List.fold_right (fun lb _53_1355 -> (match (_53_1355) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _147_820 = (

let _53_1356 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1356.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1356.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_820))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (_53_1366) with
| (rec_env, memos, _53_1365) -> begin
(

let _53_1369 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _147_827 = (let _147_826 = (let _147_825 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_147_825), (false)))
in Clos (_147_826))
in (_147_827)::env)) (Prims.snd lbs) env)
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

let _53_1384 = cfg
in {steps = (FStar_List.append ((NoInline)::(Exclude (Zeta))::[]) cfg.steps); tcenv = _53_1384.tcenv; delta_level = FStar_TypeChecker_Env.NoDelta})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m') -> begin
if (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))) then begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let _53_1392 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = _53_1392.tcenv; delta_level = FStar_TypeChecker_Env.OnlyInline})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end else begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m')))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end
end
| _53_1396 -> begin
(match (stack) with
| (_53_1400)::_53_1398 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1405) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| _53_1412 -> begin
(norm cfg env stack head)
end)
end
| _53_1414 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_828 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_828))
end
| _53_1419 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1427 -> (match (_53_1427) with
| (a, imp) -> begin
(let _147_833 = (norm cfg env [] a)
in ((_147_833), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let _53_1436 = comp
in (let _147_840 = (let _147_839 = (let _147_838 = (norm cfg env [] t)
in (let _147_837 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_838), (_147_837))))
in FStar_Syntax_Syntax.Total (_147_839))
in {FStar_Syntax_Syntax.n = _147_840; FStar_Syntax_Syntax.tk = _53_1436.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1436.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1436.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let _53_1442 = comp
in (let _147_844 = (let _147_843 = (let _147_842 = (norm cfg env [] t)
in (let _147_841 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_147_842), (_147_841))))
in FStar_Syntax_Syntax.GTotal (_147_843))
in {FStar_Syntax_Syntax.n = _147_844; FStar_Syntax_Syntax.tk = _53_1442.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1442.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1442.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1450 -> (match (_53_1450) with
| (a, i) -> begin
(let _147_848 = (norm cfg env [] a)
in ((_147_848), (i)))
end)))))
in (

let _53_1451 = comp
in (let _147_853 = (let _147_852 = (

let _53_1453 = ct
in (let _147_851 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _147_850 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_849 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _147_851; FStar_Syntax_Syntax.effect_name = _53_1453.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_850; FStar_Syntax_Syntax.effect_args = _147_849; FStar_Syntax_Syntax.flags = _53_1453.FStar_Syntax_Syntax.flags}))))
in FStar_Syntax_Syntax.Comp (_147_852))
in {FStar_Syntax_Syntax.n = _147_853; FStar_Syntax_Syntax.tk = _53_1451.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1451.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1451.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_1460 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = _53_1460.tcenv; delta_level = _53_1460.delta_level}) env [] t))
in (

let non_info = (fun t -> (let _147_861 = (norm t)
in (FStar_Syntax_Util.non_informative _147_861)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1465) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let _53_1471 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = _53_1471.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1471.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1471.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_1478 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1478.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_1478.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1478.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1478.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_1482 = ct
in {FStar_Syntax_Syntax.comp_univs = _53_1482.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1482.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1482.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1482.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_1485 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1485.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1485.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1485.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1488 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1493 -> (match (_53_1493) with
| (x, imp) -> begin
(let _147_866 = (

let _53_1494 = x
in (let _147_865 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1494.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1494.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_865}))
in ((_147_866), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _53_1507 = (FStar_List.fold_left (fun _53_1501 b -> (match (_53_1501) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (_53_1507) with
| (nbs, _53_1506) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _147_877 = (let _147_876 = (let _147_875 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _147_875))
in FStar_Util.Inl (_147_876))
in Some (_147_877))
end else begin
(let _147_880 = (let _147_879 = (let _147_878 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _147_878))
in FStar_Util.Inl (_147_879))
in Some (_147_880))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1516 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let _53_1528 = cfg
in {steps = s; tcenv = _53_1528.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
(

let _53_1541 = (set_memo r ((env), (t)))
in (

let _53_1544 = (log cfg (fun _53_1543 -> (match (()) with
| () -> begin
(let _147_886 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _147_886))
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
in (let _147_887 = (

let _53_1567 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1567.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1567.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1567.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_887))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1603), aq, r))::stack -> begin
(

let _53_1612 = (log cfg (fun _53_1611 -> (match (()) with
| () -> begin
(let _147_889 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_889))
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
| Some (_53_1622, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _147_890 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_890)))
end
| (Match (env, branches, r))::stack -> begin
(

let _53_1643 = (log cfg (fun _53_1642 -> (match (()) with
| () -> begin
(let _147_892 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _147_892))
end)))
in (

let scrutinee = t
in (

let norm_and_rebuild_match = (fun _53_1647 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1649 = cfg
in (let _147_895 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1649.tcenv; delta_level = _147_895}))
in (

let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1659) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1669 = (norm_pat env hd)
in (match (_53_1669) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_905 = (norm_pat env p)
in (Prims.fst _147_905)))))
in (((

let _53_1672 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1672.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1672.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1689 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1680 _53_1683 -> (match (((_53_1680), (_53_1683))) with
| ((pats, env), (p, b)) -> begin
(

let _53_1686 = (norm_pat env p)
in (match (_53_1686) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (_53_1689) with
| (pats, env) -> begin
(((

let _53_1690 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1690.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1690.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1694 = x
in (let _147_908 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1694.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1694.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_908}))
in (((

let _53_1697 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1697.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1697.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1701 = x
in (let _147_909 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1701.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1701.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_909}))
in (((

let _53_1704 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1704.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1704.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1710 = x
in (let _147_910 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1710.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1710.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_910}))
in (

let t = (norm_or_whnf env t)
in (((

let _53_1714 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1714.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1714.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1718 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1723 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1723) with
| (p, wopt, e) -> begin
(

let _53_1726 = (norm_pat env p)
in (match (_53_1726) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_912 = (norm_or_whnf env w)
in Some (_147_912))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _147_913 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _147_913)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1737) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1762 -> begin
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

let _53_1779 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (_53_1779) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (_53_1785) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1802) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1809 -> begin
(let _147_930 = (not ((is_cons head)))
in FStar_Util.Inr (_147_930))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _147_931 = (FStar_Syntax_Util.un_uinst head)
in _147_931.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1817 -> begin
(let _147_932 = (not ((is_cons head)))
in FStar_Util.Inr (_147_932))
end)
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1827))::rest_a, ((p, _53_1833))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1841 -> begin
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

let _53_1859 = (log cfg (fun _53_1858 -> (match (()) with
| () -> begin
(let _147_943 = (FStar_Syntax_Print.pat_to_string p)
in (let _147_942 = (let _147_941 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _147_941 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _147_943 _147_942)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _147_948 = (let _147_947 = (let _147_946 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_147_946), (false)))
in Clos (_147_947))
in (_147_948)::env)) env s)
in (let _147_949 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_949))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches scrutinee branches)
end)))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (match ((FStar_Util.find_map s (fun _53_5 -> (match (_53_5) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1870 -> begin
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


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_961 = (config s e)
in (norm _147_961 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_968 = (config s e)
in (norm_comp _147_968 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_973 = (config [] env)
in (norm_universe _147_973 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _147_978 = (config [] env)
in (ghost_to_pure_aux _147_978 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _147_985 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _147_985)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1892 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1892.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1892.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1894 -> (match (()) with
| () -> begin
(let _147_987 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _147_987))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_992 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_992)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_998 = (let _147_997 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_997 [] c))
in (FStar_Syntax_Print.comp_to_string _147_998)))


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
(let _147_1009 = (let _147_1008 = (let _147_1007 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_147_1007)))
in FStar_Syntax_Syntax.Tm_refine (_147_1008))
in (mk _147_1009 t0.FStar_Syntax_Syntax.pos))
end
| _53_1917 -> begin
t
end))
end
| _53_1919 -> begin
t
end)))
in (aux t))))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let expand = (fun sort -> (

let _53_1926 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1926) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1929 -> begin
(

let _53_1932 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1932) with
| (binders, args) -> begin
(let _147_1020 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_1019 = (let _147_1018 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_1016 -> FStar_Util.Inl (_147_1016)))
in (FStar_All.pipe_right _147_1018 (fun _147_1017 -> Some (_147_1017))))
in (FStar_Syntax_Util.abs binders _147_1020 _147_1019)))
end))
end)
end)))
in (match ((let _147_1021 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_147_1021), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1936) -> begin
(let _147_1022 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _147_1022))
end
| (_53_1939, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1944 -> begin
(

let _53_1947 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1947) with
| (head, args) -> begin
(match ((let _147_1023 = (FStar_Syntax_Subst.compress head)
in _147_1023.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (_53_1949, thead) -> begin
(

let _53_1955 = (FStar_Syntax_Util.arrow_formals thead)
in (match (_53_1955) with
| (formals, tres) -> begin
if ((FStar_List.length formals) = (FStar_List.length args)) then begin
t
end else begin
(

let _53_1963 = (env.FStar_TypeChecker_Env.type_of (

let _53_1956 = env
in {FStar_TypeChecker_Env.solver = _53_1956.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1956.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1956.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1956.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1956.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1956.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1956.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1956.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1956.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1956.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1956.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1956.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1956.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1956.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1956.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1956.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1956.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1956.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1956.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1956.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1956.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1963) with
| (_53_1959, ty, _53_1962) -> begin
(expand ty)
end))
end
end))
end
| _53_1965 -> begin
(

let _53_1973 = (env.FStar_TypeChecker_Env.type_of (

let _53_1966 = env
in {FStar_TypeChecker_Env.solver = _53_1966.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _53_1966.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _53_1966.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _53_1966.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _53_1966.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _53_1966.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = _53_1966.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _53_1966.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _53_1966.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _53_1966.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _53_1966.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _53_1966.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _53_1966.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _53_1966.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _53_1966.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _53_1966.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _53_1966.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _53_1966.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _53_1966.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _53_1966.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = _53_1966.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (_53_1973) with
| (_53_1969, ty, _53_1972) -> begin
(expand ty)
end))
end)
end))
end)))





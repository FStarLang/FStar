
open Prims

type step =
| WHNF
| Inline
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| Beta
| BetaUVars
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| DeltaComp
| SNComp
| Eta
| EtaArgs
| Unmeta
| Unlabel 
 and steps =
step Prims.list


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


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
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


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_64_9) -> begin
_64_9
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo)
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
| Clos (_64_12) -> begin
_64_12
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_64_15) -> begin
_64_15
end))


let closure_to_string : closure  ->  Prims.string = (fun _64_1 -> (match (_64_1) with
| Clos (_64_18, t, _64_21) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _64_25 -> begin
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
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range)
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
| Arg (_64_32) -> begin
_64_32
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_64_35) -> begin
_64_35
end))


let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_64_38) -> begin
_64_38
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_64_41) -> begin
_64_41
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_64_44) -> begin
_64_44
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_64_47) -> begin
_64_47
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_64_50) -> begin
_64_50
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_64_56) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _153_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _153_173 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _64_2 -> (match (_64_2) with
| Arg (c, _64_63, _64_65) -> begin
(closure_to_string c)
end
| MemoLazy (_64_69) -> begin
"MemoLazy"
end
| Abs (_64_72, bs, _64_75, _64_77, _64_79) -> begin
(let _153_176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _153_176))
end
| _64_83 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _153_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _153_179 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _64_3 -> (match (_64_3) with
| [] -> begin
true
end
| _64_90 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _64_97 -> begin
(let _153_195 = (let _153_194 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _153_194))
in (FStar_All.failwith _153_195))
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _64_118 = (FStar_List.fold_left (fun _64_109 u -> (match (_64_109) with
| (cur_kernel, cur_max, out) -> begin
(

let _64_113 = (FStar_Syntax_Util.univ_kernel u)
in (match (_64_113) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_64_118) with
| (_64_115, u, out) -> begin
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
| _64_135 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _64_128 -> begin
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
(let _153_210 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _153_210 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _153_212 = (aux u)
in (FStar_List.map (fun _153_211 -> FStar_Syntax_Syntax.U_succ (_153_211)) _153_212))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | (FStar_Syntax_Syntax.U_zero::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| FStar_Syntax_Syntax.U_zero::u::[] -> begin
u
end
| FStar_Syntax_Syntax.U_zero::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| u::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (

let _64_166 = (log cfg (fun _64_165 -> (match (()) with
| () -> begin
(let _153_236 = (FStar_Syntax_Print.tag_of_term t)
in (let _153_235 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _153_236 _153_235)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _64_170 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_64_173) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _153_242 = (let _153_241 = (let _153_240 = (closure_as_term_delayed cfg env t')
in (u, _153_240))
in FStar_Syntax_Syntax.Tm_uvar (_153_241))
in (mk _153_242 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _153_244 = (let _153_243 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_153_243))
in (mk _153_244 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _153_245 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _153_245))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_64_198) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r) -> begin
(closure_as_term cfg env t0)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (_64_211) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _64_217) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _153_251 = (FStar_List.fold_left (fun env' _64_224 -> (match (_64_224) with
| (t, _64_223) -> begin
(let _153_250 = (let _153_249 = (let _153_248 = (FStar_Util.mk_ref None)
in (env, t, _153_248))
in Clos (_153_249))
in (_153_250)::env')
end)) env args)
in (closure_as_term cfg _153_251 body))
end
| _64_226 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _64_228 -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _64_238 = (closures_as_binders_delayed cfg env bs)
in (match (_64_238) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _153_254 = (let _153_253 = (let _153_252 = (close_lcomp_opt cfg env lopt)
in (bs, body, _153_252))
in FStar_Syntax_Syntax.Tm_abs (_153_253))
in (mk _153_254 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _64_246 = (closures_as_binders_delayed cfg env bs)
in (match (_64_246) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let _64_254 = (let _153_256 = (let _153_255 = (FStar_Syntax_Syntax.mk_binder x)
in (_153_255)::[])
in (closures_as_binders_delayed cfg env _153_256))
in (match (_64_254) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _153_260 = (let _153_259 = (let _153_258 = (let _153_257 = (FStar_List.hd x)
in (FStar_All.pipe_right _153_257 Prims.fst))
in (_153_258, phi))
in FStar_Syntax_Syntax.Tm_refine (_153_259))
in (mk _153_260 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _153_266 = (let _153_265 = (let _153_264 = (closure_as_term_delayed cfg env t1)
in (let _153_263 = (let _153_262 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _153_261 -> FStar_Util.Inl (_153_261)) _153_262))
in (_153_264, _153_263, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_153_265))
in (mk _153_266 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _153_272 = (let _153_271 = (let _153_270 = (closure_as_term_delayed cfg env t1)
in (let _153_269 = (let _153_268 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _153_267 -> FStar_Util.Inr (_153_267)) _153_268))
in (_153_270, _153_269, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_153_271))
in (mk _153_272 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _153_277 = (let _153_276 = (let _153_275 = (closure_as_term_delayed cfg env t')
in (let _153_274 = (let _153_273 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_153_273))
in (_153_275, _153_274)))
in FStar_Syntax_Syntax.Tm_meta (_153_276))
in (mk _153_277 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _153_280 = (let _153_279 = (let _153_278 = (closure_as_term_delayed cfg env t')
in (_153_278, m))
in FStar_Syntax_Syntax.Tm_meta (_153_279))
in (mk _153_280 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env _64_286 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_64_292) -> begin
body
end
| FStar_Util.Inl (_64_295) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let _64_298 = lb
in {FStar_Syntax_Syntax.lbname = _64_298.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _64_298.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _64_298.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_64_302, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun _64_311 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _64_315 env -> (Dummy)::env) lbs env_univs)
end
in (

let _64_319 = lb
in (let _153_292 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _153_291 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _64_319.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _64_319.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _153_292; FStar_Syntax_Syntax.lbeff = _64_319.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _153_291}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun _64_322 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env _64_337 -> (match (_64_337) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_64_342) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(

let _64_352 = (norm_pat env hd)
in (match (_64_352) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _153_304 = (norm_pat env p)
in (Prims.fst _153_304)))))
in ((

let _64_355 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _64_355.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _64_355.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _64_372 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _64_363 _64_366 -> (match ((_64_363, _64_366)) with
| ((pats, env), (p, b)) -> begin
(

let _64_369 = (norm_pat env p)
in (match (_64_369) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_64_372) with
| (pats, env) -> begin
((

let _64_373 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _64_373.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _64_373.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _64_377 = x
in (let _153_307 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _64_377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_307}))
in ((

let _64_380 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _64_380.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _64_380.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _64_384 = x
in (let _153_308 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _64_384.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_384.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_308}))
in ((

let _64_387 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _64_387.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _64_387.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _64_393 = x
in (let _153_309 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _64_393.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_393.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_309}))
in (

let t = (closure_as_term cfg env t)
in ((

let _64_397 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _64_397.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _64_397.FStar_Syntax_Syntax.p}), env)))
end))
in (

let _64_401 = (norm_pat env pat)
in (match (_64_401) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _153_310 = (closure_as_term cfg env w)
in Some (_153_310))
end)
in (

let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _153_313 = (let _153_312 = (let _153_311 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _153_311))
in FStar_Syntax_Syntax.Tm_match (_153_312))
in (mk _153_313 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _64_411 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _64_414 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _64_420 -> begin
(FStar_List.map (fun _64_423 -> (match (_64_423) with
| (x, imp) -> begin
(let _153_321 = (closure_as_term_delayed cfg env x)
in (_153_321, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (

let _64_439 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _64_429 _64_432 -> (match ((_64_429, _64_432)) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let _64_433 = b
in (let _153_327 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _64_433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_327}))
in (

let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_64_439) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _64_445 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _153_331 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _153_331))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _153_332 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _153_332))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _64_4 -> (match (_64_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _153_334 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_153_334))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let _64_459 = c
in {FStar_Syntax_Syntax.effect_name = _64_459.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _64_5 -> (match (_64_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _153_341 = (

let _64_467 = lc
in (let _153_340 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _64_467.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _153_340; FStar_Syntax_Syntax.cflags = _64_467.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _64_469 -> (match (()) with
| () -> begin
(let _153_339 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _153_339))
end))}))
in Some (_153_341))
end))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _64_474 = t
in {FStar_Syntax_Syntax.n = _64_474.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_474.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_474.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _64_483 -> begin
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
| ((Some (true), _)::(_, (arg, _))::[]) | ((_, (arg, _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _64_561 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (false), _)::(_, (arg, _))::[]) | ((_, (arg, _))::(Some (false), _)::[]) -> begin
arg
end
| _64_604 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _64_631)::(_64_622, (arg, _64_625))::[] -> begin
arg
end
| _64_635 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _64_639)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _64_645)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _64_649 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _153_352 = (FStar_Syntax_Subst.compress t)
in _153_352.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_64_667::[], body, _64_671) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _64_679 -> begin
tm
end)
end
| _64_681 -> begin
tm
end)
end
| _64_683 -> begin
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
| _64_685 -> begin
tm
end)
end))))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _64_692 = (log cfg (fun _64_691 -> (match (()) with
| () -> begin
(let _153_379 = (FStar_Syntax_Print.tag_of_term t)
in (let _153_378 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _153_379 _153_378)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_64_695) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _153_383 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _153_383)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _153_385 = (let _153_384 = (FStar_List.map (norm_universe cfg env) us)
in (_153_384, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_153_385))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

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

let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _64_756)::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _64_764 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _64_766 -> begin
(let _153_389 = (let _153_388 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _153_388))
in (FStar_All.failwith _153_389))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_64_770) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _64_783 = (log cfg (fun _64_782 -> (match (()) with
| () -> begin
(let _153_392 = (FStar_Syntax_Print.term_to_string t)
in (let _153_391 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _153_392 _153_391)))
end)))
in (match ((let _153_393 = (FStar_Syntax_Subst.compress t')
in _153_393.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_64_786) -> begin
(norm cfg env stack t')
end
| _64_789 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end)
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| Meta (_64_799)::_64_797 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_64_805)::_64_803 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_64_811)::_64_809 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _64_817, _64_819)::stack -> begin
(match (c) with
| Univ (_64_824) -> begin
(norm cfg ((c)::env) stack t)
end
| _64_827 -> begin
(

let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _64_830::[] -> begin
body
end
| _64_834::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
end)
in (

let _64_838 = (log cfg (fun _64_837 -> (match (()) with
| () -> begin
(let _153_395 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _153_395))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(

let _64_844 = (set_memo r (env, t))
in (

let _64_847 = (log cfg (fun _64_846 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _153_397 = (closure_as_term cfg env t)
in (rebuild cfg env stack _153_397))
end else begin
(

let _64_865 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_64_865) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _153_401 = (let _153_399 = (let _153_398 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _153_398))
in (FStar_All.pipe_right _153_399 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _153_401 (fun _153_400 -> Some (_153_400))))
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _64_871 -> (Dummy)::env) env))
in (

let _64_875 = (log cfg (fun _64_874 -> (match (()) with
| () -> begin
(let _153_405 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _153_405))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _64_883 stack -> (match (_64_883) with
| (a, aq) -> begin
(let _153_412 = (let _153_411 = (let _153_410 = (let _153_409 = (let _153_408 = (FStar_Util.mk_ref None)
in (env, a, _153_408))
in Clos (_153_409))
in (_153_410, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_153_411))
in (_153_412)::stack)
end)) args))
in (

let _64_887 = (log cfg (fun _64_886 -> (match (()) with
| () -> begin
(let _153_414 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _153_414))
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

let _64_897 = x
in {FStar_Syntax_Syntax.ppname = _64_897.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_897.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _64_901 -> begin
(let _153_415 = (closure_as_term cfg env t)
in (rebuild cfg env stack _153_415))
end)
end else begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let _64_905 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_64_905) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _153_418 = (let _153_417 = (let _153_416 = (FStar_Syntax_Subst.close closing f)
in ((

let _64_907 = x
in {FStar_Syntax_Syntax.ppname = _64_907.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_907.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _153_416))
in FStar_Syntax_Syntax.Tm_refine (_153_417))
in (mk _153_418 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _153_419 = (closure_as_term cfg env t)
in (rebuild cfg env stack _153_419))
end else begin
(

let _64_916 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_64_916) with
| (bs, c) -> begin
(

let c = (let _153_422 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _64_918 -> (Dummy)::env) env))
in (norm_comp cfg _153_422 c))
in (

let t = (let _153_423 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _153_423 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _64_946 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _64_949 = (log cfg (fun _64_948 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _153_425 = (norm cfg env [] t)
in FStar_Util.Inl (_153_425))
end
| FStar_Util.Inr (c) -> begin
(let _153_426 = (norm_comp cfg env c)
in FStar_Util.Inr (_153_426))
end)
in (let _153_427 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, tc, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _153_427)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(

let env = (let _153_430 = (let _153_429 = (let _153_428 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _153_428))
in Clos (_153_429))
in (_153_430)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_64_970, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_64_982); FStar_Syntax_Syntax.lbunivs = _64_980; FStar_Syntax_Syntax.lbtyp = _64_978; FStar_Syntax_Syntax.lbeff = _64_976; FStar_Syntax_Syntax.lbdef = _64_974}::_64_972), _64_988) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _64_1010 = (FStar_List.fold_right (fun lb _64_999 -> (match (_64_999) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _153_433 = (

let _64_1000 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _64_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _64_1000.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _153_433))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_64_1010) with
| (rec_env, memos, _64_1009) -> begin
(

let _64_1013 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _153_440 = (let _153_439 = (let _153_438 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _153_438))
in Clos (_153_439))
in (_153_440)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _64_1025::_64_1023 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _64_1030) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _64_1037 -> begin
(norm cfg env stack head)
end)
end
| _64_1039 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _153_441 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_153_441))
end
| _64_1044 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _64_1052 -> (match (_64_1052) with
| (a, imp) -> begin
(let _153_446 = (norm cfg env [] a)
in (_153_446, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _64_1058 = comp
in (let _153_451 = (let _153_450 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_153_450))
in {FStar_Syntax_Syntax.n = _153_451; FStar_Syntax_Syntax.tk = _64_1058.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _64_1058.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_1058.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _64_1062 = comp
in (let _153_453 = (let _153_452 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_153_452))
in {FStar_Syntax_Syntax.n = _153_453; FStar_Syntax_Syntax.tk = _64_1062.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _64_1062.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_1062.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _64_1070 -> (match (_64_1070) with
| (a, i) -> begin
(let _153_457 = (norm cfg env [] a)
in (_153_457, i))
end)))))
in (

let _64_1071 = comp
in (let _153_461 = (let _153_460 = (

let _64_1073 = ct
in (let _153_459 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _153_458 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _64_1073.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _153_459; FStar_Syntax_Syntax.effect_args = _153_458; FStar_Syntax_Syntax.flags = _64_1073.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_153_460))
in {FStar_Syntax_Syntax.n = _153_461; FStar_Syntax_Syntax.tk = _64_1071.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _64_1071.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _64_1071.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _64_1079 -> (match (_64_1079) with
| (x, imp) -> begin
(let _153_466 = (

let _64_1080 = x
in (let _153_465 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _64_1080.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1080.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _153_465}))
in (_153_466, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let _64_1093 = (FStar_List.fold_left (fun _64_1087 b -> (match (_64_1087) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_64_1093) with
| (nbs, _64_1092) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(

let _64_1110 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _153_476 = (

let _64_1123 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _64_1123.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_1123.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _64_1123.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _153_476))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(

let _64_1166 = (log cfg (fun _64_1165 -> (match (()) with
| () -> begin
(let _153_478 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _153_478))
end)))
in (match ((FStar_ST.read m)) with
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
| Some (_64_1173, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _153_479 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _153_479)))
end
| Match (env, branches, r)::stack -> begin
(

let norm_and_rebuild_match = (fun _64_1194 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _64_1196 = cfg
in (let _153_482 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _64_1196.steps; tcenv = _64_1196.tcenv; delta_level = _153_482}))
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
| _64_1204 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _64_1209 = (FStar_Syntax_Subst.open_branch branch)
in (match (_64_1209) with
| (p, wopt, e) -> begin
(

let env = (let _153_490 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _153_490 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _153_491 = (norm_or_whnf env w)
in Some (_153_491))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _153_492 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _153_492))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _64_1223) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _64_1248 -> begin
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

let _64_1265 = (FStar_Syntax_Util.head_and_args t)
in (match (_64_1265) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_64_1271) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_64_1288) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _64_1295 -> begin
(let _153_509 = (not ((is_cons head)))
in FStar_Util.Inr (_153_509))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _64_1303 -> begin
(let _153_510 = (not ((is_cons head)))
in FStar_Util.Inr (_153_510))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _64_1313)::rest_a, (p, _64_1319)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _64_1327 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun t p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| (p, wopt, b)::rest -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inr (false) -> begin
(matches t rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let env = (FStar_List.fold_right (fun t env -> (let _153_522 = (let _153_521 = (let _153_520 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _153_520))
in Clos (_153_521))
in (_153_522)::env)) s env)
in (let _153_523 = (guard_when_clause wopt b rest)
in (norm cfg env stack _153_523)))
end)
end))
in (matches t branches))))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (match ((FStar_Util.find_map s (fun _64_6 -> (match (_64_6) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _64_1353 -> begin
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


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _153_535 = (config s e)
in (norm _153_535 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _153_542 = (config s e)
in (norm_comp _153_542 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _153_547 = (config [] env)
in (norm_universe _153_547 [] u)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _153_552 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _153_552)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _153_558 = (let _153_557 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _153_557 [] c))
in (FStar_Syntax_Print.comp_to_string _153_558)))


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
(let _153_569 = (let _153_568 = (let _153_567 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _153_567))
in FStar_Syntax_Syntax.Tm_refine (_153_568))
in (mk _153_569 t0.FStar_Syntax_Syntax.pos))
end
| _64_1387 -> begin
t
end))
end
| _64_1389 -> begin
t
end)))
in (aux t))))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _153_574 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _153_574 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _64_1400 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_64_1400) with
| (binders, cdef) -> begin
(

let inst = (let _153_578 = (let _153_577 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_153_577)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _64_1404 _64_1408 -> (match ((_64_1404, _64_1408)) with
| ((x, _64_1403), (t, _64_1407)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _153_578))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _64_1411 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _64_1411.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _64_1411.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _64_1411.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))


let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _64_1414 _64_1416 _64_1418 -> (FStar_All.failwith "NYI: normalize_sigelt"))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _64_1420 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let _64_1427 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_64_1427) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _64_1430 -> begin
(

let _64_1433 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_64_1433) with
| (binders, args) -> begin
(let _153_591 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _153_590 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _153_589 -> Some (_153_589)))
in (FStar_Syntax_Util.abs binders _153_591 _153_590)))
end))
end)
end))
end
| _64_1435 -> begin
(let _153_594 = (let _153_593 = (FStar_Syntax_Print.tag_of_term t)
in (let _153_592 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _153_593 _153_592)))
in (FStar_All.failwith _153_594))
end))





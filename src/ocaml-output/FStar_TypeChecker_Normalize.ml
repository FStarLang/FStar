
open Prims
type step =
| WHNF
| Inline
| Unfold
| Beta
| Simplify
| EraseUniverses
| DeltaComp
| SNComp
| Eta
| EtaArgs
| Unmeta
| Unlabel 
 and steps =
step Prims.list

let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF -> begin
true
end
| _ -> begin
false
end))

let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold -> begin
true
end
| _ -> begin
false
end))

let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta -> begin
true
end
| _ -> begin
false
end))

let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify -> begin
true
end
| _ -> begin
false
end))

let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses -> begin
true
end
| _ -> begin
false
end))

let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp -> begin
true
end
| _ -> begin
false
end))

let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp -> begin
true
end
| _ -> begin
false
end))

let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta -> begin
true
end
| _ -> begin
false
end))

let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs -> begin
true
end
| _ -> begin
false
end))

let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta -> begin
true
end
| _ -> begin
false
end))

let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel -> begin
true
end
| _ -> begin
false
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
| Dummy -> begin
true
end
| _ -> begin
false
end))

let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_81_8) -> begin
_81_8
end))

let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_81_11) -> begin
_81_11
end))

let closure_to_string = (fun _81_1 -> (match (_81_1) with
| Clos (_81_14, t, _81_17) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _81_21 -> begin
"dummy"
end))

type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}

let is_Mkcfg = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))

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
| Label of (Prims.string * FStar_Range.range)

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

let is_Label = (fun _discr_ -> (match (_discr_) with
| Label (_) -> begin
true
end
| _ -> begin
false
end))

let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_81_28) -> begin
_81_28
end))

let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_81_31) -> begin
_81_31
end))

let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_81_34) -> begin
_81_34
end))

let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_81_37) -> begin
_81_37
end))

let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_81_40) -> begin
_81_40
end))

let ___App____0 = (fun projectee -> (match (projectee) with
| App (_81_43) -> begin
_81_43
end))

let ___Label____0 = (fun projectee -> (match (projectee) with
| Label (_81_46) -> begin
_81_46
end))

type stack =
stack_elt Prims.list

let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_81_52) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

let env_to_string = (fun env -> (let _172_158 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _172_158 (FStar_String.concat "; "))))

let stack_elt_to_string = (fun _81_2 -> (match (_81_2) with
| Arg (c, _81_59, _81_61) -> begin
(closure_to_string c)
end
| MemoLazy (_81_65) -> begin
"MemoLazy"
end
| Abs (_81_68, bs, _81_71, _81_73, _81_75) -> begin
(let _172_161 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _172_161))
end
| _81_79 -> begin
"Match"
end))

let stack_to_string = (fun s -> (let _172_164 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _172_164 (FStar_String.concat "; "))))

let log = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

let is_empty = (fun _81_3 -> (match (_81_3) with
| [] -> begin
true
end
| _81_86 -> begin
false
end))

let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _81_90 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _81_89 -> (match (_81_89) with
| _81_93 -> begin
(let _172_180 = (let _172_179 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _172_179))
in (FStar_All.failwith _172_180))
end))))

let norm_universe = (fun cfg env u -> (let norm_univs = (fun us -> (let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (let _81_114 = (FStar_List.fold_left (fun _81_105 u -> (match (_81_105) with
| (cur_kernel, cur_max, out) -> begin
(let _81_109 = (FStar_Syntax_Util.univ_kernel u)
in (match (_81_109) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_81_114) with
| (_81_111, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _81_121 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| _81_130 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _81_120 -> (match (_81_120) with
| _81_124 -> begin
(FStar_All.failwith "Universe variable not found")
end)))
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _172_195 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _172_195 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _172_197 = (aux u)
in (FStar_List.map (fun _172_196 -> FStar_Syntax_Syntax.U_succ (_172_196)) _172_197))
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

let rec closure_as_term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _81_162 -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_81_165) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _172_224 = (let _172_223 = (let _172_222 = (closure_as_term_delayed cfg env t')
in (u, _172_222))
in FStar_Syntax_Syntax.Tm_uvar (_172_223))
in (mk _172_224 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _172_226 = (let _172_225 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_172_225))
in (mk _172_226 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _172_227 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _172_227))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_81_190) -> begin
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
(let head = (closure_as_term_delayed cfg env head)
in (let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(let _81_211 = (closures_as_binders_delayed cfg env bs)
in (match (_81_211) with
| (bs, env) -> begin
(let body = (closure_as_term_delayed cfg env body)
in (let _172_230 = (let _172_229 = (let _172_228 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _172_228))
in FStar_Syntax_Syntax.Tm_abs (_172_229))
in (mk _172_230 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _81_219 = (closures_as_binders_delayed cfg env bs)
in (match (_81_219) with
| (bs, env) -> begin
(let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let _81_227 = (let _172_232 = (let _172_231 = (FStar_Syntax_Syntax.mk_binder x)
in (_172_231)::[])
in (closures_as_binders_delayed cfg env _172_232))
in (match (_81_227) with
| (x, env) -> begin
(let phi = (closure_as_term_delayed cfg env phi)
in (let _172_236 = (let _172_235 = (let _172_234 = (let _172_233 = (FStar_List.hd x)
in (FStar_All.pipe_right _172_233 Prims.fst))
in (_172_234, phi))
in FStar_Syntax_Syntax.Tm_refine (_172_235))
in (mk _172_236 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _172_240 = (let _172_239 = (let _172_238 = (closure_as_term_delayed cfg env t1)
in (let _172_237 = (closure_as_term_delayed cfg env t2)
in (_172_238, _172_237, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_172_239))
in (mk _172_240 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _172_243 = (let _172_242 = (let _172_241 = (closure_as_term_delayed cfg env t')
in (_172_241, m))
in FStar_Syntax_Syntax.Tm_meta (_172_242))
in (mk _172_243 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_match (_81_239) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Syntax_Syntax.Tm_let (_81_242) -> begin
(FStar_All.failwith "NYI")
end))
end))
and closure_as_term_delayed = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _81_249 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inr ((fun _81_250 -> (match (()) with
| () -> begin
(closure_as_term cfg env t)
end)))) t.FStar_Syntax_Syntax.pos)
end))
and closures_as_args_delayed = (fun cfg env args -> (match (env) with
| [] -> begin
args
end
| _81_256 -> begin
(FStar_List.map (fun _81_259 -> (match (_81_259) with
| (x, imp) -> begin
(let _172_254 = (closure_as_term_delayed cfg env x)
in (_172_254, imp))
end)) args)
end))
and closures_as_binders_delayed = (fun cfg env bs -> (let _81_275 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _81_265 _81_268 -> (match ((_81_265, _81_268)) with
| ((env, out), (b, imp)) -> begin
(let b = (let _81_269 = b
in (let _172_260 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _81_269.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _81_269.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _172_260}))
in (let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_81_275) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp = (fun cfg env c -> (match (env) with
| [] -> begin
c
end
| _81_281 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _172_264 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _172_264))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _172_265 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _172_265))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _81_4 -> (match (_81_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _172_267 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_172_267))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (let _81_295 = c
in {FStar_Syntax_Syntax.effect_name = _81_295.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt = (fun cfg env _81_5 -> (match (_81_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _172_274 = (let _81_303 = lc
in (let _172_273 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _81_303.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _172_273; FStar_Syntax_Syntax.cflags = _81_303.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _81_305 -> (match (()) with
| () -> begin
(let _172_272 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _172_272))
end))}))
in Some (_172_274))
end))

let maybe_simplify = (fun steps tm -> (let w = (fun t -> (let _81_310 = t
in {FStar_Syntax_Syntax.n = _81_310.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _81_310.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _81_310.FStar_Syntax_Syntax.vars}))
in (let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _81_316) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _81_321) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _81_325 -> begin
None
end))
in (let simplify = (fun arg -> ((simp_t (Prims.fst arg)), arg))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::(_, (arg, _))::[]) | ((_, (arg, _))::(Some (true), _)::[]) -> begin
arg
end
| ((Some (false), _)::_::[]) | (_::(Some (false), _)::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _81_409 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _)::_::[]) | (_::(Some (true), _)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (false), _)::(_, (arg, _))::[]) | ((_, (arg, _))::(Some (false), _)::[]) -> begin
arg
end
| _81_452 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _81_479)::(_81_470, (arg, _81_473))::[] -> begin
arg
end
| _81_483 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _81_487)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _81_493)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _81_497 -> begin
tm
end)
end else begin
if ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit))::(t, _)::[]) -> begin
(match ((let _172_285 = (FStar_Syntax_Subst.compress t)
in _172_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_81_513::[], body, _81_517) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _81_525 -> begin
tm
end)
end
| _81_527 -> begin
tm
end)
end
| _81_529 -> begin
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
| _81_531 -> begin
tm
end)
end))))

let rec norm = (fun cfg env stack t -> (let t = (FStar_Syntax_Subst.compress t)
in (let _81_538 = (log cfg (fun _81_537 -> (match (()) with
| () -> begin
(let _172_309 = (FStar_Syntax_Print.tag_of_term t)
in (let _172_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _172_309 _172_308)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_81_541) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let u = (norm_universe cfg env u)
in (let _172_313 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _172_313)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(let us = (let _172_315 = (let _172_314 = (FStar_List.map (norm_universe cfg env) us)
in (_172_314, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_172_315))
in (let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f, _81_577) -> begin
if (cfg.delta_level = FStar_TypeChecker_Env.NoDelta) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _81_589)::stack -> begin
(let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _81_597 -> begin
(let _172_319 = (let _172_318 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _172_318))
in (FStar_All.failwith _172_319))
end)
end else begin
(norm cfg env stack t)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_81_601) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(let _81_614 = (log cfg (fun _81_613 -> (match (()) with
| () -> begin
(let _172_322 = (FStar_Syntax_Print.term_to_string t)
in (let _172_321 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _172_322 _172_321)))
end)))
in (match ((let _172_323 = (FStar_Syntax_Subst.compress t')
in _172_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_81_617) -> begin
(norm cfg env stack t')
end
| _81_620 -> begin
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
| Label (_81_630)::_81_628 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_81_636)::_81_634 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_81_642)::_81_640 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _81_648, _81_650)::stack -> begin
(match (c) with
| Univ (_81_655) -> begin
(norm cfg ((c)::env) stack t)
end
| _81_658 -> begin
(let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _81_661::[] -> begin
body
end
| _81_665::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (let _81_669 = (log cfg (fun _81_668 -> (match (()) with
| () -> begin
(let _172_325 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _172_325))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(let _81_675 = (set_memo r (env, t))
in (let _81_678 = (log cfg (fun _81_677 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _172_327 = (closure_as_term cfg env t)
in (rebuild cfg env stack _172_327))
end else begin
(let _81_695 = (FStar_Syntax_Subst.open_term bs body)
in (match (_81_695) with
| (bs, body) -> begin
(let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _81_697 -> (Dummy)::env) env))
in (let _81_701 = (log cfg (fun _81_700 -> (match (()) with
| () -> begin
(let _172_331 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _172_331))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _81_709 stack -> (match (_81_709) with
| (a, aq) -> begin
(let _172_338 = (let _172_337 = (let _172_336 = (let _172_335 = (let _172_334 = (FStar_Util.mk_ref None)
in (env, a, _172_334))
in Clos (_172_335))
in (_172_336, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_172_337))
in (_172_338)::stack)
end)) args))
in (let _81_713 = (log cfg (fun _81_712 -> (match (()) with
| () -> begin
(let _172_340 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _172_340))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _172_341 = (closure_as_term cfg env t)
in (rebuild cfg env stack _172_341))
end else begin
(let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (let _81_722 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_81_722) with
| (closing, f) -> begin
(let f = (norm cfg ((Dummy)::env) [] f)
in (let t = (let _172_344 = (let _172_343 = (let _172_342 = (FStar_Syntax_Subst.close closing f)
in ((let _81_724 = x
in {FStar_Syntax_Syntax.ppname = _81_724.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _81_724.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _172_342))
in FStar_Syntax_Syntax.Tm_refine (_172_343))
in (mk _172_344 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _172_345 = (closure_as_term cfg env t)
in (rebuild cfg env stack _172_345))
end else begin
(let _81_733 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_81_733) with
| (bs, c) -> begin
(let c = (let _172_348 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _81_735 -> (Dummy)::env) env))
in (norm_comp cfg _172_348 c))
in (let t = (let _172_349 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _172_349 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _81_763 -> begin
(let t1 = (norm cfg env [] t1)
in (let _81_766 = (log cfg (fun _81_765 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (let t2 = (norm cfg env [] t2)
in (let _172_351 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _172_351)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(let env = (let _172_354 = (let _172_353 = (let _172_352 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _172_352))
in Clos (_172_353))
in (_172_354)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_81_783, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_81_795); FStar_Syntax_Syntax.lbunivs = _81_793; FStar_Syntax_Syntax.lbtyp = _81_791; FStar_Syntax_Syntax.lbeff = _81_789; FStar_Syntax_Syntax.lbdef = _81_787}::_81_785), _81_801) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(let _81_823 = (FStar_List.fold_right (fun lb _81_812 -> (match (_81_812) with
| (rec_env, memos, i) -> begin
(let f_i = (let _172_357 = (let _81_813 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _81_813.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _81_813.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _172_357))
in (let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (let memo = (FStar_Util.mk_ref None)
in (let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_81_823) with
| (rec_env, memos, _81_822) -> begin
(let _81_826 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (let body_env = (FStar_List.fold_right (fun lb env -> (let _172_364 = (let _172_363 = (let _172_362 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _172_362))
in Clos (_172_363))
in (_172_364)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _81_838::_81_836 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _81_843) -> begin
(norm cfg env ((Label ((l, r)))::stack) head)
end
| _81_847 -> begin
(norm cfg env stack head)
end)
end
| _81_849 -> begin
(let head = (norm cfg env [] head)
in (let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let args = (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _81_855 -> (match (_81_855) with
| (a, imp) -> begin
(let _172_366 = (norm cfg env [] a)
in (_172_366, imp))
end)))))
in FStar_Syntax_Syntax.Meta_pattern (args))
end
| _81_858 -> begin
m
end)
in (let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _81_866 = comp
in (let _172_371 = (let _172_370 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_172_370))
in {FStar_Syntax_Syntax.n = _172_371; FStar_Syntax_Syntax.tk = _81_866.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _81_866.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _81_866.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _81_870 = comp
in (let _172_373 = (let _172_372 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_172_372))
in {FStar_Syntax_Syntax.n = _172_373; FStar_Syntax_Syntax.tk = _81_870.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _81_870.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _81_870.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _81_878 -> (match (_81_878) with
| (a, i) -> begin
(let _172_377 = (norm cfg env [] a)
in (_172_377, i))
end)))))
in (let _81_879 = comp
in (let _172_381 = (let _172_380 = (let _81_881 = ct
in (let _172_379 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _172_378 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _81_881.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _172_379; FStar_Syntax_Syntax.effect_args = _172_378; FStar_Syntax_Syntax.flags = _81_881.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_172_380))
in {FStar_Syntax_Syntax.n = _172_381; FStar_Syntax_Syntax.tk = _81_879.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _81_879.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _81_879.FStar_Syntax_Syntax.vars})))
end))
and norm_binder = (fun cfg env _81_887 -> (match (_81_887) with
| (x, imp) -> begin
(let _172_386 = (let _81_888 = x
in (let _172_385 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _81_888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _81_888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _172_385}))
in (_172_386, imp))
end))
and norm_binders = (fun cfg env bs -> (let _81_901 = (FStar_List.fold_left (fun _81_895 b -> (match (_81_895) with
| (nbs', env) -> begin
(let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_81_901) with
| (nbs, _81_900) -> begin
(FStar_List.rev nbs)
end)))
and rebuild = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Label (r, r')::stack -> begin
(let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, FStar_Syntax_Syntax.Meta_labeled ((r, r', false))))) r')
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(let _81_918 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(let bs = (norm_binders cfg env' bs)
in (let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _172_396 = (let _81_931 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _81_931.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _81_931.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _81_931.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _172_396))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(let _81_974 = (log cfg (fun _81_973 -> (match (()) with
| () -> begin
(let _172_398 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _172_398))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let arg = (closure_as_term cfg env tm)
in (let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_81_981, a) -> begin
(let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _172_399 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _172_399)))
end
| Match (env, branches, r)::stack -> begin
(let norm_and_rebuild_match = (fun _81_1002 -> (match (()) with
| () -> begin
(let whnf = (FStar_List.contains WHNF cfg.steps)
in (let cfg = (let _81_1004 = cfg
in (let _172_402 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _81_1004.steps; tcenv = _81_1004.tcenv; delta_level = _172_402}))
in (let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (let _81_1014 = (FStar_Syntax_Subst.open_branch branch)
in (match (_81_1014) with
| (p, wopt, e) -> begin
(let env = (let _172_410 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _172_410 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _172_411 = (norm_or_whnf env w)
in Some (_172_411))
end)
in (let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _172_412 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _172_412))))))
end))
in (let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _81_1028) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
true
end
| _81_1049 -> begin
false
end))
in (let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(let then_branch = b
in (let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (let rec matches_pat = (fun t p -> (let t = (FStar_Syntax_Subst.compress t)
in (let _81_1066 = (FStar_Syntax_Util.head_and_args t)
in (match (_81_1066) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let mopt = (FStar_Util.find_map ps (fun p -> (let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_81_1072) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_81_1089) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _81_1096 -> begin
(let _172_429 = (not ((is_cons head)))
in FStar_Util.Inr (_172_429))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _81_1104 -> begin
(let _172_430 = (not ((is_cons head)))
in FStar_Util.Inr (_172_430))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _81_1114)::rest_a, (p, _81_1120)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _81_1128 -> begin
FStar_Util.Inr (false)
end))
in (let rec matches = (fun t p -> (match (p) with
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
(let env = (FStar_List.fold_right (fun t env -> (let _172_442 = (let _172_441 = (let _172_440 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _172_440))
in Clos (_172_441))
in (_172_442)::env)) s env)
in (let _172_443 = (guard_when_clause wopt b rest)
in (norm cfg env stack _172_443)))
end)
end))
in (matches t branches))))))
end))

let config = (fun s e -> (let d = if (FStar_List.contains Unfold s) then begin
FStar_TypeChecker_Env.Unfold
end else begin
if (FStar_List.contains Inline s) then begin
FStar_TypeChecker_Env.OnlyInline
end else begin
FStar_TypeChecker_Env.NoDelta
end
end
in {steps = s; tcenv = e; delta_level = d}))

let normalize = (fun s e t -> (norm (config s e) [] [] t))

let normalize_comp = (fun s e t -> (norm_comp (config s e) [] t))

let normalize_universe = (fun env u -> (norm_universe (config [] env) [] u))

let term_to_string = (fun env t -> (let _172_468 = (normalize ((EraseUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _172_468)))

let comp_to_string = (fun env c -> (let _172_473 = (norm_comp (config ((EraseUniverses)::[]) env) [] c)
in (FStar_Syntax_Print.comp_to_string _172_473)))

let normalize_refinement = (fun steps env t0 -> (let t = (normalize (FStar_List.append steps ((Beta)::(WHNF)::[])) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _172_484 = (let _172_483 = (let _172_482 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _172_482))
in FStar_Syntax_Syntax.Tm_refine (_172_483))
in (mk _172_484 t0.FStar_Syntax_Syntax.pos))
end
| _81_1180 -> begin
t
end))
end
| _81_1182 -> begin
t
end)))
in (aux t))))

let rec unfold_effect_abbrev = (fun env comp -> (let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let _81_1193 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_81_1193) with
| (binders, cdef) -> begin
(let inst = (let _172_492 = (let _172_491 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_172_491)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _81_1197 _81_1201 -> (match ((_81_1197, _81_1201)) with
| ((x, _81_1196), (t, _81_1200)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _172_492))
in (let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (let c = (FStar_All.pipe_right (let _81_1204 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _81_1204.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _81_1204.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _81_1204.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

let normalize_sigelt = (fun _81_1207 _81_1209 _81_1211 -> (FStar_All.failwith "NYI: normalize_sigelt"))

let eta_expand = (fun _81_1213 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _81_1220 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_81_1220) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _81_1223 -> begin
(let _81_1226 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_81_1226) with
| (binders, args) -> begin
(let _172_505 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _172_504 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _172_503 -> Some (_172_503)))
in (FStar_Syntax_Util.abs binders _172_505 _172_504)))
end))
end)
end))
end
| _81_1228 -> begin
(let _172_508 = (let _172_507 = (FStar_Syntax_Print.tag_of_term t)
in (let _172_506 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _172_507 _172_506)))
in (FStar_All.failwith _172_508))
end))





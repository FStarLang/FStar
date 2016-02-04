
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

let is_WHNF : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| WHNF -> begin
true
end
| _ -> begin
false
end))

let is_Inline : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Inline -> begin
true
end
| _ -> begin
false
end))

let is_Unfold : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Unfold -> begin
true
end
| _ -> begin
false
end))

let is_Beta : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Beta -> begin
true
end
| _ -> begin
false
end))

let is_Simplify : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Simplify -> begin
true
end
| _ -> begin
false
end))

let is_EraseUniverses : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| EraseUniverses -> begin
true
end
| _ -> begin
false
end))

let is_DeltaComp : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| DeltaComp -> begin
true
end
| _ -> begin
false
end))

let is_SNComp : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SNComp -> begin
true
end
| _ -> begin
false
end))

let is_Eta : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Eta -> begin
true
end
| _ -> begin
false
end))

let is_EtaArgs : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| EtaArgs -> begin
true
end
| _ -> begin
false
end))

let is_Unmeta : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Unmeta -> begin
true
end
| _ -> begin
false
end))

let is_Unlabel : step  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
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

let is_Clos : closure  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))

let is_Univ : closure  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))

let is_Dummy : closure  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Dummy -> begin
true
end
| _ -> begin
false
end))

let ___Clos____0 : closure  ->  (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) = (fun projectee -> (match (projectee) with
| Clos (_86_8) -> begin
_86_8
end))

let ___Univ____0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_86_11) -> begin
_86_11
end))

let closure_to_string : closure  ->  Prims.string = (fun _86_1 -> (match (_86_1) with
| Clos (_86_14, t, _86_17) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _86_21 -> begin
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
| Label of (Prims.string * FStar_Range.range)

let is_Arg : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))

let is_UnivArgs : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))

let is_MemoLazy : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))

let is_Match : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

let is_Abs : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

let is_App : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

let is_Label : stack_elt  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Label (_) -> begin
true
end
| _ -> begin
false
end))

let ___Arg____0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_86_28) -> begin
_86_28
end))

let ___UnivArgs____0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_86_31) -> begin
_86_31
end))

let ___MemoLazy____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_86_34) -> begin
_86_34
end))

let ___Match____0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_86_37) -> begin
_86_37
end))

let ___Abs____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_86_40) -> begin
_86_40
end))

let ___App____0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_86_43) -> begin
_86_43
end))

let ___Label____0 : stack_elt  ->  (Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Label (_86_46) -> begin
_86_46
end))

type stack =
stack_elt Prims.list

let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_86_52) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _189_158 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _189_158 (FStar_String.concat "; "))))

let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _86_2 -> (match (_86_2) with
| Arg (c, _86_59, _86_61) -> begin
(closure_to_string c)
end
| MemoLazy (_86_65) -> begin
"MemoLazy"
end
| Abs (_86_68, bs, _86_71, _86_73, _86_75) -> begin
(let _189_161 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _189_161))
end
| _86_79 -> begin
"Match"
end))

let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _189_164 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _189_164 (FStar_String.concat "; "))))

let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

let is_empty = (fun _86_3 -> (match (_86_3) with
| [] -> begin
true
end
| _86_86 -> begin
false
end))

let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _86_90 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _86_89 -> (match (_86_89) with
| _86_93 -> begin
(let _189_180 = (let _189_179 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _189_179))
in (FStar_All.failwith _189_180))
end))))

let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (let norm_univs = (fun us -> (let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (let _86_114 = (FStar_List.fold_left (fun _86_105 u -> (match (_86_105) with
| (cur_kernel, cur_max, out) -> begin
(let _86_109 = (FStar_Syntax_Util.univ_kernel u)
in (match (_86_109) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_86_114) with
| (_86_111, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _86_121 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| _86_130 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _86_120 -> (match (_86_120) with
| _86_124 -> begin
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
(let _189_195 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _189_195 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _189_197 = (aux u)
in (FStar_List.map (fun _189_196 -> FStar_Syntax_Syntax.U_succ (_189_196)) _189_197))
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

let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _86_162 -> begin
(let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_86_165) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _189_224 = (let _189_223 = (let _189_222 = (closure_as_term_delayed cfg env t')
in (u, _189_222))
in FStar_Syntax_Syntax.Tm_uvar (_189_223))
in (mk _189_224 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _189_226 = (let _189_225 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_189_225))
in (mk _189_226 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _189_227 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _189_227))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_86_190) -> begin
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
(let _86_211 = (closures_as_binders_delayed cfg env bs)
in (match (_86_211) with
| (bs, env) -> begin
(let body = (closure_as_term_delayed cfg env body)
in (let _189_230 = (let _189_229 = (let _189_228 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _189_228))
in FStar_Syntax_Syntax.Tm_abs (_189_229))
in (mk _189_230 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let _86_219 = (closures_as_binders_delayed cfg env bs)
in (match (_86_219) with
| (bs, env) -> begin
(let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let _86_227 = (let _189_232 = (let _189_231 = (FStar_Syntax_Syntax.mk_binder x)
in (_189_231)::[])
in (closures_as_binders_delayed cfg env _189_232))
in (match (_86_227) with
| (x, env) -> begin
(let phi = (closure_as_term_delayed cfg env phi)
in (let _189_236 = (let _189_235 = (let _189_234 = (let _189_233 = (FStar_List.hd x)
in (FStar_All.pipe_right _189_233 Prims.fst))
in (_189_234, phi))
in FStar_Syntax_Syntax.Tm_refine (_189_235))
in (mk _189_236 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _189_240 = (let _189_239 = (let _189_238 = (closure_as_term_delayed cfg env t1)
in (let _189_237 = (closure_as_term_delayed cfg env t2)
in (_189_238, _189_237, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_189_239))
in (mk _189_240 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _189_243 = (let _189_242 = (let _189_241 = (closure_as_term_delayed cfg env t')
in (_189_241, m))
in FStar_Syntax_Syntax.Tm_meta (_189_242))
in (mk _189_243 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_match (_86_239) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Syntax_Syntax.Tm_let (_86_242) -> begin
(FStar_All.failwith "NYI")
end))
end))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _86_249 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inr ((fun _86_250 -> (match (()) with
| () -> begin
(closure_as_term cfg env t)
end)))) t.FStar_Syntax_Syntax.pos)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] -> begin
args
end
| _86_256 -> begin
(FStar_List.map (fun _86_259 -> (match (_86_259) with
| (x, imp) -> begin
(let _189_254 = (closure_as_term_delayed cfg env x)
in (_189_254, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * closure Prims.list) = (fun cfg env bs -> (let _86_275 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _86_265 _86_268 -> (match ((_86_265, _86_268)) with
| ((env, out), (b, imp)) -> begin
(let b = (let _86_269 = b
in (let _189_260 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_269.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_269.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _189_260}))
in (let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_86_275) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] -> begin
c
end
| _86_281 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _189_264 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _189_264))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _189_265 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _189_265))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _86_4 -> (match (_86_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _189_267 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_189_267))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (let _86_295 = c
in {FStar_Syntax_Syntax.effect_name = _86_295.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _86_5 -> (match (_86_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _189_274 = (let _86_303 = lc
in (let _189_273 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _86_303.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _189_273; FStar_Syntax_Syntax.cflags = _86_303.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _86_305 -> (match (()) with
| () -> begin
(let _189_272 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _189_272))
end))}))
in Some (_189_274))
end))

let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (let w = (fun t -> (let _86_310 = t
in {FStar_Syntax_Syntax.n = _86_310.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _86_310.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _86_310.FStar_Syntax_Syntax.vars}))
in (let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _86_316) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _86_321) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _86_325 -> begin
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
| _86_409 -> begin
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
| _86_452 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _86_479)::(_86_470, (arg, _86_473))::[] -> begin
arg
end
| _86_483 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _86_487)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _86_493)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _86_497 -> begin
tm
end)
end else begin
if ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit))::(t, _)::[]) -> begin
(match ((let _189_285 = (FStar_Syntax_Subst.compress t)
in _189_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_86_513::[], body, _86_517) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _86_525 -> begin
tm
end)
end
| _86_527 -> begin
tm
end)
end
| _86_529 -> begin
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
| _86_531 -> begin
tm
end)
end))))

let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (let t = (FStar_Syntax_Subst.compress t)
in (let _86_538 = (log cfg (fun _86_537 -> (match (()) with
| () -> begin
(let _189_309 = (FStar_Syntax_Print.tag_of_term t)
in (let _189_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _189_309 _189_308)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_86_541) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let u = (norm_universe cfg env u)
in (let _189_313 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _189_313)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(let us = (let _189_315 = (let _189_314 = (FStar_List.map (norm_universe cfg env) us)
in (_189_314, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_189_315))
in (let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f, _86_577) -> begin
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
| UnivArgs (us', _86_589)::stack -> begin
(let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _86_597 -> begin
(let _189_319 = (let _189_318 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _189_318))
in (FStar_All.failwith _189_319))
end)
end else begin
(norm cfg env stack t)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_86_601) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(let _86_614 = (log cfg (fun _86_613 -> (match (()) with
| () -> begin
(let _189_322 = (FStar_Syntax_Print.term_to_string t)
in (let _189_321 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _189_322 _189_321)))
end)))
in (match ((let _189_323 = (FStar_Syntax_Subst.compress t')
in _189_323.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_86_617) -> begin
(norm cfg env stack t')
end
| _86_620 -> begin
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
| Label (_86_630)::_86_628 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_86_636)::_86_634 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_86_642)::_86_640 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _86_648, _86_650)::stack -> begin
(match (c) with
| Univ (_86_655) -> begin
(norm cfg ((c)::env) stack t)
end
| _86_658 -> begin
(let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _86_661::[] -> begin
body
end
| _86_665::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (let _86_669 = (log cfg (fun _86_668 -> (match (()) with
| () -> begin
(let _189_325 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _189_325))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(let _86_675 = (set_memo r (env, t))
in (let _86_678 = (log cfg (fun _86_677 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _189_327 = (closure_as_term cfg env t)
in (rebuild cfg env stack _189_327))
end else begin
(let _86_695 = (FStar_Syntax_Subst.open_term bs body)
in (match (_86_695) with
| (bs, body) -> begin
(let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _86_697 -> (Dummy)::env) env))
in (let _86_701 = (log cfg (fun _86_700 -> (match (()) with
| () -> begin
(let _189_331 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _189_331))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _86_709 stack -> (match (_86_709) with
| (a, aq) -> begin
(let _189_338 = (let _189_337 = (let _189_336 = (let _189_335 = (let _189_334 = (FStar_Util.mk_ref None)
in (env, a, _189_334))
in Clos (_189_335))
in (_189_336, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_189_337))
in (_189_338)::stack)
end)) args))
in (let _86_713 = (log cfg (fun _86_712 -> (match (()) with
| () -> begin
(let _189_340 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _189_340))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _189_341 = (closure_as_term cfg env t)
in (rebuild cfg env stack _189_341))
end else begin
(let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (let _86_722 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_86_722) with
| (closing, f) -> begin
(let f = (norm cfg ((Dummy)::env) [] f)
in (let t = (let _189_344 = (let _189_343 = (let _189_342 = (FStar_Syntax_Subst.close closing f)
in ((let _86_724 = x
in {FStar_Syntax_Syntax.ppname = _86_724.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_724.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _189_342))
in FStar_Syntax_Syntax.Tm_refine (_189_343))
in (mk _189_344 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _189_345 = (closure_as_term cfg env t)
in (rebuild cfg env stack _189_345))
end else begin
(let _86_733 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_86_733) with
| (bs, c) -> begin
(let c = (let _189_348 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _86_735 -> (Dummy)::env) env))
in (norm_comp cfg _189_348 c))
in (let t = (let _189_349 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _189_349 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _86_763 -> begin
(let t1 = (norm cfg env [] t1)
in (let _86_766 = (log cfg (fun _86_765 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (let t2 = (norm cfg env [] t2)
in (let _189_351 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _189_351)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(let env = (let _189_354 = (let _189_353 = (let _189_352 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _189_352))
in Clos (_189_353))
in (_189_354)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_86_783, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_86_795); FStar_Syntax_Syntax.lbunivs = _86_793; FStar_Syntax_Syntax.lbtyp = _86_791; FStar_Syntax_Syntax.lbeff = _86_789; FStar_Syntax_Syntax.lbdef = _86_787}::_86_785), _86_801) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(let _86_823 = (FStar_List.fold_right (fun lb _86_812 -> (match (_86_812) with
| (rec_env, memos, i) -> begin
(let f_i = (let _189_357 = (let _86_813 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _86_813.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _86_813.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _189_357))
in (let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (let memo = (FStar_Util.mk_ref None)
in (let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_86_823) with
| (rec_env, memos, _86_822) -> begin
(let _86_826 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (let body_env = (FStar_List.fold_right (fun lb env -> (let _189_364 = (let _189_363 = (let _189_362 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _189_362))
in Clos (_189_363))
in (_189_364)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _86_838::_86_836 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _86_843) -> begin
(norm cfg env ((Label ((l, r)))::stack) head)
end
| _86_847 -> begin
(norm cfg env stack head)
end)
end
| _86_849 -> begin
(let head = (norm cfg env [] head)
in (let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let args = (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _86_855 -> (match (_86_855) with
| (a, imp) -> begin
(let _189_366 = (norm cfg env [] a)
in (_189_366, imp))
end)))))
in FStar_Syntax_Syntax.Meta_pattern (args))
end
| _86_858 -> begin
m
end)
in (let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _86_866 = comp
in (let _189_371 = (let _189_370 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_189_370))
in {FStar_Syntax_Syntax.n = _189_371; FStar_Syntax_Syntax.tk = _86_866.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _86_866.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _86_866.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _86_870 = comp
in (let _189_373 = (let _189_372 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_189_372))
in {FStar_Syntax_Syntax.n = _189_373; FStar_Syntax_Syntax.tk = _86_870.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _86_870.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _86_870.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _86_878 -> (match (_86_878) with
| (a, i) -> begin
(let _189_377 = (norm cfg env [] a)
in (_189_377, i))
end)))))
in (let _86_879 = comp
in (let _189_381 = (let _189_380 = (let _86_881 = ct
in (let _189_379 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _189_378 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _86_881.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _189_379; FStar_Syntax_Syntax.effect_args = _189_378; FStar_Syntax_Syntax.flags = _86_881.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_189_380))
in {FStar_Syntax_Syntax.n = _189_381; FStar_Syntax_Syntax.tk = _86_879.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _86_879.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _86_879.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _86_887 -> (match (_86_887) with
| (x, imp) -> begin
(let _189_386 = (let _86_888 = x
in (let _189_385 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_888.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_888.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _189_385}))
in (_189_386, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (let _86_901 = (FStar_List.fold_left (fun _86_895 b -> (match (_86_895) with
| (nbs', env) -> begin
(let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_86_901) with
| (nbs, _86_900) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Label (r, r')::stack -> begin
(let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, FStar_Syntax_Syntax.Meta_labeled ((r, r', false))))) r')
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(let _86_918 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(let bs = (norm_binders cfg env' bs)
in (let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _189_396 = (let _86_931 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _86_931.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _86_931.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _86_931.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _189_396))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(let _86_974 = (log cfg (fun _86_973 -> (match (()) with
| () -> begin
(let _189_398 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _189_398))
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
| Some (_86_981, a) -> begin
(let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _189_399 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _189_399)))
end
| Match (env, branches, r)::stack -> begin
(let norm_and_rebuild_match = (fun _86_1002 -> (match (()) with
| () -> begin
(let whnf = (FStar_List.contains WHNF cfg.steps)
in (let cfg = (let _86_1004 = cfg
in (let _189_402 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _86_1004.steps; tcenv = _86_1004.tcenv; delta_level = _189_402}))
in (let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (let _86_1014 = (FStar_Syntax_Subst.open_branch branch)
in (match (_86_1014) with
| (p, wopt, e) -> begin
(let env = (let _189_410 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _189_410 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _189_411 = (norm_or_whnf env w)
in Some (_189_411))
end)
in (let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _189_412 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _189_412))))))
end))
in (let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _86_1028) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
true
end
| _86_1049 -> begin
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
in (let _86_1066 = (FStar_Syntax_Util.head_and_args t)
in (match (_86_1066) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(let mopt = (FStar_Util.find_map ps (fun p -> (let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_86_1072) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_86_1089) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _86_1096 -> begin
(let _189_429 = (not ((is_cons head)))
in FStar_Util.Inr (_189_429))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _86_1104 -> begin
(let _189_430 = (not ((is_cons head)))
in FStar_Util.Inr (_189_430))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _86_1114)::rest_a, (p, _86_1120)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _86_1128 -> begin
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
(let env = (FStar_List.fold_right (fun t env -> (let _189_442 = (let _189_441 = (let _189_440 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _189_440))
in Clos (_189_441))
in (_189_442)::env)) s env)
in (let _189_443 = (guard_when_clause wopt b rest)
in (norm cfg env stack _189_443)))
end)
end))
in (matches t branches))))))
end))

let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (let d = if (FStar_List.contains Unfold s) then begin
FStar_TypeChecker_Env.Unfold
end else begin
if (FStar_List.contains Inline s) then begin
FStar_TypeChecker_Env.OnlyInline
end else begin
FStar_TypeChecker_Env.NoDelta
end
end
in {steps = s; tcenv = e; delta_level = d}))

let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (norm (config s e) [] [] t))

let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (norm_comp (config s e) [] t))

let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (norm_universe (config [] env) [] u))

let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _189_468 = (normalize ((EraseUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _189_468)))

let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _189_473 = (norm_comp (config ((EraseUniverses)::[]) env) [] c)
in (FStar_Syntax_Print.comp_to_string _189_473)))

let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (let t = (normalize (FStar_List.append steps ((Beta)::(WHNF)::[])) env t0)
in (let rec aux = (fun t -> (let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _189_484 = (let _189_483 = (let _189_482 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _189_482))
in FStar_Syntax_Syntax.Tm_refine (_189_483))
in (mk _189_484 t0.FStar_Syntax_Syntax.pos))
end
| _86_1180 -> begin
t
end))
end
| _86_1182 -> begin
t
end)))
in (aux t))))

let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(let _86_1193 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_86_1193) with
| (binders, cdef) -> begin
(let inst = (let _189_492 = (let _189_491 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_189_491)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _86_1197 _86_1201 -> (match ((_86_1197, _86_1201)) with
| ((x, _86_1196), (t, _86_1200)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _189_492))
in (let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (let c = (FStar_All.pipe_right (let _86_1204 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _86_1204.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _86_1204.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _86_1204.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _86_1207 _86_1209 _86_1211 -> (FStar_All.failwith "NYI: normalize_sigelt"))

let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _86_1213 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(let _86_1220 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_86_1220) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _86_1223 -> begin
(let _86_1226 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_86_1226) with
| (binders, args) -> begin
(let _189_505 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _189_504 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _189_503 -> Some (_189_503)))
in (FStar_Syntax_Util.abs binders _189_505 _189_504)))
end))
end)
end))
end
| _86_1228 -> begin
(let _189_508 = (let _189_507 = (FStar_Syntax_Print.tag_of_term t)
in (let _189_506 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _189_507 _189_506)))
in (FStar_All.failwith _189_508))
end))





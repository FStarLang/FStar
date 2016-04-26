
open Prims
# 42 "FStar.TypeChecker.Normalize.fst"
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

# 43 "FStar.TypeChecker.Normalize.fst"
let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))

# 44 "FStar.TypeChecker.Normalize.fst"
let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Normalize.fst"
let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.TypeChecker.Normalize.fst"
let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.TypeChecker.Normalize.fst"
let is_BetaUVars = (fun _discr_ -> (match (_discr_) with
| BetaUVars (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "FStar.TypeChecker.Normalize.fst"
let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.TypeChecker.Normalize.fst"
let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))

# 50 "FStar.TypeChecker.Normalize.fst"
let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Normalize.fst"
let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.TypeChecker.Normalize.fst"
let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.TypeChecker.Normalize.fst"
let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.TypeChecker.Normalize.fst"
let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.TypeChecker.Normalize.fst"
let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.TypeChecker.Normalize.fst"
let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.TypeChecker.Normalize.fst"
let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_8) -> begin
_53_8
end))

# 61 "FStar.TypeChecker.Normalize.fst"
type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list

# 62 "FStar.TypeChecker.Normalize.fst"
let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))

# 64 "FStar.TypeChecker.Normalize.fst"
let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.TypeChecker.Normalize.fst"
let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_53_11) -> begin
_53_11
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_14) -> begin
_53_14
end))

# 67 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_17, t, _53_20) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_24 -> begin
"dummy"
end))

# 71 "FStar.TypeChecker.Normalize.fst"
type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}

# 71 "FStar.TypeChecker.Normalize.fst"
let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))

# 77 "FStar.TypeChecker.Normalize.fst"
type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list

# 79 "FStar.TypeChecker.Normalize.fst"
type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

# 81 "FStar.TypeChecker.Normalize.fst"
type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)

# 82 "FStar.TypeChecker.Normalize.fst"
let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.TypeChecker.Normalize.fst"
let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_53_31) -> begin
_53_31
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_34) -> begin
_53_34
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_37) -> begin
_53_37
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_40) -> begin
_53_40
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_43) -> begin
_53_43
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_46) -> begin
_53_46
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_49) -> begin
_53_49
end))

# 90 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 103 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 104 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_55) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 109 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _142_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _142_173 (FStar_String.concat "; "))))

# 112 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_62, _53_64) -> begin
(closure_to_string c)
end
| MemoLazy (_53_68) -> begin
"MemoLazy"
end
| Abs (_53_71, bs, _53_74, _53_76, _53_78) -> begin
(let _142_176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _142_176))
end
| _53_82 -> begin
"Match"
end))

# 118 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _142_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _142_179 (FStar_String.concat "; "))))

# 121 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 126 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_89 -> begin
false
end))

# 130 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_96 -> begin
(let _142_195 = (let _142_194 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _142_194))
in (FStar_All.failwith _142_195))
end)

# 134 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 135 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _142_200 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _142_200 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 139 "FStar.TypeChecker.Normalize.fst"
let _53_109 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_109) with
| (binders, cdef) -> begin
(
# 140 "FStar.TypeChecker.Normalize.fst"
let inst = (let _142_204 = (let _142_203 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_142_203)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_113 _53_117 -> (match ((_53_113, _53_117)) with
| ((x, _53_112), (t, _53_116)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _142_204))
in (
# 141 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 142 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 142 "FStar.TypeChecker.Normalize.fst"
let _53_120 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_120.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_120.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_120.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 153 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 154 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 155 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 160 "FStar.TypeChecker.Normalize.fst"
let _53_141 = (FStar_List.fold_left (fun _53_132 u -> (match (_53_132) with
| (cur_kernel, cur_max, out) -> begin
(
# 162 "FStar.TypeChecker.Normalize.fst"
let _53_136 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_136) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_53_141) with
| (_53_138, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 173 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 174 "FStar.TypeChecker.Normalize.fst"
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
| _53_158 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_151 -> begin
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
(let _142_219 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _142_219 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _142_221 = (aux u)
in (FStar_List.map (fun _142_220 -> FStar_Syntax_Syntax.U_succ (_142_220)) _142_221))
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

# 212 "FStar.TypeChecker.Normalize.fst"
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (
# 213 "FStar.TypeChecker.Normalize.fst"
let _53_189 = (log cfg (fun _53_188 -> (match (()) with
| () -> begin
(let _142_245 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_244 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _142_245 _142_244)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _53_193 -> begin
(
# 217 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_196) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _142_251 = (let _142_250 = (let _142_249 = (closure_as_term_delayed cfg env t')
in (u, _142_249))
in FStar_Syntax_Syntax.Tm_uvar (_142_250))
in (mk _142_251 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _142_253 = (let _142_252 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_142_252))
in (mk _142_253 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _142_254 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _142_254))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_221) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_53_234) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 246 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _53_240) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _142_260 = (FStar_List.fold_left (fun env' _53_247 -> (match (_53_247) with
| (t, _53_246) -> begin
(let _142_259 = (let _142_258 = (let _142_257 = (FStar_Util.mk_ref None)
in (env, t, _142_257))
in Clos (_142_258))
in (_142_259)::env')
end)) env args)
in (closure_as_term cfg _142_260 body))
end
| _53_249 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _53_251 -> begin
(
# 253 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (
# 254 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 259 "FStar.TypeChecker.Normalize.fst"
let _53_261 = (closures_as_binders_delayed cfg env bs)
in (match (_53_261) with
| (bs, env) -> begin
(
# 260 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _142_263 = (let _142_262 = (let _142_261 = (close_lcomp_opt cfg env lopt)
in (bs, body, _142_261))
in FStar_Syntax_Syntax.Tm_abs (_142_262))
in (mk _142_263 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 264 "FStar.TypeChecker.Normalize.fst"
let _53_269 = (closures_as_binders_delayed cfg env bs)
in (match (_53_269) with
| (bs, env) -> begin
(
# 265 "FStar.TypeChecker.Normalize.fst"
let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 269 "FStar.TypeChecker.Normalize.fst"
let _53_277 = (let _142_265 = (let _142_264 = (FStar_Syntax_Syntax.mk_binder x)
in (_142_264)::[])
in (closures_as_binders_delayed cfg env _142_265))
in (match (_53_277) with
| (x, env) -> begin
(
# 270 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _142_269 = (let _142_268 = (let _142_267 = (let _142_266 = (FStar_List.hd x)
in (FStar_All.pipe_right _142_266 Prims.fst))
in (_142_267, phi))
in FStar_Syntax_Syntax.Tm_refine (_142_268))
in (mk _142_269 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _142_275 = (let _142_274 = (let _142_273 = (closure_as_term_delayed cfg env t1)
in (let _142_272 = (let _142_271 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _142_270 -> FStar_Util.Inl (_142_270)) _142_271))
in (_142_273, _142_272, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_142_274))
in (mk _142_275 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _142_281 = (let _142_280 = (let _142_279 = (closure_as_term_delayed cfg env t1)
in (let _142_278 = (let _142_277 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _142_276 -> FStar_Util.Inr (_142_276)) _142_277))
in (_142_279, _142_278, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_142_280))
in (mk _142_281 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _142_286 = (let _142_285 = (let _142_284 = (closure_as_term_delayed cfg env t')
in (let _142_283 = (let _142_282 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_142_282))
in (_142_284, _142_283)))
in FStar_Syntax_Syntax.Tm_meta (_142_285))
in (mk _142_286 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _142_289 = (let _142_288 = (let _142_287 = (closure_as_term_delayed cfg env t')
in (_142_287, m))
in FStar_Syntax_Syntax.Tm_meta (_142_288))
in (mk _142_289 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 287 "FStar.TypeChecker.Normalize.fst"
let env0 = env
in (
# 288 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env _53_309 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 289 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 290 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 291 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_315) -> begin
body
end
| FStar_Util.Inl (_53_318) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 294 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 294 "FStar.TypeChecker.Normalize.fst"
let _53_321 = lb
in {FStar_Syntax_Syntax.lbname = _53_321.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_321.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_321.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_325, lbs), body) -> begin
(
# 298 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 299 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _53_334 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 300 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_338 env -> (Dummy)::env) lbs env_univs)
end
in (
# 303 "FStar.TypeChecker.Normalize.fst"
let _53_342 = lb
in (let _142_301 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _142_300 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_342.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_342.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _142_301; FStar_Syntax_Syntax.lbeff = _53_342.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _142_300}))))))
in (
# 305 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 306 "FStar.TypeChecker.Normalize.fst"
let body = (
# 307 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _53_345 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 312 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 313 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _53_360 -> (match (_53_360) with
| (pat, w_opt, tm) -> begin
(
# 314 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_365) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 318 "FStar.TypeChecker.Normalize.fst"
let _53_375 = (norm_pat env hd)
in (match (_53_375) with
| (hd, env') -> begin
(
# 319 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _142_313 = (norm_pat env p)
in (Prims.fst _142_313)))))
in ((
# 320 "FStar.TypeChecker.Normalize.fst"
let _53_378 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_378.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_378.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 322 "FStar.TypeChecker.Normalize.fst"
let _53_395 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_386 _53_389 -> (match ((_53_386, _53_389)) with
| ((pats, env), (p, b)) -> begin
(
# 323 "FStar.TypeChecker.Normalize.fst"
let _53_392 = (norm_pat env p)
in (match (_53_392) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_53_395) with
| (pats, env) -> begin
((
# 325 "FStar.TypeChecker.Normalize.fst"
let _53_396 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _53_396.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_396.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 327 "FStar.TypeChecker.Normalize.fst"
let x = (
# 327 "FStar.TypeChecker.Normalize.fst"
let _53_400 = x
in (let _142_316 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_400.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_400.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_316}))
in ((
# 328 "FStar.TypeChecker.Normalize.fst"
let _53_403 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_403.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_403.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 330 "FStar.TypeChecker.Normalize.fst"
let x = (
# 330 "FStar.TypeChecker.Normalize.fst"
let _53_407 = x
in (let _142_317 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_407.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_407.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_317}))
in ((
# 331 "FStar.TypeChecker.Normalize.fst"
let _53_410 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_410.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_410.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 333 "FStar.TypeChecker.Normalize.fst"
let x = (
# 333 "FStar.TypeChecker.Normalize.fst"
let _53_416 = x
in (let _142_318 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_416.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_416.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_318}))
in (
# 334 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 335 "FStar.TypeChecker.Normalize.fst"
let _53_420 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _53_420.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_420.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 336 "FStar.TypeChecker.Normalize.fst"
let _53_424 = (norm_pat env pat)
in (match (_53_424) with
| (pat, env) -> begin
(
# 337 "FStar.TypeChecker.Normalize.fst"
let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _142_319 = (closure_as_term cfg env w)
in Some (_142_319))
end)
in (
# 340 "FStar.TypeChecker.Normalize.fst"
let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _142_322 = (let _142_321 = (let _142_320 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _142_320))
in FStar_Syntax_Syntax.Tm_match (_142_321))
in (mk _142_322 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _53_434 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _53_437 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _53_443 -> begin
(FStar_List.map (fun _53_446 -> (match (_53_446) with
| (x, imp) -> begin
(let _142_330 = (closure_as_term_delayed cfg env x)
in (_142_330, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (
# 357 "FStar.TypeChecker.Normalize.fst"
let _53_462 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_452 _53_455 -> (match ((_53_452, _53_455)) with
| ((env, out), (b, imp)) -> begin
(
# 358 "FStar.TypeChecker.Normalize.fst"
let b = (
# 358 "FStar.TypeChecker.Normalize.fst"
let _53_456 = b
in (let _142_336 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_456.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_456.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_336}))
in (
# 359 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_53_462) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _53_468 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _142_340 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _142_340))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _142_341 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _142_341))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 371 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 372 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 373 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _142_343 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_142_343))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 376 "FStar.TypeChecker.Normalize.fst"
let _53_482 = c
in {FStar_Syntax_Syntax.effect_name = _53_482.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(let _142_351 = (let _142_350 = (
# 381 "FStar.TypeChecker.Normalize.fst"
let _53_490 = lc
in (let _142_349 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _53_490.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _142_349; FStar_Syntax_Syntax.cflags = _53_490.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_492 -> (match (()) with
| () -> begin
(let _142_348 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _142_348))
end))}))
in FStar_Util.Inl (_142_350))
in Some (_142_351))
end
| _53_494 -> begin
lopt
end))

# 389 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 390 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 390 "FStar.TypeChecker.Normalize.fst"
let _53_499 = t
in {FStar_Syntax_Syntax.n = _53_499.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_499.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_499.FStar_Syntax_Syntax.vars}))
in (
# 391 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_508 -> begin
None
end))
in (
# 395 "FStar.TypeChecker.Normalize.fst"
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
| _53_586 -> begin
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
| _53_629 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _53_656)::(_53_647, (arg, _53_650))::[] -> begin
arg
end
| _53_660 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _53_664)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _53_670)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_674 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _142_362 = (FStar_Syntax_Subst.compress t)
in _142_362.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_692::[], body, _53_696) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_704 -> begin
tm
end)
end
| _53_706 -> begin
tm
end)
end
| _53_708 -> begin
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
| _53_710 -> begin
tm
end)
end))))

# 448 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 450 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 451 "FStar.TypeChecker.Normalize.fst"
let _53_717 = (log cfg (fun _53_716 -> (match (()) with
| () -> begin
(let _142_392 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_391 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _142_392 _142_391)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_720) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 466 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _142_396 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_396)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 472 "FStar.TypeChecker.Normalize.fst"
let us = (let _142_398 = (let _142_397 = (FStar_List.map (norm_universe cfg env) us)
in (_142_397, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_142_398))
in (
# 473 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(
# 477 "FStar.TypeChecker.Normalize.fst"
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
# 487 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _53_782)::stack -> begin
(
# 491 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_790 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_792 -> begin
(let _142_402 = (let _142_401 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _142_401))
in (FStar_All.failwith _142_402))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_796) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 506 "FStar.TypeChecker.Normalize.fst"
let _53_809 = (log cfg (fun _53_808 -> (match (()) with
| () -> begin
(let _142_405 = (FStar_Syntax_Print.term_to_string t)
in (let _142_404 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _142_405 _142_404)))
end)))
in (match ((let _142_406 = (FStar_Syntax_Subst.compress t')
in _142_406.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_812) -> begin
(norm cfg env stack t')
end
| _53_815 -> begin
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
| Meta (_53_825)::_53_823 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_53_831)::_53_829 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_53_837)::_53_835 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _53_843, _53_845)::stack -> begin
(match (c) with
| Univ (_53_850) -> begin
(norm cfg ((c)::env) stack t)
end
| _53_853 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _53_856::[] -> begin
(match (lopt) with
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(
# 545 "FStar.TypeChecker.Normalize.fst"
let _53_862 = (log cfg (fun _53_861 -> (match (()) with
| () -> begin
(let _142_408 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_408))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(
# 549 "FStar.TypeChecker.Normalize.fst"
let _53_868 = (log cfg (fun _53_867 -> (match (()) with
| () -> begin
(let _142_410 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_410))
end)))
in (norm cfg ((c)::env) stack body))
end
| _53_871 -> begin
(
# 554 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 554 "FStar.TypeChecker.Normalize.fst"
let _53_872 = cfg
in {steps = (WHNF)::cfg.steps; tcenv = _53_872.tcenv; delta_level = _53_872.delta_level})
in (let _142_411 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_411)))
end)
end
| _53_877::tl -> begin
(
# 558 "FStar.TypeChecker.Normalize.fst"
let _53_880 = (log cfg (fun _53_879 -> (match (()) with
| () -> begin
(let _142_413 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_413))
end)))
in (
# 559 "FStar.TypeChecker.Normalize.fst"
let body = (mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack body)))
end)
end)
end
| MemoLazy (r)::stack -> begin
(
# 565 "FStar.TypeChecker.Normalize.fst"
let _53_887 = (set_memo r (env, t))
in (
# 566 "FStar.TypeChecker.Normalize.fst"
let _53_890 = (log cfg (fun _53_889 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_415 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_415))
end else begin
(
# 574 "FStar.TypeChecker.Normalize.fst"
let _53_908 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_908) with
| (bs, body, opening) -> begin
(
# 575 "FStar.TypeChecker.Normalize.fst"
let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _142_421 = (let _142_419 = (let _142_417 = (let _142_416 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _142_416))
in (FStar_All.pipe_right _142_417 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _142_419 (fun _142_418 -> FStar_Util.Inl (_142_418))))
in (FStar_All.pipe_right _142_421 (fun _142_420 -> Some (_142_420))))
end
| _53_913 -> begin
lopt
end)
in (
# 578 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_916 -> (Dummy)::env) env))
in (
# 579 "FStar.TypeChecker.Normalize.fst"
let _53_920 = (log cfg (fun _53_919 -> (match (()) with
| () -> begin
(let _142_425 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _142_425))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 584 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_928 stack -> (match (_53_928) with
| (a, aq) -> begin
(let _142_432 = (let _142_431 = (let _142_430 = (let _142_429 = (let _142_428 = (FStar_Util.mk_ref None)
in (env, a, _142_428))
in Clos (_142_429))
in (_142_430, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_142_431))
in (_142_432)::stack)
end)) args))
in (
# 585 "FStar.TypeChecker.Normalize.fst"
let _53_932 = (log cfg (fun _53_931 -> (match (()) with
| () -> begin
(let _142_434 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _142_434))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(
# 592 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 593 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_refine (((
# 593 "FStar.TypeChecker.Normalize.fst"
let _53_942 = x
in {FStar_Syntax_Syntax.ppname = _53_942.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_942.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_946 -> begin
(let _142_435 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_435))
end)
end else begin
(
# 596 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 597 "FStar.TypeChecker.Normalize.fst"
let _53_950 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_53_950) with
| (closing, f) -> begin
(
# 598 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 599 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_438 = (let _142_437 = (let _142_436 = (FStar_Syntax_Subst.close closing f)
in ((
# 599 "FStar.TypeChecker.Normalize.fst"
let _53_952 = x
in {FStar_Syntax_Syntax.ppname = _53_952.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_952.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _142_436))
in FStar_Syntax_Syntax.Tm_refine (_142_437))
in (mk _142_438 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_439 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_439))
end else begin
(
# 605 "FStar.TypeChecker.Normalize.fst"
let _53_961 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_961) with
| (bs, c) -> begin
(
# 606 "FStar.TypeChecker.Normalize.fst"
let c = (let _142_442 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_963 -> (Dummy)::env) env))
in (norm_comp cfg _142_442 c))
in (
# 607 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_443 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _142_443 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _53_991 -> begin
(
# 616 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 617 "FStar.TypeChecker.Normalize.fst"
let _53_994 = (log cfg (fun _53_993 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 618 "FStar.TypeChecker.Normalize.fst"
let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _142_445 = (norm cfg env [] t)
in FStar_Util.Inl (_142_445))
end
| FStar_Util.Inr (c) -> begin
(let _142_446 = (norm_comp cfg env c)
in FStar_Util.Inr (_142_446))
end)
in (let _142_447 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, tc, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_447)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 625 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 629 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_450 = (let _142_449 = (let _142_448 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _142_448))
in Clos (_142_449))
in (_142_450)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_53_1015, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1027); FStar_Syntax_Syntax.lbunivs = _53_1025; FStar_Syntax_Syntax.lbtyp = _53_1023; FStar_Syntax_Syntax.lbeff = _53_1021; FStar_Syntax_Syntax.lbdef = _53_1019}::_53_1017), _53_1033) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 646 "FStar.TypeChecker.Normalize.fst"
let _53_1055 = (FStar_List.fold_right (fun lb _53_1044 -> (match (_53_1044) with
| (rec_env, memos, i) -> begin
(
# 647 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _142_453 = (
# 647 "FStar.TypeChecker.Normalize.fst"
let _53_1045 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1045.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1045.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _142_453))
in (
# 648 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 649 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 650 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_53_1055) with
| (rec_env, memos, _53_1054) -> begin
(
# 652 "FStar.TypeChecker.Normalize.fst"
let _53_1058 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 653 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _142_460 = (let _142_459 = (let _142_458 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _142_458))
in Clos (_142_459))
in (_142_460)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _53_1070::_53_1068 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1075) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 665 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _53_1082 -> begin
(norm cfg env stack head)
end)
end
| _53_1084 -> begin
(
# 672 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 673 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _142_461 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_142_461))
end
| _53_1089 -> begin
m
end)
in (
# 677 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1097 -> (match (_53_1097) with
| (a, imp) -> begin
(let _142_466 = (norm cfg env [] a)
in (_142_466, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (
# 686 "FStar.TypeChecker.Normalize.fst"
let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 689 "FStar.TypeChecker.Normalize.fst"
let _53_1104 = comp
in (let _142_471 = (let _142_470 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_142_470))
in {FStar_Syntax_Syntax.n = _142_471; FStar_Syntax_Syntax.tk = _53_1104.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1104.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1104.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 692 "FStar.TypeChecker.Normalize.fst"
let _53_1108 = comp
in (let _142_473 = (let _142_472 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_142_472))
in {FStar_Syntax_Syntax.n = _142_473; FStar_Syntax_Syntax.tk = _53_1108.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1108.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1108.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 695 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1116 -> (match (_53_1116) with
| (a, i) -> begin
(let _142_477 = (norm cfg env [] a)
in (_142_477, i))
end)))))
in (
# 696 "FStar.TypeChecker.Normalize.fst"
let _53_1117 = comp
in (let _142_481 = (let _142_480 = (
# 696 "FStar.TypeChecker.Normalize.fst"
let _53_1119 = ct
in (let _142_479 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _142_478 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1119.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _142_479; FStar_Syntax_Syntax.effect_args = _142_478; FStar_Syntax_Syntax.flags = _53_1119.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_142_480))
in {FStar_Syntax_Syntax.n = _142_481; FStar_Syntax_Syntax.tk = _53_1117.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1117.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1117.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (
# 703 "FStar.TypeChecker.Normalize.fst"
let norm = (fun t -> (norm (
# 704 "FStar.TypeChecker.Normalize.fst"
let _53_1126 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]; tcenv = _53_1126.tcenv; delta_level = _53_1126.delta_level}) env [] t))
in (
# 705 "FStar.TypeChecker.Normalize.fst"
let non_info = (fun t -> (let _142_489 = (norm t)
in (FStar_Syntax_Util.non_informative _142_489)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_1131) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(
# 708 "FStar.TypeChecker.Normalize.fst"
let _53_1135 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_1135.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1135.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1135.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 710 "FStar.TypeChecker.Normalize.fst"
let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(
# 713 "FStar.TypeChecker.Normalize.fst"
let ct = if (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_Ghost_lid) then begin
(
# 715 "FStar.TypeChecker.Normalize.fst"
let _53_1140 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_Pure_lid; FStar_Syntax_Syntax.result_typ = _53_1140.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1140.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1140.FStar_Syntax_Syntax.flags})
end else begin
if (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_GTot_lid) then begin
(
# 717 "FStar.TypeChecker.Normalize.fst"
let _53_1142 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.result_typ = _53_1142.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1142.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1142.FStar_Syntax_Syntax.flags})
end else begin
if (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_GHOST_lid) then begin
(
# 719 "FStar.TypeChecker.Normalize.fst"
let _53_1144 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1144.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1144.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1144.FStar_Syntax_Syntax.flags})
end else begin
(
# 720 "FStar.TypeChecker.Normalize.fst"
let ct = (unfold_effect_abbrev cfg.tcenv c)
in (
# 721 "FStar.TypeChecker.Normalize.fst"
let _53_1147 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_1147.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1147.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_1147.FStar_Syntax_Syntax.flags}))
end
end
end
in (
# 722 "FStar.TypeChecker.Normalize.fst"
let _53_1150 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_1150.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1150.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1150.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1153 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1158 -> (match (_53_1158) with
| (x, imp) -> begin
(let _142_494 = (
# 728 "FStar.TypeChecker.Normalize.fst"
let _53_1159 = x
in (let _142_493 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1159.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_493}))
in (_142_494, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 732 "FStar.TypeChecker.Normalize.fst"
let _53_1172 = (FStar_List.fold_left (fun _53_1166 b -> (match (_53_1166) with
| (nbs', env) -> begin
(
# 733 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_53_1172) with
| (nbs, _53_1171) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 747 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 751 "FStar.TypeChecker.Normalize.fst"
let _53_1189 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 755 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 756 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _142_504 = (
# 757 "FStar.TypeChecker.Normalize.fst"
let _53_1202 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1202.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1202.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1202.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _142_504))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 763 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 767 "FStar.TypeChecker.Normalize.fst"
let _53_1245 = (log cfg (fun _53_1244 -> (match (()) with
| () -> begin
(let _142_506 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _142_506))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 772 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 773 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 775 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1252, a) -> begin
(
# 779 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 784 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _142_507 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _142_507)))
end
| Match (env, branches, r)::stack -> begin
(
# 788 "FStar.TypeChecker.Normalize.fst"
let _53_1273 = (log cfg (fun _53_1272 -> (match (()) with
| () -> begin
(let _142_509 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _142_509))
end)))
in (
# 789 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _53_1276 -> (match (()) with
| () -> begin
(
# 790 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 791 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 791 "FStar.TypeChecker.Normalize.fst"
let _53_1278 = cfg
in (let _142_512 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _53_1278.steps; tcenv = _53_1278.tcenv; delta_level = _142_512}))
in (
# 792 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 796 "FStar.TypeChecker.Normalize.fst"
let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1286 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 800 "FStar.TypeChecker.Normalize.fst"
let _53_1291 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1291) with
| (p, wopt, e) -> begin
(
# 801 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_520 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _142_520 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 803 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _142_521 = (norm_or_whnf env w)
in Some (_142_521))
end)
in (
# 806 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _142_522 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _142_522))))))
end))
in (
# 810 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1305) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1330 -> begin
false
end))
in (
# 817 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 821 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 822 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 826 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 830 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 831 "FStar.TypeChecker.Normalize.fst"
let _53_1347 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1347) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 834 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 835 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1353) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1370) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1377 -> begin
(let _142_539 = (not ((is_cons head)))
in FStar_Util.Inr (_142_539))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _142_540 = (FStar_Syntax_Util.un_uinst head)
in _142_540.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1385 -> begin
(let _142_541 = (not ((is_cons head)))
in FStar_Util.Inr (_142_541))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _53_1395)::rest_a, (p, _53_1401)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1409 -> begin
FStar_Util.Inr (false)
end))
in (
# 868 "FStar.TypeChecker.Normalize.fst"
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
# 879 "FStar.TypeChecker.Normalize.fst"
let _53_1427 = (log cfg (fun _53_1426 -> (match (()) with
| () -> begin
(let _142_552 = (FStar_Syntax_Print.pat_to_string p)
in (let _142_551 = (let _142_550 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _142_550 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _142_552 _142_551)))
end)))
in (
# 884 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env t -> (let _142_557 = (let _142_556 = (let _142_555 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _142_555))
in Clos (_142_556))
in (_142_557)::env)) env s)
in (let _142_558 = (guard_when_clause wopt b rest)
in (norm cfg env stack _142_558))))
end)
end))
in (matches t branches)))))))
end))

# 889 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 890 "FStar.TypeChecker.Normalize.fst"
let d = (match ((FStar_Util.find_map s (fun _53_5 -> (match (_53_5) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1438 -> begin
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

# 897 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _142_570 = (config s e)
in (norm _142_570 [] [] t)))

# 898 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _142_577 = (config s e)
in (norm_comp _142_577 [] t)))

# 899 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _142_582 = (config [] env)
in (norm_universe _142_582 [] u)))

# 900 "FStar.TypeChecker.Normalize.fst"
let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _142_587 = (config [] env)
in (ghost_to_pure_aux _142_587 [] c)))

# 902 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _142_592 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _142_592)))

# 903 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _142_598 = (let _142_597 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _142_597 [] c))
in (FStar_Syntax_Print.comp_to_string _142_598)))

# 905 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 906 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 907 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 908 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 911 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _142_609 = (let _142_608 = (let _142_607 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _142_607))
in FStar_Syntax_Syntax.Tm_refine (_142_608))
in (mk _142_609 t0.FStar_Syntax_Syntax.pos))
end
| _53_1474 -> begin
t
end))
end
| _53_1476 -> begin
t
end)))
in (aux t))))

# 920 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _53_1477 _53_1479 _53_1481 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 922 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _53_1483 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 925 "FStar.TypeChecker.Normalize.fst"
let _53_1490 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_53_1490) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1493 -> begin
(
# 929 "FStar.TypeChecker.Normalize.fst"
let _53_1496 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1496) with
| (binders, args) -> begin
(let _142_624 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _142_623 = (let _142_622 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _142_620 -> FStar_Util.Inl (_142_620)))
in (FStar_All.pipe_right _142_622 (fun _142_621 -> Some (_142_621))))
in (FStar_Syntax_Util.abs binders _142_624 _142_623)))
end))
end)
end))
end
| _53_1498 -> begin
(let _142_627 = (let _142_626 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_625 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _142_626 _142_625)))
in (FStar_All.failwith _142_627))
end))





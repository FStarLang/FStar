
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
let ___UnfoldUntil____0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_66_9) -> begin
_66_9
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
let ___Clos____0 : closure  ->  (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) = (fun projectee -> (match (projectee) with
| Clos (_66_12) -> begin
_66_12
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_66_15) -> begin
_66_15
end))

# 67 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _66_1 -> (match (_66_1) with
| Clos (_66_18, t, _66_21) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _66_25 -> begin
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
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range)
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
let ___Arg____0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_66_32) -> begin
_66_32
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_66_35) -> begin
_66_35
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_66_38) -> begin
_66_38
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_66_41) -> begin
_66_41
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_66_44) -> begin
_66_44
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___App____0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_66_47) -> begin
_66_47
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_66_50) -> begin
_66_50
end))

# 90 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 102 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 103 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_66_56) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 108 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_173 (FStar_String.concat "; "))))

# 111 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _66_2 -> (match (_66_2) with
| Arg (c, _66_63, _66_65) -> begin
(closure_to_string c)
end
| MemoLazy (_66_69) -> begin
"MemoLazy"
end
| Abs (_66_72, bs, _66_75, _66_77, _66_79) -> begin
(let _147_176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_176))
end
| _66_83 -> begin
"Match"
end))

# 117 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_179 (FStar_String.concat "; "))))

# 120 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 125 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _66_3 -> (match (_66_3) with
| [] -> begin
true
end
| _66_90 -> begin
false
end))

# 129 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _66_94 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _66_93 -> (match (_66_93) with
| _66_97 -> begin
(let _147_195 = (let _147_194 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_194))
in (FStar_All.failwith _147_195))
end))))

# 141 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 143 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 148 "FStar.TypeChecker.Normalize.fst"
let _66_118 = (FStar_List.fold_left (fun _66_109 u -> (match (_66_109) with
| (cur_kernel, cur_max, out) -> begin
(
# 150 "FStar.TypeChecker.Normalize.fst"
let _66_113 = (FStar_Syntax_Util.univ_kernel u)
in (match (_66_113) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_66_118) with
| (_66_115, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 161 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 162 "FStar.TypeChecker.Normalize.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _66_125 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| Dummy -> begin
(u)::[]
end
| _66_135 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _66_124 -> (match (_66_124) with
| _66_128 -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses)) then begin
(FStar_Syntax_Syntax.U_unknown)::[]
end else begin
(FStar_All.failwith "Universe variable not found")
end
end)))
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _147_210 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_210 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_212 = (aux u)
in (FStar_List.map (fun _147_211 -> FStar_Syntax_Syntax.U_succ (_147_211)) _147_212))
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

# 200 "FStar.TypeChecker.Normalize.fst"
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _66_167 -> begin
(
# 204 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_170) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _147_239 = (let _147_238 = (let _147_237 = (closure_as_term_delayed cfg env t')
in (u, _147_237))
in FStar_Syntax_Syntax.Tm_uvar (_147_238))
in (mk _147_239 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_241 = (let _147_240 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_240))
in (mk _147_241 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_242 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_242))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_195) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_66_208) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 233 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _66_214) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _147_248 = (FStar_List.fold_left (fun env' _66_221 -> (match (_66_221) with
| (t, _66_220) -> begin
(let _147_247 = (let _147_246 = (let _147_245 = (FStar_Util.mk_ref None)
in (env, t, _147_245))
in Clos (_147_246))
in (_147_247)::env')
end)) env args)
in (closure_as_term cfg _147_248 body))
end
| _66_223 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _66_225 -> begin
(
# 240 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (
# 241 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 246 "FStar.TypeChecker.Normalize.fst"
let _66_235 = (closures_as_binders_delayed cfg env bs)
in (match (_66_235) with
| (bs, env) -> begin
(
# 247 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _147_251 = (let _147_250 = (let _147_249 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _147_249))
in FStar_Syntax_Syntax.Tm_abs (_147_250))
in (mk _147_251 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 251 "FStar.TypeChecker.Normalize.fst"
let _66_243 = (closures_as_binders_delayed cfg env bs)
in (match (_66_243) with
| (bs, env) -> begin
(
# 252 "FStar.TypeChecker.Normalize.fst"
let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 256 "FStar.TypeChecker.Normalize.fst"
let _66_251 = (let _147_253 = (let _147_252 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_252)::[])
in (closures_as_binders_delayed cfg env _147_253))
in (match (_66_251) with
| (x, env) -> begin
(
# 257 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _147_257 = (let _147_256 = (let _147_255 = (let _147_254 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_254 Prims.fst))
in (_147_255, phi))
in FStar_Syntax_Syntax.Tm_refine (_147_256))
in (mk _147_257 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _147_261 = (let _147_260 = (let _147_259 = (closure_as_term_delayed cfg env t1)
in (let _147_258 = (closure_as_term_delayed cfg env t2)
in (_147_259, _147_258, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_147_260))
in (mk _147_261 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_264 = (let _147_263 = (let _147_262 = (closure_as_term_delayed cfg env t')
in (_147_262, m))
in FStar_Syntax_Syntax.Tm_meta (_147_263))
in (mk _147_264 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 267 "FStar.TypeChecker.Normalize.fst"
let env0 = env
in (
# 268 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env _66_271 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 269 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 270 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 271 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_66_277) -> begin
body
end
| FStar_Util.Inl (_66_280) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 274 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 274 "FStar.TypeChecker.Normalize.fst"
let _66_283 = lb
in {FStar_Syntax_Syntax.lbname = _66_283.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _66_283.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _66_283.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_66_287, lbs), body) -> begin
(
# 278 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 279 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _66_296 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 280 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _66_300 env -> (Dummy)::env) lbs env_univs)
end
in (
# 283 "FStar.TypeChecker.Normalize.fst"
let _66_304 = lb
in (let _147_276 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_275 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _66_304.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _66_304.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_276; FStar_Syntax_Syntax.lbeff = _66_304.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_275}))))))
in (
# 285 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 286 "FStar.TypeChecker.Normalize.fst"
let body = (
# 287 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _66_307 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 292 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 293 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _66_322 -> (match (_66_322) with
| (pat, w_opt, tm) -> begin
(
# 294 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_66_327) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 298 "FStar.TypeChecker.Normalize.fst"
let _66_337 = (norm_pat env hd)
in (match (_66_337) with
| (hd, env') -> begin
(
# 299 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_288 = (norm_pat env p)
in (Prims.fst _147_288)))))
in ((
# 300 "FStar.TypeChecker.Normalize.fst"
let _66_340 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _66_340.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_340.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 302 "FStar.TypeChecker.Normalize.fst"
let _66_357 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _66_348 _66_351 -> (match ((_66_348, _66_351)) with
| ((pats, env), (p, b)) -> begin
(
# 303 "FStar.TypeChecker.Normalize.fst"
let _66_354 = (norm_pat env p)
in (match (_66_354) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_66_357) with
| (pats, env) -> begin
((
# 305 "FStar.TypeChecker.Normalize.fst"
let _66_358 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _66_358.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_358.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 307 "FStar.TypeChecker.Normalize.fst"
let x = (
# 307 "FStar.TypeChecker.Normalize.fst"
let _66_362 = x
in (let _147_291 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_362.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_362.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_291}))
in ((
# 308 "FStar.TypeChecker.Normalize.fst"
let _66_365 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _66_365.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_365.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 310 "FStar.TypeChecker.Normalize.fst"
let x = (
# 310 "FStar.TypeChecker.Normalize.fst"
let _66_369 = x
in (let _147_292 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_369.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_369.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_292}))
in ((
# 311 "FStar.TypeChecker.Normalize.fst"
let _66_372 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _66_372.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_372.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 313 "FStar.TypeChecker.Normalize.fst"
let x = (
# 313 "FStar.TypeChecker.Normalize.fst"
let _66_378 = x
in (let _147_293 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_378.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_378.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_293}))
in (
# 314 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 315 "FStar.TypeChecker.Normalize.fst"
let _66_382 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _66_382.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_382.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 316 "FStar.TypeChecker.Normalize.fst"
let _66_386 = (norm_pat env pat)
in (match (_66_386) with
| (pat, env) -> begin
(
# 317 "FStar.TypeChecker.Normalize.fst"
let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_294 = (closure_as_term cfg env w)
in Some (_147_294))
end)
in (
# 320 "FStar.TypeChecker.Normalize.fst"
let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _147_297 = (let _147_296 = (let _147_295 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _147_295))
in FStar_Syntax_Syntax.Tm_match (_147_296))
in (mk _147_297 t.FStar_Syntax_Syntax.pos))))
end))
end))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _66_396 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _66_399 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _66_405 -> begin
(FStar_List.map (fun _66_408 -> (match (_66_408) with
| (x, imp) -> begin
(let _147_305 = (closure_as_term_delayed cfg env x)
in (_147_305, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * closure Prims.list) = (fun cfg env bs -> (
# 337 "FStar.TypeChecker.Normalize.fst"
let _66_424 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _66_414 _66_417 -> (match ((_66_414, _66_417)) with
| ((env, out), (b, imp)) -> begin
(
# 338 "FStar.TypeChecker.Normalize.fst"
let b = (
# 338 "FStar.TypeChecker.Normalize.fst"
let _66_418 = b
in (let _147_311 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_418.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_418.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_311}))
in (
# 339 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_66_424) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _66_430 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _147_315 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _147_315))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _147_316 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _147_316))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 351 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 352 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 353 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _66_4 -> (match (_66_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_318 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_318))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 356 "FStar.TypeChecker.Normalize.fst"
let _66_444 = c
in {FStar_Syntax_Syntax.effect_name = _66_444.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _66_5 -> (match (_66_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _147_325 = (
# 362 "FStar.TypeChecker.Normalize.fst"
let _66_452 = lc
in (let _147_324 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _66_452.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _147_324; FStar_Syntax_Syntax.cflags = _66_452.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _66_454 -> (match (()) with
| () -> begin
(let _147_323 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _147_323))
end))}))
in Some (_147_325))
end))

# 369 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 370 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 370 "FStar.TypeChecker.Normalize.fst"
let _66_459 = t
in {FStar_Syntax_Syntax.n = _66_459.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_459.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_459.FStar_Syntax_Syntax.vars}))
in (
# 371 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _66_468 -> begin
None
end))
in (
# 375 "FStar.TypeChecker.Normalize.fst"
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
| _66_546 -> begin
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
| _66_589 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _66_616)::(_66_607, (arg, _66_610))::[] -> begin
arg
end
| _66_620 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _66_624)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _66_630)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _66_634 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _147_336 = (FStar_Syntax_Subst.compress t)
in _147_336.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_652::[], body, _66_656) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _66_664 -> begin
tm
end)
end
| _66_666 -> begin
tm
end)
end
| _66_668 -> begin
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
| _66_670 -> begin
tm
end)
end))))

# 428 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 430 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 431 "FStar.TypeChecker.Normalize.fst"
let _66_677 = (log cfg (fun _66_676 -> (match (()) with
| () -> begin
(let _147_363 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_362 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_363 _147_362)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_680) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 445 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _147_367 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_367)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 451 "FStar.TypeChecker.Normalize.fst"
let us = (let _147_369 = (let _147_368 = (FStar_List.map (norm_universe cfg env) us)
in (_147_368, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_147_369))
in (
# 452 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(
# 459 "FStar.TypeChecker.Normalize.fst"
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
# 469 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _66_741)::stack -> begin
(
# 473 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _66_749 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _66_751 -> begin
(let _147_373 = (let _147_372 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_372))
in (FStar_All.failwith _147_373))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_755) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 488 "FStar.TypeChecker.Normalize.fst"
let _66_768 = (log cfg (fun _66_767 -> (match (()) with
| () -> begin
(let _147_376 = (FStar_Syntax_Print.term_to_string t)
in (let _147_375 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_376 _147_375)))
end)))
in (match ((let _147_377 = (FStar_Syntax_Subst.compress t')
in _147_377.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_771) -> begin
(norm cfg env stack t')
end
| _66_774 -> begin
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
| Meta (_66_784)::_66_782 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_66_790)::_66_788 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_66_796)::_66_794 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _66_802, _66_804)::stack -> begin
(match (c) with
| Univ (_66_809) -> begin
(norm cfg ((c)::env) stack t)
end
| _66_812 -> begin
(
# 516 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _66_815::[] -> begin
body
end
| _66_819::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 520 "FStar.TypeChecker.Normalize.fst"
let _66_823 = (log cfg (fun _66_822 -> (match (()) with
| () -> begin
(let _147_379 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_379))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 525 "FStar.TypeChecker.Normalize.fst"
let _66_829 = (set_memo r (env, t))
in (
# 526 "FStar.TypeChecker.Normalize.fst"
let _66_832 = (log cfg (fun _66_831 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_381 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_381))
end else begin
(
# 534 "FStar.TypeChecker.Normalize.fst"
let _66_849 = (FStar_Syntax_Subst.open_term bs body)
in (match (_66_849) with
| (bs, body) -> begin
(
# 535 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_851 -> (Dummy)::env) env))
in (
# 536 "FStar.TypeChecker.Normalize.fst"
let _66_855 = (log cfg (fun _66_854 -> (match (()) with
| () -> begin
(let _147_385 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_385))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 541 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _66_863 stack -> (match (_66_863) with
| (a, aq) -> begin
(let _147_392 = (let _147_391 = (let _147_390 = (let _147_389 = (let _147_388 = (FStar_Util.mk_ref None)
in (env, a, _147_388))
in Clos (_147_389))
in (_147_390, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_147_391))
in (_147_392)::stack)
end)) args))
in (
# 542 "FStar.TypeChecker.Normalize.fst"
let _66_867 = (log cfg (fun _66_866 -> (match (()) with
| () -> begin
(let _147_394 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_394))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(
# 549 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 550 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_refine (((
# 550 "FStar.TypeChecker.Normalize.fst"
let _66_877 = x
in {FStar_Syntax_Syntax.ppname = _66_877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_877.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _66_881 -> begin
(let _147_395 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_395))
end)
end else begin
(
# 553 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 554 "FStar.TypeChecker.Normalize.fst"
let _66_885 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_66_885) with
| (closing, f) -> begin
(
# 555 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 556 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_398 = (let _147_397 = (let _147_396 = (FStar_Syntax_Subst.close closing f)
in ((
# 556 "FStar.TypeChecker.Normalize.fst"
let _66_887 = x
in {FStar_Syntax_Syntax.ppname = _66_887.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_887.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _147_396))
in FStar_Syntax_Syntax.Tm_refine (_147_397))
in (mk _147_398 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_399 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_399))
end else begin
(
# 562 "FStar.TypeChecker.Normalize.fst"
let _66_896 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_66_896) with
| (bs, c) -> begin
(
# 563 "FStar.TypeChecker.Normalize.fst"
let c = (let _147_402 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_898 -> (Dummy)::env) env))
in (norm_comp cfg _147_402 c))
in (
# 564 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_403 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_403 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _66_926 -> begin
(
# 573 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 574 "FStar.TypeChecker.Normalize.fst"
let _66_929 = (log cfg (fun _66_928 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 575 "FStar.TypeChecker.Normalize.fst"
let t2 = (norm cfg env [] t2)
in (let _147_405 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_405)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 582 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 586 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_408 = (let _147_407 = (let _147_406 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _147_406))
in Clos (_147_407))
in (_147_408)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_66_946, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_66_958); FStar_Syntax_Syntax.lbunivs = _66_956; FStar_Syntax_Syntax.lbtyp = _66_954; FStar_Syntax_Syntax.lbeff = _66_952; FStar_Syntax_Syntax.lbdef = _66_950}::_66_948), _66_964) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 603 "FStar.TypeChecker.Normalize.fst"
let _66_986 = (FStar_List.fold_right (fun lb _66_975 -> (match (_66_975) with
| (rec_env, memos, i) -> begin
(
# 604 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _147_411 = (
# 604 "FStar.TypeChecker.Normalize.fst"
let _66_976 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _66_976.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _66_976.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_411))
in (
# 605 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 606 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 607 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_66_986) with
| (rec_env, memos, _66_985) -> begin
(
# 609 "FStar.TypeChecker.Normalize.fst"
let _66_989 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 610 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _147_418 = (let _147_417 = (let _147_416 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _147_416))
in Clos (_147_417))
in (_147_418)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _66_1001::_66_999 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _66_1006) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 622 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _66_1013 -> begin
(norm cfg env stack head)
end)
end
| _66_1015 -> begin
(
# 629 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 630 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_419 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_419))
end
| _66_1020 -> begin
m
end)
in (
# 634 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _66_1028 -> (match (_66_1028) with
| (a, imp) -> begin
(let _147_424 = (norm cfg env [] a)
in (_147_424, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 645 "FStar.TypeChecker.Normalize.fst"
let _66_1034 = comp
in (let _147_429 = (let _147_428 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_147_428))
in {FStar_Syntax_Syntax.n = _147_429; FStar_Syntax_Syntax.tk = _66_1034.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1034.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1034.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 648 "FStar.TypeChecker.Normalize.fst"
let _66_1038 = comp
in (let _147_431 = (let _147_430 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_147_430))
in {FStar_Syntax_Syntax.n = _147_431; FStar_Syntax_Syntax.tk = _66_1038.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1038.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1038.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 651 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _66_1046 -> (match (_66_1046) with
| (a, i) -> begin
(let _147_435 = (norm cfg env [] a)
in (_147_435, i))
end)))))
in (
# 652 "FStar.TypeChecker.Normalize.fst"
let _66_1047 = comp
in (let _147_439 = (let _147_438 = (
# 652 "FStar.TypeChecker.Normalize.fst"
let _66_1049 = ct
in (let _147_437 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_436 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _66_1049.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_437; FStar_Syntax_Syntax.effect_args = _147_436; FStar_Syntax_Syntax.flags = _66_1049.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_147_438))
in {FStar_Syntax_Syntax.n = _147_439; FStar_Syntax_Syntax.tk = _66_1047.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1047.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1047.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _66_1055 -> (match (_66_1055) with
| (x, imp) -> begin
(let _147_444 = (
# 656 "FStar.TypeChecker.Normalize.fst"
let _66_1056 = x
in (let _147_443 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_1056.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1056.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_443}))
in (_147_444, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 660 "FStar.TypeChecker.Normalize.fst"
let _66_1069 = (FStar_List.fold_left (fun _66_1063 b -> (match (_66_1063) with
| (nbs', env) -> begin
(
# 661 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_66_1069) with
| (nbs, _66_1068) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 675 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 679 "FStar.TypeChecker.Normalize.fst"
let _66_1086 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 683 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 684 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _147_454 = (
# 685 "FStar.TypeChecker.Normalize.fst"
let _66_1099 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _66_1099.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_1099.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _66_1099.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_454))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 691 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 695 "FStar.TypeChecker.Normalize.fst"
let _66_1142 = (log cfg (fun _66_1141 -> (match (()) with
| () -> begin
(let _147_456 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_456))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 700 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 701 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 703 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_66_1149, a) -> begin
(
# 707 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 712 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _147_457 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_457)))
end
| Match (env, branches, r)::stack -> begin
(
# 716 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _66_1170 -> (match (()) with
| () -> begin
(
# 717 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 718 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 718 "FStar.TypeChecker.Normalize.fst"
let _66_1172 = cfg
in (let _147_460 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _66_1172.steps; tcenv = _66_1172.tcenv; delta_level = _147_460}))
in (
# 719 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 723 "FStar.TypeChecker.Normalize.fst"
let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 725 "FStar.TypeChecker.Normalize.fst"
let _66_1182 = (FStar_Syntax_Subst.open_branch branch)
in (match (_66_1182) with
| (p, wopt, e) -> begin
(
# 726 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_468 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _147_468 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 728 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_469 = (norm_or_whnf env w)
in Some (_147_469))
end)
in (
# 731 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _147_470 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _147_470))))))
end))
in (
# 735 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _66_1196) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _66_1221 -> begin
false
end))
in (
# 742 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 746 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 747 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 751 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 755 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 756 "FStar.TypeChecker.Normalize.fst"
let _66_1238 = (FStar_Syntax_Util.head_and_args t)
in (match (_66_1238) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 759 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 760 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_66_1244) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_66_1261) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _66_1268 -> begin
(let _147_487 = (not ((is_cons head)))
in FStar_Util.Inr (_147_487))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _66_1276 -> begin
(let _147_488 = (not ((is_cons head)))
in FStar_Util.Inr (_147_488))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _66_1286)::rest_a, (p, _66_1292)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _66_1300 -> begin
FStar_Util.Inr (false)
end))
in (
# 793 "FStar.TypeChecker.Normalize.fst"
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
# 806 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_right (fun t env -> (let _147_500 = (let _147_499 = (let _147_498 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _147_498))
in Clos (_147_499))
in (_147_500)::env)) s env)
in (let _147_501 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_501)))
end)
end))
in (matches t branches))))))
end))

# 811 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 812 "FStar.TypeChecker.Normalize.fst"
let d = (match ((FStar_Util.find_map s (fun _66_6 -> (match (_66_6) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _66_1326 -> begin
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

# 819 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _147_513 = (config s e)
in (norm _147_513 [] [] t)))

# 820 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _147_520 = (config s e)
in (norm_comp _147_520 [] t)))

# 821 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _147_525 = (config [] env)
in (norm_universe _147_525 [] u)))

# 823 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_530 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_530)))

# 824 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_536 = (let _147_535 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _147_535 [] c))
in (FStar_Syntax_Print.comp_to_string _147_536)))

# 826 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 827 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 828 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 829 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 832 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _147_547 = (let _147_546 = (let _147_545 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _147_545))
in FStar_Syntax_Syntax.Tm_refine (_147_546))
in (mk _147_547 t0.FStar_Syntax_Syntax.pos))
end
| _66_1360 -> begin
t
end))
end
| _66_1362 -> begin
t
end)))
in (aux t))))

# 841 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 842 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _147_552 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _147_552 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 846 "FStar.TypeChecker.Normalize.fst"
let _66_1373 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_66_1373) with
| (binders, cdef) -> begin
(
# 847 "FStar.TypeChecker.Normalize.fst"
let inst = (let _147_556 = (let _147_555 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_555)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _66_1377 _66_1381 -> (match ((_66_1377, _66_1381)) with
| ((x, _66_1376), (t, _66_1380)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _147_556))
in (
# 848 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 849 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 849 "FStar.TypeChecker.Normalize.fst"
let _66_1384 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _66_1384.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _66_1384.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _66_1384.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 852 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _66_1387 _66_1389 _66_1391 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 853 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _66_1393 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 856 "FStar.TypeChecker.Normalize.fst"
let _66_1400 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_66_1400) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _66_1403 -> begin
(
# 860 "FStar.TypeChecker.Normalize.fst"
let _66_1406 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_66_1406) with
| (binders, args) -> begin
(let _147_569 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_568 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_567 -> Some (_147_567)))
in (FStar_Syntax_Util.abs binders _147_569 _147_568)))
end))
end)
end))
end
| _66_1408 -> begin
(let _147_572 = (let _147_571 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_570 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _147_571 _147_570)))
in (FStar_All.failwith _147_572))
end))





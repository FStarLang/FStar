
open Prims
# 42 "FStar.TypeChecker.Normalize.fst"
type step =
| WHNF
| Inline
| Unfold
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
let is_Unfold = (fun _discr_ -> (match (_discr_) with
| Unfold (_) -> begin
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
| Clos (_66_8) -> begin
_66_8
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_66_11) -> begin
_66_11
end))

# 67 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _66_1 -> (match (_66_1) with
| Clos (_66_14, t, _66_17) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _66_21 -> begin
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
| Arg (_66_28) -> begin
_66_28
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_66_31) -> begin
_66_31
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_66_34) -> begin
_66_34
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_66_37) -> begin
_66_37
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_66_40) -> begin
_66_40
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___App____0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_66_43) -> begin
_66_43
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_66_46) -> begin
_66_46
end))

# 90 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 102 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 103 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_66_52) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 108 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_160 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_160 (FStar_String.concat "; "))))

# 111 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _66_2 -> (match (_66_2) with
| Arg (c, _66_59, _66_61) -> begin
(closure_to_string c)
end
| MemoLazy (_66_65) -> begin
"MemoLazy"
end
| Abs (_66_68, bs, _66_71, _66_73, _66_75) -> begin
(let _147_163 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_163))
end
| _66_79 -> begin
"Match"
end))

# 117 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_166 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_166 (FStar_String.concat "; "))))

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
| _66_86 -> begin
false
end))

# 129 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _66_90 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _66_89 -> (match (_66_89) with
| _66_93 -> begin
(let _147_182 = (let _147_181 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_181))
in (FStar_All.failwith _147_182))
end))))

# 141 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 143 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 148 "FStar.TypeChecker.Normalize.fst"
let _66_114 = (FStar_List.fold_left (fun _66_105 u -> (match (_66_105) with
| (cur_kernel, cur_max, out) -> begin
(
# 150 "FStar.TypeChecker.Normalize.fst"
let _66_109 = (FStar_Syntax_Util.univ_kernel u)
in (match (_66_109) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_66_114) with
| (_66_111, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 161 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 162 "FStar.TypeChecker.Normalize.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _66_121 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| Dummy -> begin
(u)::[]
end
| _66_131 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _66_120 -> (match (_66_120) with
| _66_124 -> begin
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
(let _147_197 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_197 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_199 = (aux u)
in (FStar_List.map (fun _147_198 -> FStar_Syntax_Syntax.U_succ (_147_198)) _147_199))
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
| _66_163 -> begin
(
# 204 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_166) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _147_226 = (let _147_225 = (let _147_224 = (closure_as_term_delayed cfg env t')
in (u, _147_224))
in FStar_Syntax_Syntax.Tm_uvar (_147_225))
in (mk _147_226 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_228 = (let _147_227 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_227))
in (mk _147_228 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_229 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_229))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_191) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_66_204) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 233 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _66_210) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _147_235 = (FStar_List.fold_left (fun env' _66_217 -> (match (_66_217) with
| (t, _66_216) -> begin
(let _147_234 = (let _147_233 = (let _147_232 = (FStar_Util.mk_ref None)
in (env, t, _147_232))
in Clos (_147_233))
in (_147_234)::env')
end)) env args)
in (closure_as_term cfg _147_235 body))
end
| _66_219 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _66_221 -> begin
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
let _66_231 = (closures_as_binders_delayed cfg env bs)
in (match (_66_231) with
| (bs, env) -> begin
(
# 247 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _147_238 = (let _147_237 = (let _147_236 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _147_236))
in FStar_Syntax_Syntax.Tm_abs (_147_237))
in (mk _147_238 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 251 "FStar.TypeChecker.Normalize.fst"
let _66_239 = (closures_as_binders_delayed cfg env bs)
in (match (_66_239) with
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
let _66_247 = (let _147_240 = (let _147_239 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_239)::[])
in (closures_as_binders_delayed cfg env _147_240))
in (match (_66_247) with
| (x, env) -> begin
(
# 257 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _147_244 = (let _147_243 = (let _147_242 = (let _147_241 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_241 Prims.fst))
in (_147_242, phi))
in FStar_Syntax_Syntax.Tm_refine (_147_243))
in (mk _147_244 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _147_248 = (let _147_247 = (let _147_246 = (closure_as_term_delayed cfg env t1)
in (let _147_245 = (closure_as_term_delayed cfg env t2)
in (_147_246, _147_245, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_147_247))
in (mk _147_248 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_251 = (let _147_250 = (let _147_249 = (closure_as_term_delayed cfg env t')
in (_147_249, m))
in FStar_Syntax_Syntax.Tm_meta (_147_250))
in (mk _147_251 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 267 "FStar.TypeChecker.Normalize.fst"
let env0 = env
in (
# 268 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env _66_267 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 269 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 270 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 271 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_66_273) -> begin
body
end
| FStar_Util.Inl (_66_276) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 274 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 274 "FStar.TypeChecker.Normalize.fst"
let _66_279 = lb
in {FStar_Syntax_Syntax.lbname = _66_279.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _66_279.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _66_279.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_66_283, lbs), body) -> begin
(
# 278 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 279 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _66_292 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 280 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _66_296 env -> (Dummy)::env) lbs env_univs)
end
in (
# 283 "FStar.TypeChecker.Normalize.fst"
let _66_300 = lb
in (let _147_263 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _147_262 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _66_300.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _66_300.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _147_263; FStar_Syntax_Syntax.lbeff = _66_300.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _147_262}))))))
in (
# 285 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 286 "FStar.TypeChecker.Normalize.fst"
let body = (
# 287 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _66_303 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 292 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 293 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _66_318 -> (match (_66_318) with
| (pat, w_opt, tm) -> begin
(
# 294 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_66_323) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 298 "FStar.TypeChecker.Normalize.fst"
let _66_333 = (norm_pat env hd)
in (match (_66_333) with
| (hd, env') -> begin
(
# 299 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _147_275 = (norm_pat env p)
in (Prims.fst _147_275)))))
in ((
# 300 "FStar.TypeChecker.Normalize.fst"
let _66_336 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _66_336.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_336.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 302 "FStar.TypeChecker.Normalize.fst"
let _66_353 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _66_344 _66_347 -> (match ((_66_344, _66_347)) with
| ((pats, env), (p, b)) -> begin
(
# 303 "FStar.TypeChecker.Normalize.fst"
let _66_350 = (norm_pat env p)
in (match (_66_350) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_66_353) with
| (pats, env) -> begin
((
# 305 "FStar.TypeChecker.Normalize.fst"
let _66_354 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _66_354.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_354.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 307 "FStar.TypeChecker.Normalize.fst"
let x = (
# 307 "FStar.TypeChecker.Normalize.fst"
let _66_358 = x
in (let _147_278 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_358.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_358.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_278}))
in ((
# 308 "FStar.TypeChecker.Normalize.fst"
let _66_361 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _66_361.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_361.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 310 "FStar.TypeChecker.Normalize.fst"
let x = (
# 310 "FStar.TypeChecker.Normalize.fst"
let _66_365 = x
in (let _147_279 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_279}))
in ((
# 311 "FStar.TypeChecker.Normalize.fst"
let _66_368 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _66_368.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_368.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 313 "FStar.TypeChecker.Normalize.fst"
let x = (
# 313 "FStar.TypeChecker.Normalize.fst"
let _66_374 = x
in (let _147_280 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_374.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_374.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_280}))
in (
# 314 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 315 "FStar.TypeChecker.Normalize.fst"
let _66_378 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _66_378.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _66_378.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 316 "FStar.TypeChecker.Normalize.fst"
let _66_382 = (norm_pat env pat)
in (match (_66_382) with
| (pat, env) -> begin
(
# 317 "FStar.TypeChecker.Normalize.fst"
let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_281 = (closure_as_term cfg env w)
in Some (_147_281))
end)
in (
# 320 "FStar.TypeChecker.Normalize.fst"
let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _147_284 = (let _147_283 = (let _147_282 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _147_282))
in FStar_Syntax_Syntax.Tm_match (_147_283))
in (mk _147_284 t.FStar_Syntax_Syntax.pos))))
end))
end))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _66_392 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _66_395 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inr ((fun _66_396 -> (match (()) with
| () -> begin
(closure_as_term cfg env t)
end)))) t.FStar_Syntax_Syntax.pos)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _66_402 -> begin
(FStar_List.map (fun _66_405 -> (match (_66_405) with
| (x, imp) -> begin
(let _147_295 = (closure_as_term_delayed cfg env x)
in (_147_295, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * closure Prims.list) = (fun cfg env bs -> (
# 336 "FStar.TypeChecker.Normalize.fst"
let _66_421 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _66_411 _66_414 -> (match ((_66_411, _66_414)) with
| ((env, out), (b, imp)) -> begin
(
# 337 "FStar.TypeChecker.Normalize.fst"
let b = (
# 337 "FStar.TypeChecker.Normalize.fst"
let _66_415 = b
in (let _147_301 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_415.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_415.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_301}))
in (
# 338 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_66_421) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _66_427 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _147_305 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _147_305))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _147_306 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _147_306))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 350 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 351 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 352 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _66_4 -> (match (_66_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_308 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_308))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 355 "FStar.TypeChecker.Normalize.fst"
let _66_441 = c
in {FStar_Syntax_Syntax.effect_name = _66_441.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _66_5 -> (match (_66_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _147_315 = (
# 361 "FStar.TypeChecker.Normalize.fst"
let _66_449 = lc
in (let _147_314 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _66_449.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _147_314; FStar_Syntax_Syntax.cflags = _66_449.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _66_451 -> (match (()) with
| () -> begin
(let _147_313 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _147_313))
end))}))
in Some (_147_315))
end))

# 368 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 369 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 369 "FStar.TypeChecker.Normalize.fst"
let _66_456 = t
in {FStar_Syntax_Syntax.n = _66_456.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_456.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_456.FStar_Syntax_Syntax.vars}))
in (
# 370 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _66_465 -> begin
None
end))
in (
# 374 "FStar.TypeChecker.Normalize.fst"
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
| _66_543 -> begin
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
| _66_586 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _66_613)::(_66_604, (arg, _66_607))::[] -> begin
arg
end
| _66_617 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _66_621)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _66_627)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _66_631 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _147_326 = (FStar_Syntax_Subst.compress t)
in _147_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_649::[], body, _66_653) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _66_661 -> begin
tm
end)
end
| _66_663 -> begin
tm
end)
end
| _66_665 -> begin
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
| _66_667 -> begin
tm
end)
end))))

# 427 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 429 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 430 "FStar.TypeChecker.Normalize.fst"
let _66_674 = (log cfg (fun _66_673 -> (match (()) with
| () -> begin
(let _147_353 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_352 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_353 _147_352)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_677) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 444 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _147_357 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_357)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 450 "FStar.TypeChecker.Normalize.fst"
let us = (let _147_359 = (let _147_358 = (FStar_List.map (norm_universe cfg env) us)
in (_147_358, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_147_359))
in (
# 451 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
if (cfg.delta_level = FStar_TypeChecker_Env.NoDelta) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(
# 463 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _66_733)::stack -> begin
(
# 467 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _66_741 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _66_743 -> begin
(let _147_363 = (let _147_362 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_362))
in (FStar_All.failwith _147_363))
end)
end else begin
(norm cfg env stack t)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_747) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 482 "FStar.TypeChecker.Normalize.fst"
let _66_760 = (log cfg (fun _66_759 -> (match (()) with
| () -> begin
(let _147_366 = (FStar_Syntax_Print.term_to_string t)
in (let _147_365 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_366 _147_365)))
end)))
in (match ((let _147_367 = (FStar_Syntax_Subst.compress t')
in _147_367.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_763) -> begin
(norm cfg env stack t')
end
| _66_766 -> begin
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
| Meta (_66_776)::_66_774 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_66_782)::_66_780 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_66_788)::_66_786 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _66_794, _66_796)::stack -> begin
(match (c) with
| Univ (_66_801) -> begin
(norm cfg ((c)::env) stack t)
end
| _66_804 -> begin
(
# 510 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _66_807::[] -> begin
body
end
| _66_811::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 514 "FStar.TypeChecker.Normalize.fst"
let _66_815 = (log cfg (fun _66_814 -> (match (()) with
| () -> begin
(let _147_369 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_369))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 519 "FStar.TypeChecker.Normalize.fst"
let _66_821 = (set_memo r (env, t))
in (
# 520 "FStar.TypeChecker.Normalize.fst"
let _66_824 = (log cfg (fun _66_823 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_371 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_371))
end else begin
(
# 528 "FStar.TypeChecker.Normalize.fst"
let _66_841 = (FStar_Syntax_Subst.open_term bs body)
in (match (_66_841) with
| (bs, body) -> begin
(
# 529 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_843 -> (Dummy)::env) env))
in (
# 530 "FStar.TypeChecker.Normalize.fst"
let _66_847 = (log cfg (fun _66_846 -> (match (()) with
| () -> begin
(let _147_375 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_375))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 535 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _66_855 stack -> (match (_66_855) with
| (a, aq) -> begin
(let _147_382 = (let _147_381 = (let _147_380 = (let _147_379 = (let _147_378 = (FStar_Util.mk_ref None)
in (env, a, _147_378))
in Clos (_147_379))
in (_147_380, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_147_381))
in (_147_382)::stack)
end)) args))
in (
# 536 "FStar.TypeChecker.Normalize.fst"
let _66_859 = (log cfg (fun _66_858 -> (match (()) with
| () -> begin
(let _147_384 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_384))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_385 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_385))
end else begin
(
# 542 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 543 "FStar.TypeChecker.Normalize.fst"
let _66_868 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_66_868) with
| (closing, f) -> begin
(
# 544 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 545 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_388 = (let _147_387 = (let _147_386 = (FStar_Syntax_Subst.close closing f)
in ((
# 545 "FStar.TypeChecker.Normalize.fst"
let _66_870 = x
in {FStar_Syntax_Syntax.ppname = _66_870.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_870.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _147_386))
in FStar_Syntax_Syntax.Tm_refine (_147_387))
in (mk _147_388 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_389 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_389))
end else begin
(
# 551 "FStar.TypeChecker.Normalize.fst"
let _66_879 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_66_879) with
| (bs, c) -> begin
(
# 552 "FStar.TypeChecker.Normalize.fst"
let c = (let _147_392 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_881 -> (Dummy)::env) env))
in (norm_comp cfg _147_392 c))
in (
# 553 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_393 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_393 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _66_909 -> begin
(
# 562 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 563 "FStar.TypeChecker.Normalize.fst"
let _66_912 = (log cfg (fun _66_911 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 564 "FStar.TypeChecker.Normalize.fst"
let t2 = (norm cfg env [] t2)
in (let _147_395 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_395)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 571 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 575 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_398 = (let _147_397 = (let _147_396 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _147_396))
in Clos (_147_397))
in (_147_398)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_66_929, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_66_941); FStar_Syntax_Syntax.lbunivs = _66_939; FStar_Syntax_Syntax.lbtyp = _66_937; FStar_Syntax_Syntax.lbeff = _66_935; FStar_Syntax_Syntax.lbdef = _66_933}::_66_931), _66_947) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 592 "FStar.TypeChecker.Normalize.fst"
let _66_969 = (FStar_List.fold_right (fun lb _66_958 -> (match (_66_958) with
| (rec_env, memos, i) -> begin
(
# 593 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _147_401 = (
# 593 "FStar.TypeChecker.Normalize.fst"
let _66_959 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _66_959.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _66_959.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_401))
in (
# 594 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 595 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 596 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_66_969) with
| (rec_env, memos, _66_968) -> begin
(
# 598 "FStar.TypeChecker.Normalize.fst"
let _66_972 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 599 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _147_408 = (let _147_407 = (let _147_406 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _147_406))
in Clos (_147_407))
in (_147_408)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _66_984::_66_982 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _66_989) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 611 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _66_996 -> begin
(norm cfg env stack head)
end)
end
| _66_998 -> begin
(
# 618 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 619 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_409 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_409))
end
| _66_1003 -> begin
m
end)
in (
# 623 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _66_1011 -> (match (_66_1011) with
| (a, imp) -> begin
(let _147_414 = (norm cfg env [] a)
in (_147_414, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 634 "FStar.TypeChecker.Normalize.fst"
let _66_1017 = comp
in (let _147_419 = (let _147_418 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_147_418))
in {FStar_Syntax_Syntax.n = _147_419; FStar_Syntax_Syntax.tk = _66_1017.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1017.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1017.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 637 "FStar.TypeChecker.Normalize.fst"
let _66_1021 = comp
in (let _147_421 = (let _147_420 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_147_420))
in {FStar_Syntax_Syntax.n = _147_421; FStar_Syntax_Syntax.tk = _66_1021.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1021.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1021.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 640 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _66_1029 -> (match (_66_1029) with
| (a, i) -> begin
(let _147_425 = (norm cfg env [] a)
in (_147_425, i))
end)))))
in (
# 641 "FStar.TypeChecker.Normalize.fst"
let _66_1030 = comp
in (let _147_429 = (let _147_428 = (
# 641 "FStar.TypeChecker.Normalize.fst"
let _66_1032 = ct
in (let _147_427 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_426 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _66_1032.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_427; FStar_Syntax_Syntax.effect_args = _147_426; FStar_Syntax_Syntax.flags = _66_1032.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_147_428))
in {FStar_Syntax_Syntax.n = _147_429; FStar_Syntax_Syntax.tk = _66_1030.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_1030.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_1030.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _66_1038 -> (match (_66_1038) with
| (x, imp) -> begin
(let _147_434 = (
# 645 "FStar.TypeChecker.Normalize.fst"
let _66_1039 = x
in (let _147_433 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_1039.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1039.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_433}))
in (_147_434, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 649 "FStar.TypeChecker.Normalize.fst"
let _66_1052 = (FStar_List.fold_left (fun _66_1046 b -> (match (_66_1046) with
| (nbs', env) -> begin
(
# 650 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_66_1052) with
| (nbs, _66_1051) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 664 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 668 "FStar.TypeChecker.Normalize.fst"
let _66_1069 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 672 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 673 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _147_444 = (
# 674 "FStar.TypeChecker.Normalize.fst"
let _66_1082 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _66_1082.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_1082.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _66_1082.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_444))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 680 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 684 "FStar.TypeChecker.Normalize.fst"
let _66_1125 = (log cfg (fun _66_1124 -> (match (()) with
| () -> begin
(let _147_446 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_446))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 689 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 690 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 692 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_66_1132, a) -> begin
(
# 696 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 701 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _147_447 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_447)))
end
| Match (env, branches, r)::stack -> begin
(
# 705 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _66_1153 -> (match (()) with
| () -> begin
(
# 706 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 707 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 707 "FStar.TypeChecker.Normalize.fst"
let _66_1155 = cfg
in (let _147_450 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _66_1155.steps; tcenv = _66_1155.tcenv; delta_level = _147_450}))
in (
# 708 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 712 "FStar.TypeChecker.Normalize.fst"
let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 714 "FStar.TypeChecker.Normalize.fst"
let _66_1165 = (FStar_Syntax_Subst.open_branch branch)
in (match (_66_1165) with
| (p, wopt, e) -> begin
(
# 715 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_458 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _147_458 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 717 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_459 = (norm_or_whnf env w)
in Some (_147_459))
end)
in (
# 720 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _147_460 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _147_460))))))
end))
in (
# 724 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _66_1179) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _66_1204 -> begin
false
end))
in (
# 731 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 735 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 736 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 740 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 744 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 745 "FStar.TypeChecker.Normalize.fst"
let _66_1221 = (FStar_Syntax_Util.head_and_args t)
in (match (_66_1221) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 748 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 749 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_66_1227) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_66_1244) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _66_1251 -> begin
(let _147_477 = (not ((is_cons head)))
in FStar_Util.Inr (_147_477))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _66_1259 -> begin
(let _147_478 = (not ((is_cons head)))
in FStar_Util.Inr (_147_478))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _66_1269)::rest_a, (p, _66_1275)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _66_1283 -> begin
FStar_Util.Inr (false)
end))
in (
# 782 "FStar.TypeChecker.Normalize.fst"
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
# 795 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_right (fun t env -> (let _147_490 = (let _147_489 = (let _147_488 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _147_488))
in Clos (_147_489))
in (_147_490)::env)) s env)
in (let _147_491 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_491)))
end)
end))
in (matches t branches))))))
end))

# 800 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 801 "FStar.TypeChecker.Normalize.fst"
let d = if (FStar_List.contains Unfold s) then begin
FStar_TypeChecker_Env.Unfold
end else begin
if (FStar_List.contains Inline s) then begin
FStar_TypeChecker_Env.OnlyInline
end else begin
FStar_TypeChecker_Env.NoDelta
end
end
in {steps = s; tcenv = e; delta_level = d}))

# 808 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (norm (config s e) [] [] t))

# 809 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (norm_comp (config s e) [] t))

# 810 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (norm_universe (config [] env) [] u))

# 812 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_516 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_516)))

# 813 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_521 = (norm_comp (config ((AllowUnboundUniverses)::[]) env) [] c)
in (FStar_Syntax_Print.comp_to_string _147_521)))

# 815 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 816 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 817 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 818 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 821 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _147_532 = (let _147_531 = (let _147_530 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _147_530))
in FStar_Syntax_Syntax.Tm_refine (_147_531))
in (mk _147_532 t0.FStar_Syntax_Syntax.pos))
end
| _66_1335 -> begin
t
end))
end
| _66_1337 -> begin
t
end)))
in (aux t))))

# 830 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 831 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _147_537 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _147_537 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 835 "FStar.TypeChecker.Normalize.fst"
let _66_1348 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_66_1348) with
| (binders, cdef) -> begin
(
# 836 "FStar.TypeChecker.Normalize.fst"
let inst = (let _147_541 = (let _147_540 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_540)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _66_1352 _66_1356 -> (match ((_66_1352, _66_1356)) with
| ((x, _66_1351), (t, _66_1355)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _147_541))
in (
# 837 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 838 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 838 "FStar.TypeChecker.Normalize.fst"
let _66_1359 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _66_1359.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _66_1359.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _66_1359.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 841 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _66_1362 _66_1364 _66_1366 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 842 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _66_1368 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 845 "FStar.TypeChecker.Normalize.fst"
let _66_1375 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_66_1375) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _66_1378 -> begin
(
# 849 "FStar.TypeChecker.Normalize.fst"
let _66_1381 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_66_1381) with
| (binders, args) -> begin
(let _147_554 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_553 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_552 -> Some (_147_552)))
in (FStar_Syntax_Util.abs binders _147_554 _147_553)))
end))
end)
end))
end
| _66_1383 -> begin
(let _147_557 = (let _147_556 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_555 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _147_556 _147_555)))
in (FStar_All.failwith _147_557))
end))





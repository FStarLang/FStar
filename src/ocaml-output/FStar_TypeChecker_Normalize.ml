
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
| UnfoldUntil (_59_9) -> begin
_59_9
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
| Clos (_59_12) -> begin
_59_12
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_59_15) -> begin
_59_15
end))

# 67 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _59_1 -> (match (_59_1) with
| Clos (_59_18, t, _59_21) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _59_25 -> begin
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
let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_59_32) -> begin
_59_32
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_59_35) -> begin
_59_35
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_59_38) -> begin
_59_38
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_59_41) -> begin
_59_41
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_59_44) -> begin
_59_44
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_59_47) -> begin
_59_47
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_59_50) -> begin
_59_50
end))

# 90 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 102 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 103 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_59_56) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 108 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _143_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _143_173 (FStar_String.concat "; "))))

# 111 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _59_2 -> (match (_59_2) with
| Arg (c, _59_63, _59_65) -> begin
(closure_to_string c)
end
| MemoLazy (_59_69) -> begin
"MemoLazy"
end
| Abs (_59_72, bs, _59_75, _59_77, _59_79) -> begin
(let _143_176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _143_176))
end
| _59_83 -> begin
"Match"
end))

# 117 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _143_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _143_179 (FStar_String.concat "; "))))

# 120 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 125 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _59_3 -> (match (_59_3) with
| [] -> begin
true
end
| _59_90 -> begin
false
end))

# 129 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _59_94 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _59_93 -> (match (_59_93) with
| _59_97 -> begin
(let _143_195 = (let _143_194 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _143_194))
in (FStar_All.failwith _143_195))
end))))

# 141 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 143 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 148 "FStar.TypeChecker.Normalize.fst"
let _59_118 = (FStar_List.fold_left (fun _59_109 u -> (match (_59_109) with
| (cur_kernel, cur_max, out) -> begin
(
# 150 "FStar.TypeChecker.Normalize.fst"
let _59_113 = (FStar_Syntax_Util.univ_kernel u)
in (match (_59_113) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_59_118) with
| (_59_115, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 161 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 162 "FStar.TypeChecker.Normalize.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _59_125 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| Dummy -> begin
(u)::[]
end
| _59_135 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _59_124 -> (match (_59_124) with
| _59_128 -> begin
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
(let _143_210 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _143_210 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _143_212 = (aux u)
in (FStar_List.map (fun _143_211 -> FStar_Syntax_Syntax.U_succ (_143_211)) _143_212))
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
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (
# 201 "FStar.TypeChecker.Normalize.fst"
let _59_166 = (log cfg (fun _59_165 -> (match (()) with
| () -> begin
(let _143_236 = (FStar_Syntax_Print.tag_of_term t)
in (let _143_235 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _143_236 _143_235)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _59_170 -> begin
(
# 205 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_59_173) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _143_242 = (let _143_241 = (let _143_240 = (closure_as_term_delayed cfg env t')
in (u, _143_240))
in FStar_Syntax_Syntax.Tm_uvar (_143_241))
in (mk _143_242 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _143_244 = (let _143_243 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_143_243))
in (mk _143_244 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _143_245 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _143_245))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_59_198) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_59_211) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 234 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _59_217) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _143_251 = (FStar_List.fold_left (fun env' _59_224 -> (match (_59_224) with
| (t, _59_223) -> begin
(let _143_250 = (let _143_249 = (let _143_248 = (FStar_Util.mk_ref None)
in (env, t, _143_248))
in Clos (_143_249))
in (_143_250)::env')
end)) env args)
in (closure_as_term cfg _143_251 body))
end
| _59_226 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _59_228 -> begin
(
# 241 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (
# 242 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 247 "FStar.TypeChecker.Normalize.fst"
let _59_238 = (closures_as_binders_delayed cfg env bs)
in (match (_59_238) with
| (bs, env) -> begin
(
# 248 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _143_254 = (let _143_253 = (let _143_252 = (close_lcomp_opt cfg env lopt)
in (bs, body, _143_252))
in FStar_Syntax_Syntax.Tm_abs (_143_253))
in (mk _143_254 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 252 "FStar.TypeChecker.Normalize.fst"
let _59_246 = (closures_as_binders_delayed cfg env bs)
in (match (_59_246) with
| (bs, env) -> begin
(
# 253 "FStar.TypeChecker.Normalize.fst"
let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 257 "FStar.TypeChecker.Normalize.fst"
let _59_254 = (let _143_256 = (let _143_255 = (FStar_Syntax_Syntax.mk_binder x)
in (_143_255)::[])
in (closures_as_binders_delayed cfg env _143_256))
in (match (_59_254) with
| (x, env) -> begin
(
# 258 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _143_260 = (let _143_259 = (let _143_258 = (let _143_257 = (FStar_List.hd x)
in (FStar_All.pipe_right _143_257 Prims.fst))
in (_143_258, phi))
in FStar_Syntax_Syntax.Tm_refine (_143_259))
in (mk _143_260 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _143_264 = (let _143_263 = (let _143_262 = (closure_as_term_delayed cfg env t1)
in (let _143_261 = (closure_as_term_delayed cfg env t2)
in (_143_262, _143_261, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_143_263))
in (mk _143_264 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _143_269 = (let _143_268 = (let _143_267 = (closure_as_term_delayed cfg env t')
in (let _143_266 = (let _143_265 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_143_265))
in (_143_267, _143_266)))
in FStar_Syntax_Syntax.Tm_meta (_143_268))
in (mk _143_269 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _143_272 = (let _143_271 = (let _143_270 = (closure_as_term_delayed cfg env t')
in (_143_270, m))
in FStar_Syntax_Syntax.Tm_meta (_143_271))
in (mk _143_272 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 272 "FStar.TypeChecker.Normalize.fst"
let env0 = env
in (
# 273 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env _59_279 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 274 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 275 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 276 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_59_285) -> begin
body
end
| FStar_Util.Inl (_59_288) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 279 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 279 "FStar.TypeChecker.Normalize.fst"
let _59_291 = lb
in {FStar_Syntax_Syntax.lbname = _59_291.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _59_291.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _59_291.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_59_295, lbs), body) -> begin
(
# 283 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 284 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _59_304 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 285 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _59_308 env -> (Dummy)::env) lbs env_univs)
end
in (
# 288 "FStar.TypeChecker.Normalize.fst"
let _59_312 = lb
in (let _143_284 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _143_283 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _59_312.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _59_312.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _143_284; FStar_Syntax_Syntax.lbeff = _59_312.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _143_283}))))))
in (
# 290 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 291 "FStar.TypeChecker.Normalize.fst"
let body = (
# 292 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _59_315 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 297 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 298 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _59_330 -> (match (_59_330) with
| (pat, w_opt, tm) -> begin
(
# 299 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_59_335) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 303 "FStar.TypeChecker.Normalize.fst"
let _59_345 = (norm_pat env hd)
in (match (_59_345) with
| (hd, env') -> begin
(
# 304 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _143_296 = (norm_pat env p)
in (Prims.fst _143_296)))))
in ((
# 305 "FStar.TypeChecker.Normalize.fst"
let _59_348 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _59_348.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_348.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 307 "FStar.TypeChecker.Normalize.fst"
let _59_365 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _59_356 _59_359 -> (match ((_59_356, _59_359)) with
| ((pats, env), (p, b)) -> begin
(
# 308 "FStar.TypeChecker.Normalize.fst"
let _59_362 = (norm_pat env p)
in (match (_59_362) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_59_365) with
| (pats, env) -> begin
((
# 310 "FStar.TypeChecker.Normalize.fst"
let _59_366 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _59_366.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_366.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 312 "FStar.TypeChecker.Normalize.fst"
let x = (
# 312 "FStar.TypeChecker.Normalize.fst"
let _59_370 = x
in (let _143_299 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_370.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_370.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_299}))
in ((
# 313 "FStar.TypeChecker.Normalize.fst"
let _59_373 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _59_373.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_373.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 315 "FStar.TypeChecker.Normalize.fst"
let x = (
# 315 "FStar.TypeChecker.Normalize.fst"
let _59_377 = x
in (let _143_300 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_300}))
in ((
# 316 "FStar.TypeChecker.Normalize.fst"
let _59_380 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _59_380.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_380.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 318 "FStar.TypeChecker.Normalize.fst"
let x = (
# 318 "FStar.TypeChecker.Normalize.fst"
let _59_386 = x
in (let _143_301 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_386.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_386.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_301}))
in (
# 319 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 320 "FStar.TypeChecker.Normalize.fst"
let _59_390 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _59_390.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _59_390.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 321 "FStar.TypeChecker.Normalize.fst"
let _59_394 = (norm_pat env pat)
in (match (_59_394) with
| (pat, env) -> begin
(
# 322 "FStar.TypeChecker.Normalize.fst"
let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _143_302 = (closure_as_term cfg env w)
in Some (_143_302))
end)
in (
# 325 "FStar.TypeChecker.Normalize.fst"
let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _143_305 = (let _143_304 = (let _143_303 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _143_303))
in FStar_Syntax_Syntax.Tm_match (_143_304))
in (mk _143_305 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _59_404 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _59_407 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _59_413 -> begin
(FStar_List.map (fun _59_416 -> (match (_59_416) with
| (x, imp) -> begin
(let _143_313 = (closure_as_term_delayed cfg env x)
in (_143_313, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (
# 342 "FStar.TypeChecker.Normalize.fst"
let _59_432 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _59_422 _59_425 -> (match ((_59_422, _59_425)) with
| ((env, out), (b, imp)) -> begin
(
# 343 "FStar.TypeChecker.Normalize.fst"
let b = (
# 343 "FStar.TypeChecker.Normalize.fst"
let _59_426 = b
in (let _143_319 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_426.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_426.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_319}))
in (
# 344 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_59_432) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _59_438 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _143_323 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _143_323))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _143_324 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _143_324))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 356 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 357 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 358 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _59_4 -> (match (_59_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _143_326 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_143_326))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 361 "FStar.TypeChecker.Normalize.fst"
let _59_452 = c
in {FStar_Syntax_Syntax.effect_name = _59_452.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _59_5 -> (match (_59_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _143_333 = (
# 367 "FStar.TypeChecker.Normalize.fst"
let _59_460 = lc
in (let _143_332 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _59_460.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _143_332; FStar_Syntax_Syntax.cflags = _59_460.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _59_462 -> (match (()) with
| () -> begin
(let _143_331 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _143_331))
end))}))
in Some (_143_333))
end))

# 374 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 375 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 375 "FStar.TypeChecker.Normalize.fst"
let _59_467 = t
in {FStar_Syntax_Syntax.n = _59_467.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_467.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_467.FStar_Syntax_Syntax.vars}))
in (
# 376 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _59_476 -> begin
None
end))
in (
# 380 "FStar.TypeChecker.Normalize.fst"
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
| _59_554 -> begin
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
| _59_597 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _59_624)::(_59_615, (arg, _59_618))::[] -> begin
arg
end
| _59_628 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _59_632)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _59_638)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _59_642 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _143_344 = (FStar_Syntax_Subst.compress t)
in _143_344.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_59_660::[], body, _59_664) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _59_672 -> begin
tm
end)
end
| _59_674 -> begin
tm
end)
end
| _59_676 -> begin
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
| _59_678 -> begin
tm
end)
end))))

# 433 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 435 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 436 "FStar.TypeChecker.Normalize.fst"
let _59_685 = (log cfg (fun _59_684 -> (match (()) with
| () -> begin
(let _143_371 = (FStar_Syntax_Print.tag_of_term t)
in (let _143_370 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _143_371 _143_370)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_59_688) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 450 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _143_375 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _143_375)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 456 "FStar.TypeChecker.Normalize.fst"
let us = (let _143_377 = (let _143_376 = (FStar_List.map (norm_universe cfg env) us)
in (_143_376, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_143_377))
in (
# 457 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(
# 464 "FStar.TypeChecker.Normalize.fst"
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
# 474 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _59_749)::stack -> begin
(
# 478 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _59_757 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _59_759 -> begin
(let _143_381 = (let _143_380 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _143_380))
in (FStar_All.failwith _143_381))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_59_763) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 493 "FStar.TypeChecker.Normalize.fst"
let _59_776 = (log cfg (fun _59_775 -> (match (()) with
| () -> begin
(let _143_384 = (FStar_Syntax_Print.term_to_string t)
in (let _143_383 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _143_384 _143_383)))
end)))
in (match ((let _143_385 = (FStar_Syntax_Subst.compress t')
in _143_385.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_59_779) -> begin
(norm cfg env stack t')
end
| _59_782 -> begin
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
| Meta (_59_792)::_59_790 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_59_798)::_59_796 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_59_804)::_59_802 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _59_810, _59_812)::stack -> begin
(match (c) with
| Univ (_59_817) -> begin
(norm cfg ((c)::env) stack t)
end
| _59_820 -> begin
(
# 521 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _59_823::[] -> begin
body
end
| _59_827::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 525 "FStar.TypeChecker.Normalize.fst"
let _59_831 = (log cfg (fun _59_830 -> (match (()) with
| () -> begin
(let _143_387 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _143_387))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 530 "FStar.TypeChecker.Normalize.fst"
let _59_837 = (set_memo r (env, t))
in (
# 531 "FStar.TypeChecker.Normalize.fst"
let _59_840 = (log cfg (fun _59_839 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _143_389 = (closure_as_term cfg env t)
in (rebuild cfg env stack _143_389))
end else begin
(
# 539 "FStar.TypeChecker.Normalize.fst"
let _59_858 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_59_858) with
| (bs, body, opening) -> begin
(
# 540 "FStar.TypeChecker.Normalize.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _143_393 = (let _143_391 = (let _143_390 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _143_390))
in (FStar_All.pipe_right _143_391 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _143_393 (fun _143_392 -> Some (_143_392))))
end)
in (
# 543 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _59_864 -> (Dummy)::env) env))
in (
# 544 "FStar.TypeChecker.Normalize.fst"
let _59_868 = (log cfg (fun _59_867 -> (match (()) with
| () -> begin
(let _143_397 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _143_397))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 549 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _59_876 stack -> (match (_59_876) with
| (a, aq) -> begin
(let _143_404 = (let _143_403 = (let _143_402 = (let _143_401 = (let _143_400 = (FStar_Util.mk_ref None)
in (env, a, _143_400))
in Clos (_143_401))
in (_143_402, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_143_403))
in (_143_404)::stack)
end)) args))
in (
# 550 "FStar.TypeChecker.Normalize.fst"
let _59_880 = (log cfg (fun _59_879 -> (match (()) with
| () -> begin
(let _143_406 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _143_406))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(
# 557 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 558 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_refine (((
# 558 "FStar.TypeChecker.Normalize.fst"
let _59_890 = x
in {FStar_Syntax_Syntax.ppname = _59_890.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_890.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _59_894 -> begin
(let _143_407 = (closure_as_term cfg env t)
in (rebuild cfg env stack _143_407))
end)
end else begin
(
# 561 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 562 "FStar.TypeChecker.Normalize.fst"
let _59_898 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_59_898) with
| (closing, f) -> begin
(
# 563 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 564 "FStar.TypeChecker.Normalize.fst"
let t = (let _143_410 = (let _143_409 = (let _143_408 = (FStar_Syntax_Subst.close closing f)
in ((
# 564 "FStar.TypeChecker.Normalize.fst"
let _59_900 = x
in {FStar_Syntax_Syntax.ppname = _59_900.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_900.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _143_408))
in FStar_Syntax_Syntax.Tm_refine (_143_409))
in (mk _143_410 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _143_411 = (closure_as_term cfg env t)
in (rebuild cfg env stack _143_411))
end else begin
(
# 570 "FStar.TypeChecker.Normalize.fst"
let _59_909 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_59_909) with
| (bs, c) -> begin
(
# 571 "FStar.TypeChecker.Normalize.fst"
let c = (let _143_414 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _59_911 -> (Dummy)::env) env))
in (norm_comp cfg _143_414 c))
in (
# 572 "FStar.TypeChecker.Normalize.fst"
let t = (let _143_415 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _143_415 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _59_939 -> begin
(
# 581 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 582 "FStar.TypeChecker.Normalize.fst"
let _59_942 = (log cfg (fun _59_941 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 583 "FStar.TypeChecker.Normalize.fst"
let t2 = (norm cfg env [] t2)
in (let _143_417 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _143_417)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 590 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 594 "FStar.TypeChecker.Normalize.fst"
let env = (let _143_420 = (let _143_419 = (let _143_418 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _143_418))
in Clos (_143_419))
in (_143_420)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_59_959, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_59_971); FStar_Syntax_Syntax.lbunivs = _59_969; FStar_Syntax_Syntax.lbtyp = _59_967; FStar_Syntax_Syntax.lbeff = _59_965; FStar_Syntax_Syntax.lbdef = _59_963}::_59_961), _59_977) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 611 "FStar.TypeChecker.Normalize.fst"
let _59_999 = (FStar_List.fold_right (fun lb _59_988 -> (match (_59_988) with
| (rec_env, memos, i) -> begin
(
# 612 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _143_423 = (
# 612 "FStar.TypeChecker.Normalize.fst"
let _59_989 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _59_989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _59_989.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _143_423))
in (
# 613 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 614 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 615 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_59_999) with
| (rec_env, memos, _59_998) -> begin
(
# 617 "FStar.TypeChecker.Normalize.fst"
let _59_1002 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 618 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _143_430 = (let _143_429 = (let _143_428 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _143_428))
in Clos (_143_429))
in (_143_430)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _59_1014::_59_1012 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _59_1019) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 630 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _59_1026 -> begin
(norm cfg env stack head)
end)
end
| _59_1028 -> begin
(
# 637 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 638 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _143_431 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_143_431))
end
| _59_1033 -> begin
m
end)
in (
# 642 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _59_1041 -> (match (_59_1041) with
| (a, imp) -> begin
(let _143_436 = (norm cfg env [] a)
in (_143_436, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 653 "FStar.TypeChecker.Normalize.fst"
let _59_1047 = comp
in (let _143_441 = (let _143_440 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_143_440))
in {FStar_Syntax_Syntax.n = _143_441; FStar_Syntax_Syntax.tk = _59_1047.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1047.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1047.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 656 "FStar.TypeChecker.Normalize.fst"
let _59_1051 = comp
in (let _143_443 = (let _143_442 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_143_442))
in {FStar_Syntax_Syntax.n = _143_443; FStar_Syntax_Syntax.tk = _59_1051.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1051.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1051.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 659 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _59_1059 -> (match (_59_1059) with
| (a, i) -> begin
(let _143_447 = (norm cfg env [] a)
in (_143_447, i))
end)))))
in (
# 660 "FStar.TypeChecker.Normalize.fst"
let _59_1060 = comp
in (let _143_451 = (let _143_450 = (
# 660 "FStar.TypeChecker.Normalize.fst"
let _59_1062 = ct
in (let _143_449 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _143_448 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _59_1062.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _143_449; FStar_Syntax_Syntax.effect_args = _143_448; FStar_Syntax_Syntax.flags = _59_1062.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_143_450))
in {FStar_Syntax_Syntax.n = _143_451; FStar_Syntax_Syntax.tk = _59_1060.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _59_1060.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _59_1060.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _59_1068 -> (match (_59_1068) with
| (x, imp) -> begin
(let _143_456 = (
# 664 "FStar.TypeChecker.Normalize.fst"
let _59_1069 = x
in (let _143_455 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _59_1069.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _59_1069.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _143_455}))
in (_143_456, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 668 "FStar.TypeChecker.Normalize.fst"
let _59_1082 = (FStar_List.fold_left (fun _59_1076 b -> (match (_59_1076) with
| (nbs', env) -> begin
(
# 669 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_59_1082) with
| (nbs, _59_1081) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 683 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 687 "FStar.TypeChecker.Normalize.fst"
let _59_1099 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 691 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 692 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _143_466 = (
# 693 "FStar.TypeChecker.Normalize.fst"
let _59_1112 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _59_1112.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _59_1112.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _59_1112.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _143_466))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 699 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 703 "FStar.TypeChecker.Normalize.fst"
let _59_1155 = (log cfg (fun _59_1154 -> (match (()) with
| () -> begin
(let _143_468 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _143_468))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 708 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 709 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 711 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_59_1162, a) -> begin
(
# 715 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 720 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _143_469 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _143_469)))
end
| Match (env, branches, r)::stack -> begin
(
# 724 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _59_1183 -> (match (()) with
| () -> begin
(
# 725 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 726 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 726 "FStar.TypeChecker.Normalize.fst"
let _59_1185 = cfg
in (let _143_472 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _59_1185.steps; tcenv = _59_1185.tcenv; delta_level = _143_472}))
in (
# 727 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 731 "FStar.TypeChecker.Normalize.fst"
let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _59_1193 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 735 "FStar.TypeChecker.Normalize.fst"
let _59_1198 = (FStar_Syntax_Subst.open_branch branch)
in (match (_59_1198) with
| (p, wopt, e) -> begin
(
# 736 "FStar.TypeChecker.Normalize.fst"
let env = (let _143_480 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _143_480 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 738 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _143_481 = (norm_or_whnf env w)
in Some (_143_481))
end)
in (
# 741 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _143_482 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _143_482))))))
end))
in (
# 745 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _59_1212) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _59_1237 -> begin
false
end))
in (
# 752 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 756 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 757 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 761 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 765 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 766 "FStar.TypeChecker.Normalize.fst"
let _59_1254 = (FStar_Syntax_Util.head_and_args t)
in (match (_59_1254) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 769 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 770 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_59_1260) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_59_1277) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _59_1284 -> begin
(let _143_499 = (not ((is_cons head)))
in FStar_Util.Inr (_143_499))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _59_1292 -> begin
(let _143_500 = (not ((is_cons head)))
in FStar_Util.Inr (_143_500))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _59_1302)::rest_a, (p, _59_1308)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _59_1316 -> begin
FStar_Util.Inr (false)
end))
in (
# 803 "FStar.TypeChecker.Normalize.fst"
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
# 816 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_right (fun t env -> (let _143_512 = (let _143_511 = (let _143_510 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _143_510))
in Clos (_143_511))
in (_143_512)::env)) s env)
in (let _143_513 = (guard_when_clause wopt b rest)
in (norm cfg env stack _143_513)))
end)
end))
in (matches t branches))))))
end))

# 821 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 822 "FStar.TypeChecker.Normalize.fst"
let d = (match ((FStar_Util.find_map s (fun _59_6 -> (match (_59_6) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _59_1342 -> begin
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

# 829 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _143_525 = (config s e)
in (norm _143_525 [] [] t)))

# 830 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _143_532 = (config s e)
in (norm_comp _143_532 [] t)))

# 831 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _143_537 = (config [] env)
in (norm_universe _143_537 [] u)))

# 833 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _143_542 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _143_542)))

# 834 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _143_548 = (let _143_547 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _143_547 [] c))
in (FStar_Syntax_Print.comp_to_string _143_548)))

# 836 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 837 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 838 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 839 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 842 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _143_559 = (let _143_558 = (let _143_557 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _143_557))
in FStar_Syntax_Syntax.Tm_refine (_143_558))
in (mk _143_559 t0.FStar_Syntax_Syntax.pos))
end
| _59_1376 -> begin
t
end))
end
| _59_1378 -> begin
t
end)))
in (aux t))))

# 851 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 852 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _143_564 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _143_564 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 856 "FStar.TypeChecker.Normalize.fst"
let _59_1389 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_59_1389) with
| (binders, cdef) -> begin
(
# 857 "FStar.TypeChecker.Normalize.fst"
let inst = (let _143_568 = (let _143_567 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_143_567)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _59_1393 _59_1397 -> (match ((_59_1393, _59_1397)) with
| ((x, _59_1392), (t, _59_1396)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _143_568))
in (
# 858 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 859 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 859 "FStar.TypeChecker.Normalize.fst"
let _59_1400 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _59_1400.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _59_1400.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _59_1400.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 862 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _59_1403 _59_1405 _59_1407 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 863 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _59_1409 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 866 "FStar.TypeChecker.Normalize.fst"
let _59_1416 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_59_1416) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _59_1419 -> begin
(
# 870 "FStar.TypeChecker.Normalize.fst"
let _59_1422 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_59_1422) with
| (binders, args) -> begin
(let _143_581 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _143_580 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _143_579 -> Some (_143_579)))
in (FStar_Syntax_Util.abs binders _143_581 _143_580)))
end))
end)
end))
end
| _59_1424 -> begin
(let _143_584 = (let _143_583 = (FStar_Syntax_Print.tag_of_term t)
in (let _143_582 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _143_583 _143_582)))
in (FStar_All.failwith _143_584))
end))





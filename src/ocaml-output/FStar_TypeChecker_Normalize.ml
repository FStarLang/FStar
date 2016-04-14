
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
| UnfoldUntil (_53_9) -> begin
_53_9
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
| Clos (_53_12) -> begin
_53_12
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_15) -> begin
_53_15
end))

# 67 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_18, t, _53_21) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_25 -> begin
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
| Arg (_53_32) -> begin
_53_32
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_35) -> begin
_53_35
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 = (fun projectee -> (match (projectee) with
| MemoLazy (_53_38) -> begin
_53_38
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_41) -> begin
_53_41
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_44) -> begin
_53_44
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_47) -> begin
_53_47
end))

# 88 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_50) -> begin
_53_50
end))

# 90 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 102 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 103 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_56) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 108 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _142_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _142_173 (FStar_String.concat "; "))))

# 111 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_63, _53_65) -> begin
(closure_to_string c)
end
| MemoLazy (_53_69) -> begin
"MemoLazy"
end
| Abs (_53_72, bs, _53_75, _53_77, _53_79) -> begin
(let _142_176 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _142_176))
end
| _53_83 -> begin
"Match"
end))

# 117 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _142_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _142_179 (FStar_String.concat "; "))))

# 120 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 125 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_90 -> begin
false
end))

# 129 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_97 -> begin
(let _142_195 = (let _142_194 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _142_194))
in (FStar_All.failwith _142_195))
end)

# 141 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 143 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 148 "FStar.TypeChecker.Normalize.fst"
let _53_118 = (FStar_List.fold_left (fun _53_109 u -> (match (_53_109) with
| (cur_kernel, cur_max, out) -> begin
(
# 150 "FStar.TypeChecker.Normalize.fst"
let _53_113 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_113) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_53_118) with
| (_53_115, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 161 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 162 "FStar.TypeChecker.Normalize.fst"
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
| _53_135 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_128 -> begin
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
(let _142_210 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _142_210 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _142_212 = (aux u)
in (FStar_List.map (fun _142_211 -> FStar_Syntax_Syntax.U_succ (_142_211)) _142_212))
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
let _53_166 = (log cfg (fun _53_165 -> (match (()) with
| () -> begin
(let _142_236 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_235 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _142_236 _142_235)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _53_170 -> begin
(
# 205 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_173) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _142_242 = (let _142_241 = (let _142_240 = (closure_as_term_delayed cfg env t')
in (u, _142_240))
in FStar_Syntax_Syntax.Tm_uvar (_142_241))
in (mk _142_242 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _142_244 = (let _142_243 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_142_243))
in (mk _142_244 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _142_245 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _142_245))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_198) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_53_211) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 234 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _53_217) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _142_251 = (FStar_List.fold_left (fun env' _53_224 -> (match (_53_224) with
| (t, _53_223) -> begin
(let _142_250 = (let _142_249 = (let _142_248 = (FStar_Util.mk_ref None)
in (env, t, _142_248))
in Clos (_142_249))
in (_142_250)::env')
end)) env args)
in (closure_as_term cfg _142_251 body))
end
| _53_226 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _53_228 -> begin
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
let _53_238 = (closures_as_binders_delayed cfg env bs)
in (match (_53_238) with
| (bs, env) -> begin
(
# 248 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _142_254 = (let _142_253 = (let _142_252 = (close_lcomp_opt cfg env lopt)
in (bs, body, _142_252))
in FStar_Syntax_Syntax.Tm_abs (_142_253))
in (mk _142_254 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 252 "FStar.TypeChecker.Normalize.fst"
let _53_246 = (closures_as_binders_delayed cfg env bs)
in (match (_53_246) with
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
let _53_254 = (let _142_256 = (let _142_255 = (FStar_Syntax_Syntax.mk_binder x)
in (_142_255)::[])
in (closures_as_binders_delayed cfg env _142_256))
in (match (_53_254) with
| (x, env) -> begin
(
# 258 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _142_260 = (let _142_259 = (let _142_258 = (let _142_257 = (FStar_List.hd x)
in (FStar_All.pipe_right _142_257 Prims.fst))
in (_142_258, phi))
in FStar_Syntax_Syntax.Tm_refine (_142_259))
in (mk _142_260 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _142_266 = (let _142_265 = (let _142_264 = (closure_as_term_delayed cfg env t1)
in (let _142_263 = (let _142_262 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _142_261 -> FStar_Util.Inl (_142_261)) _142_262))
in (_142_264, _142_263, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_142_265))
in (mk _142_266 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _142_272 = (let _142_271 = (let _142_270 = (closure_as_term_delayed cfg env t1)
in (let _142_269 = (let _142_268 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _142_267 -> FStar_Util.Inr (_142_267)) _142_268))
in (_142_270, _142_269, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_142_271))
in (mk _142_272 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _142_277 = (let _142_276 = (let _142_275 = (closure_as_term_delayed cfg env t')
in (let _142_274 = (let _142_273 = (FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env)))
in FStar_Syntax_Syntax.Meta_pattern (_142_273))
in (_142_275, _142_274)))
in FStar_Syntax_Syntax.Tm_meta (_142_276))
in (mk _142_277 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _142_280 = (let _142_279 = (let _142_278 = (closure_as_term_delayed cfg env t')
in (_142_278, m))
in FStar_Syntax_Syntax.Tm_meta (_142_279))
in (mk _142_280 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 275 "FStar.TypeChecker.Normalize.fst"
let env0 = env
in (
# 276 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env _53_286 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 277 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 278 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 279 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_292) -> begin
body
end
| FStar_Util.Inl (_53_295) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 282 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 282 "FStar.TypeChecker.Normalize.fst"
let _53_298 = lb
in {FStar_Syntax_Syntax.lbname = _53_298.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_298.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_298.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_302, lbs), body) -> begin
(
# 286 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 287 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _53_311 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 288 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_315 env -> (Dummy)::env) lbs env_univs)
end
in (
# 291 "FStar.TypeChecker.Normalize.fst"
let _53_319 = lb
in (let _142_292 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _142_291 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_319.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_319.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _142_292; FStar_Syntax_Syntax.lbeff = _53_319.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _142_291}))))))
in (
# 293 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 294 "FStar.TypeChecker.Normalize.fst"
let body = (
# 295 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _53_322 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 300 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 301 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _53_337 -> (match (_53_337) with
| (pat, w_opt, tm) -> begin
(
# 302 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_342) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 306 "FStar.TypeChecker.Normalize.fst"
let _53_352 = (norm_pat env hd)
in (match (_53_352) with
| (hd, env') -> begin
(
# 307 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _142_304 = (norm_pat env p)
in (Prims.fst _142_304)))))
in ((
# 308 "FStar.TypeChecker.Normalize.fst"
let _53_355 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_355.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_355.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 310 "FStar.TypeChecker.Normalize.fst"
let _53_372 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_363 _53_366 -> (match ((_53_363, _53_366)) with
| ((pats, env), (p, b)) -> begin
(
# 311 "FStar.TypeChecker.Normalize.fst"
let _53_369 = (norm_pat env p)
in (match (_53_369) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_53_372) with
| (pats, env) -> begin
((
# 313 "FStar.TypeChecker.Normalize.fst"
let _53_373 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _53_373.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_373.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 315 "FStar.TypeChecker.Normalize.fst"
let x = (
# 315 "FStar.TypeChecker.Normalize.fst"
let _53_377 = x
in (let _142_307 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_377.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_377.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_307}))
in ((
# 316 "FStar.TypeChecker.Normalize.fst"
let _53_380 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_380.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_380.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 318 "FStar.TypeChecker.Normalize.fst"
let x = (
# 318 "FStar.TypeChecker.Normalize.fst"
let _53_384 = x
in (let _142_308 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_384.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_384.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_308}))
in ((
# 319 "FStar.TypeChecker.Normalize.fst"
let _53_387 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_387.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_387.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 321 "FStar.TypeChecker.Normalize.fst"
let x = (
# 321 "FStar.TypeChecker.Normalize.fst"
let _53_393 = x
in (let _142_309 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_393.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_393.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_309}))
in (
# 322 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 323 "FStar.TypeChecker.Normalize.fst"
let _53_397 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _53_397.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_397.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 324 "FStar.TypeChecker.Normalize.fst"
let _53_401 = (norm_pat env pat)
in (match (_53_401) with
| (pat, env) -> begin
(
# 325 "FStar.TypeChecker.Normalize.fst"
let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
(let _142_310 = (closure_as_term cfg env w)
in Some (_142_310))
end)
in (
# 328 "FStar.TypeChecker.Normalize.fst"
let tm = (closure_as_term cfg env tm)
in (pat, w_opt, tm)))
end)))
end))
in (let _142_313 = (let _142_312 = (let _142_311 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in (head, _142_311))
in FStar_Syntax_Syntax.Tm_match (_142_312))
in (mk _142_313 t.FStar_Syntax_Syntax.pos))))
end))
end)))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| _53_411 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _53_414 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _53_420 -> begin
(FStar_List.map (fun _53_423 -> (match (_53_423) with
| (x, imp) -> begin
(let _142_321 = (closure_as_term_delayed cfg env x)
in (_142_321, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (
# 345 "FStar.TypeChecker.Normalize.fst"
let _53_439 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_429 _53_432 -> (match ((_53_429, _53_432)) with
| ((env, out), (b, imp)) -> begin
(
# 346 "FStar.TypeChecker.Normalize.fst"
let b = (
# 346 "FStar.TypeChecker.Normalize.fst"
let _53_433 = b
in (let _142_327 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_433.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_433.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_327}))
in (
# 347 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_53_439) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _53_445 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _142_331 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _142_331))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _142_332 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _142_332))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 359 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 360 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 361 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _53_4 -> (match (_53_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _142_334 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_142_334))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 364 "FStar.TypeChecker.Normalize.fst"
let _53_459 = c
in {FStar_Syntax_Syntax.effect_name = _53_459.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _53_5 -> (match (_53_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _142_341 = (
# 370 "FStar.TypeChecker.Normalize.fst"
let _53_467 = lc
in (let _142_340 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _53_467.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _142_340; FStar_Syntax_Syntax.cflags = _53_467.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_469 -> (match (()) with
| () -> begin
(let _142_339 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _142_339))
end))}))
in Some (_142_341))
end))

# 377 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 378 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 378 "FStar.TypeChecker.Normalize.fst"
let _53_474 = t
in {FStar_Syntax_Syntax.n = _53_474.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_474.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_474.FStar_Syntax_Syntax.vars}))
in (
# 379 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_483 -> begin
None
end))
in (
# 383 "FStar.TypeChecker.Normalize.fst"
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
| _53_561 -> begin
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
| _53_604 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _53_631)::(_53_622, (arg, _53_625))::[] -> begin
arg
end
| _53_635 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _53_639)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _53_645)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_649 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _142_352 = (FStar_Syntax_Subst.compress t)
in _142_352.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_667::[], body, _53_671) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_679 -> begin
tm
end)
end
| _53_681 -> begin
tm
end)
end
| _53_683 -> begin
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
| _53_685 -> begin
tm
end)
end))))

# 436 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 438 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 439 "FStar.TypeChecker.Normalize.fst"
let _53_692 = (log cfg (fun _53_691 -> (match (()) with
| () -> begin
(let _142_379 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_378 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _142_379 _142_378)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_695) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 453 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _142_383 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_383)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 459 "FStar.TypeChecker.Normalize.fst"
let us = (let _142_385 = (let _142_384 = (FStar_List.map (norm_universe cfg env) us)
in (_142_384, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_142_385))
in (
# 460 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(
# 467 "FStar.TypeChecker.Normalize.fst"
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
# 477 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _53_756)::stack -> begin
(
# 481 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_764 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_766 -> begin
(let _142_389 = (let _142_388 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _142_388))
in (FStar_All.failwith _142_389))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_770) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 496 "FStar.TypeChecker.Normalize.fst"
let _53_783 = (log cfg (fun _53_782 -> (match (()) with
| () -> begin
(let _142_392 = (FStar_Syntax_Print.term_to_string t)
in (let _142_391 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _142_392 _142_391)))
end)))
in (match ((let _142_393 = (FStar_Syntax_Subst.compress t')
in _142_393.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_786) -> begin
(norm cfg env stack t')
end
| _53_789 -> begin
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
| Meta (_53_799)::_53_797 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_53_805)::_53_803 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_53_811)::_53_809 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _53_817, _53_819)::stack -> begin
(match (c) with
| Univ (_53_824) -> begin
(norm cfg ((c)::env) stack t)
end
| _53_827 -> begin
(
# 524 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _53_830::[] -> begin
body
end
| _53_834::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 528 "FStar.TypeChecker.Normalize.fst"
let _53_838 = (log cfg (fun _53_837 -> (match (()) with
| () -> begin
(let _142_395 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_395))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 533 "FStar.TypeChecker.Normalize.fst"
let _53_844 = (set_memo r (env, t))
in (
# 534 "FStar.TypeChecker.Normalize.fst"
let _53_847 = (log cfg (fun _53_846 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_397 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_397))
end else begin
(
# 542 "FStar.TypeChecker.Normalize.fst"
let _53_865 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_865) with
| (bs, body, opening) -> begin
(
# 543 "FStar.TypeChecker.Normalize.fst"
let lopt = (match (lopt) with
| None -> begin
None
end
| Some (l) -> begin
(let _142_401 = (let _142_399 = (let _142_398 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _142_398))
in (FStar_All.pipe_right _142_399 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _142_401 (fun _142_400 -> Some (_142_400))))
end)
in (
# 546 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_871 -> (Dummy)::env) env))
in (
# 547 "FStar.TypeChecker.Normalize.fst"
let _53_875 = (log cfg (fun _53_874 -> (match (()) with
| () -> begin
(let _142_405 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _142_405))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 552 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_883 stack -> (match (_53_883) with
| (a, aq) -> begin
(let _142_412 = (let _142_411 = (let _142_410 = (let _142_409 = (let _142_408 = (FStar_Util.mk_ref None)
in (env, a, _142_408))
in Clos (_142_409))
in (_142_410, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_142_411))
in (_142_412)::stack)
end)) args))
in (
# 553 "FStar.TypeChecker.Normalize.fst"
let _53_887 = (log cfg (fun _53_886 -> (match (()) with
| () -> begin
(let _142_414 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _142_414))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(
# 560 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 561 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_refine (((
# 561 "FStar.TypeChecker.Normalize.fst"
let _53_897 = x
in {FStar_Syntax_Syntax.ppname = _53_897.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_897.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_901 -> begin
(let _142_415 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_415))
end)
end else begin
(
# 564 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 565 "FStar.TypeChecker.Normalize.fst"
let _53_905 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_53_905) with
| (closing, f) -> begin
(
# 566 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 567 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_418 = (let _142_417 = (let _142_416 = (FStar_Syntax_Subst.close closing f)
in ((
# 567 "FStar.TypeChecker.Normalize.fst"
let _53_907 = x
in {FStar_Syntax_Syntax.ppname = _53_907.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_907.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _142_416))
in FStar_Syntax_Syntax.Tm_refine (_142_417))
in (mk _142_418 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_419 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_419))
end else begin
(
# 573 "FStar.TypeChecker.Normalize.fst"
let _53_916 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_916) with
| (bs, c) -> begin
(
# 574 "FStar.TypeChecker.Normalize.fst"
let c = (let _142_422 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_918 -> (Dummy)::env) env))
in (norm_comp cfg _142_422 c))
in (
# 575 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_423 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _142_423 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _53_946 -> begin
(
# 584 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 585 "FStar.TypeChecker.Normalize.fst"
let _53_949 = (log cfg (fun _53_948 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 586 "FStar.TypeChecker.Normalize.fst"
let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _142_425 = (norm cfg env [] t)
in FStar_Util.Inl (_142_425))
end
| FStar_Util.Inr (c) -> begin
(let _142_426 = (norm_comp cfg env c)
in FStar_Util.Inr (_142_426))
end)
in (let _142_427 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, tc, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_427)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 593 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 597 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_430 = (let _142_429 = (let _142_428 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _142_428))
in Clos (_142_429))
in (_142_430)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_53_970, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_982); FStar_Syntax_Syntax.lbunivs = _53_980; FStar_Syntax_Syntax.lbtyp = _53_978; FStar_Syntax_Syntax.lbeff = _53_976; FStar_Syntax_Syntax.lbdef = _53_974}::_53_972), _53_988) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 614 "FStar.TypeChecker.Normalize.fst"
let _53_1010 = (FStar_List.fold_right (fun lb _53_999 -> (match (_53_999) with
| (rec_env, memos, i) -> begin
(
# 615 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _142_433 = (
# 615 "FStar.TypeChecker.Normalize.fst"
let _53_1000 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1000.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1000.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _142_433))
in (
# 616 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 617 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 618 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_53_1010) with
| (rec_env, memos, _53_1009) -> begin
(
# 620 "FStar.TypeChecker.Normalize.fst"
let _53_1013 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 621 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _142_440 = (let _142_439 = (let _142_438 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _142_438))
in Clos (_142_439))
in (_142_440)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _53_1025::_53_1023 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1030) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 633 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _53_1037 -> begin
(norm cfg env stack head)
end)
end
| _53_1039 -> begin
(
# 640 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 641 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _142_441 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_142_441))
end
| _53_1044 -> begin
m
end)
in (
# 645 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1052 -> (match (_53_1052) with
| (a, imp) -> begin
(let _142_446 = (norm cfg env [] a)
in (_142_446, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 656 "FStar.TypeChecker.Normalize.fst"
let _53_1058 = comp
in (let _142_451 = (let _142_450 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_142_450))
in {FStar_Syntax_Syntax.n = _142_451; FStar_Syntax_Syntax.tk = _53_1058.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1058.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1058.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 659 "FStar.TypeChecker.Normalize.fst"
let _53_1062 = comp
in (let _142_453 = (let _142_452 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_142_452))
in {FStar_Syntax_Syntax.n = _142_453; FStar_Syntax_Syntax.tk = _53_1062.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1062.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1062.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 662 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1070 -> (match (_53_1070) with
| (a, i) -> begin
(let _142_457 = (norm cfg env [] a)
in (_142_457, i))
end)))))
in (
# 663 "FStar.TypeChecker.Normalize.fst"
let _53_1071 = comp
in (let _142_461 = (let _142_460 = (
# 663 "FStar.TypeChecker.Normalize.fst"
let _53_1073 = ct
in (let _142_459 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _142_458 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1073.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _142_459; FStar_Syntax_Syntax.effect_args = _142_458; FStar_Syntax_Syntax.flags = _53_1073.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_142_460))
in {FStar_Syntax_Syntax.n = _142_461; FStar_Syntax_Syntax.tk = _53_1071.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1071.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1071.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1079 -> (match (_53_1079) with
| (x, imp) -> begin
(let _142_466 = (
# 667 "FStar.TypeChecker.Normalize.fst"
let _53_1080 = x
in (let _142_465 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1080.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1080.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_465}))
in (_142_466, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 671 "FStar.TypeChecker.Normalize.fst"
let _53_1093 = (FStar_List.fold_left (fun _53_1087 b -> (match (_53_1087) with
| (nbs', env) -> begin
(
# 672 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_53_1093) with
| (nbs, _53_1092) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 686 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 690 "FStar.TypeChecker.Normalize.fst"
let _53_1110 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 694 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 695 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _142_476 = (
# 696 "FStar.TypeChecker.Normalize.fst"
let _53_1123 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1123.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1123.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1123.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _142_476))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 702 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 706 "FStar.TypeChecker.Normalize.fst"
let _53_1166 = (log cfg (fun _53_1165 -> (match (()) with
| () -> begin
(let _142_478 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _142_478))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 711 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 712 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 714 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1173, a) -> begin
(
# 718 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 723 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _142_479 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _142_479)))
end
| Match (env, branches, r)::stack -> begin
(
# 727 "FStar.TypeChecker.Normalize.fst"
let _53_1194 = (log cfg (fun _53_1193 -> (match (()) with
| () -> begin
(let _142_481 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _142_481))
end)))
in (
# 728 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _53_1197 -> (match (()) with
| () -> begin
(
# 729 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 730 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 730 "FStar.TypeChecker.Normalize.fst"
let _53_1199 = cfg
in (let _142_484 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _53_1199.steps; tcenv = _53_1199.tcenv; delta_level = _142_484}))
in (
# 731 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 735 "FStar.TypeChecker.Normalize.fst"
let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1207 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 739 "FStar.TypeChecker.Normalize.fst"
let _53_1212 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1212) with
| (p, wopt, e) -> begin
(
# 740 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_492 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _142_492 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 742 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _142_493 = (norm_or_whnf env w)
in Some (_142_493))
end)
in (
# 745 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _142_494 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _142_494))))))
end))
in (
# 749 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1226) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1251 -> begin
false
end))
in (
# 756 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 760 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 761 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 765 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 769 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 770 "FStar.TypeChecker.Normalize.fst"
let _53_1268 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1268) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 773 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 774 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1274) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1291) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1298 -> begin
(let _142_511 = (not ((is_cons head)))
in FStar_Util.Inr (_142_511))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _142_512 = (FStar_Syntax_Util.un_uinst head)
in _142_512.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1306 -> begin
(let _142_513 = (not ((is_cons head)))
in FStar_Util.Inr (_142_513))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _53_1316)::rest_a, (p, _53_1322)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1330 -> begin
FStar_Util.Inr (false)
end))
in (
# 807 "FStar.TypeChecker.Normalize.fst"
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
# 818 "FStar.TypeChecker.Normalize.fst"
let _53_1348 = (log cfg (fun _53_1347 -> (match (()) with
| () -> begin
(let _142_524 = (FStar_Syntax_Print.pat_to_string p)
in (let _142_523 = (let _142_522 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _142_522 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _142_524 _142_523)))
end)))
in (
# 823 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env t -> (let _142_529 = (let _142_528 = (let _142_527 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _142_527))
in Clos (_142_528))
in (_142_529)::env)) env s)
in (let _142_530 = (guard_when_clause wopt b rest)
in (norm cfg env stack _142_530))))
end)
end))
in (matches t branches)))))))
end))

# 828 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 829 "FStar.TypeChecker.Normalize.fst"
let d = (match ((FStar_Util.find_map s (fun _53_6 -> (match (_53_6) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1359 -> begin
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

# 836 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _142_542 = (config s e)
in (norm _142_542 [] [] t)))

# 837 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _142_549 = (config s e)
in (norm_comp _142_549 [] t)))

# 838 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _142_554 = (config [] env)
in (norm_universe _142_554 [] u)))

# 840 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _142_559 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _142_559)))

# 841 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _142_565 = (let _142_564 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _142_564 [] c))
in (FStar_Syntax_Print.comp_to_string _142_565)))

# 843 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 844 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 845 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 846 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 849 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _142_576 = (let _142_575 = (let _142_574 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _142_574))
in FStar_Syntax_Syntax.Tm_refine (_142_575))
in (mk _142_576 t0.FStar_Syntax_Syntax.pos))
end
| _53_1393 -> begin
t
end))
end
| _53_1395 -> begin
t
end)))
in (aux t))))

# 858 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 859 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _142_581 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _142_581 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 863 "FStar.TypeChecker.Normalize.fst"
let _53_1406 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_1406) with
| (binders, cdef) -> begin
(
# 864 "FStar.TypeChecker.Normalize.fst"
let inst = (let _142_585 = (let _142_584 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_142_584)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_1410 _53_1414 -> (match ((_53_1410, _53_1414)) with
| ((x, _53_1409), (t, _53_1413)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _142_585))
in (
# 865 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 866 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 866 "FStar.TypeChecker.Normalize.fst"
let _53_1417 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_1417.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_1417.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1417.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 869 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _53_1420 _53_1422 _53_1424 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 870 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _53_1426 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 873 "FStar.TypeChecker.Normalize.fst"
let _53_1433 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_53_1433) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1436 -> begin
(
# 877 "FStar.TypeChecker.Normalize.fst"
let _53_1439 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1439) with
| (binders, args) -> begin
(let _142_598 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _142_597 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _142_596 -> Some (_142_596)))
in (FStar_Syntax_Util.abs binders _142_598 _142_597)))
end))
end)
end))
end
| _53_1441 -> begin
(let _142_601 = (let _142_600 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_599 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _142_600 _142_599)))
in (FStar_All.failwith _142_601))
end))





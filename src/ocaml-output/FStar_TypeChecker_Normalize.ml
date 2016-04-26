
open Prims
# 31 "FStar.TypeChecker.Normalize.fst"
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

# 58 "FStar.TypeChecker.Normalize.fst"
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

# 65 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_17, t, _53_20) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_24 -> begin
"dummy"
end))

# 69 "FStar.TypeChecker.Normalize.fst"
type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}

# 71 "FStar.TypeChecker.Normalize.fst"
let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))

# 75 "FStar.TypeChecker.Normalize.fst"
type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list

# 77 "FStar.TypeChecker.Normalize.fst"
type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

# 79 "FStar.TypeChecker.Normalize.fst"
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

# 88 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 100 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 102 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_55) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 106 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _142_173 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _142_173 (FStar_String.concat "; "))))

# 109 "FStar.TypeChecker.Normalize.fst"
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

# 115 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _142_179 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _142_179 (FStar_String.concat "; "))))

# 118 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 123 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_89 -> begin
false
end))

# 127 "FStar.TypeChecker.Normalize.fst"
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

# 131 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 143 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 148 "FStar.TypeChecker.Normalize.fst"
let _53_117 = (FStar_List.fold_left (fun _53_108 u -> (match (_53_108) with
| (cur_kernel, cur_max, out) -> begin
(
# 150 "FStar.TypeChecker.Normalize.fst"
let _53_112 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_112) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_53_117) with
| (_53_114, u, out) -> begin
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
| _53_134 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_127 -> begin
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

# 190 "FStar.TypeChecker.Normalize.fst"
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (
# 201 "FStar.TypeChecker.Normalize.fst"
let _53_165 = (log cfg (fun _53_164 -> (match (()) with
| () -> begin
(let _142_236 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_235 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _142_236 _142_235)))
end)))
in (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
t
end
| _53_169 -> begin
(
# 205 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_172) -> begin
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
| Univ (_53_197) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (_53_210) when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(
# 234 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, _53_216) when ((FStar_List.length binders) = (FStar_List.length args)) -> begin
(let _142_251 = (FStar_List.fold_left (fun env' _53_223 -> (match (_53_223) with
| (t, _53_222) -> begin
(let _142_250 = (let _142_249 = (let _142_248 = (FStar_Util.mk_ref None)
in (env, t, _142_248))
in Clos (_142_249))
in (_142_250)::env')
end)) env args)
in (closure_as_term cfg _142_251 body))
end
| _53_225 -> begin
(mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)
end))
end
| _53_227 -> begin
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
let _53_237 = (closures_as_binders_delayed cfg env bs)
in (match (_53_237) with
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
let _53_245 = (closures_as_binders_delayed cfg env bs)
in (match (_53_245) with
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
let _53_253 = (let _142_256 = (let _142_255 = (FStar_Syntax_Syntax.mk_binder x)
in (_142_255)::[])
in (closures_as_binders_delayed cfg env _142_256))
in (match (_53_253) with
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
let env = (FStar_List.fold_left (fun env _53_285 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (
# 277 "FStar.TypeChecker.Normalize.fst"
let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 278 "FStar.TypeChecker.Normalize.fst"
let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (
# 279 "FStar.TypeChecker.Normalize.fst"
let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (_53_291) -> begin
body
end
| FStar_Util.Inl (_53_294) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (
# 282 "FStar.TypeChecker.Normalize.fst"
let lb = (
# 282 "FStar.TypeChecker.Normalize.fst"
let _53_297 = lb
in {FStar_Syntax_Syntax.lbname = _53_297.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_297.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = _53_297.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((false, (lb)::[]), body))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((_53_301, lbs), body) -> begin
(
# 286 "FStar.TypeChecker.Normalize.fst"
let norm_one_lb = (fun env lb -> (
# 287 "FStar.TypeChecker.Normalize.fst"
let env_univs = (FStar_List.fold_right (fun _53_310 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (
# 288 "FStar.TypeChecker.Normalize.fst"
let env = if (FStar_Syntax_Syntax.is_top_level lbs) then begin
env_univs
end else begin
(FStar_List.fold_right (fun _53_314 env -> (Dummy)::env) lbs env_univs)
end
in (
# 291 "FStar.TypeChecker.Normalize.fst"
let _53_318 = lb
in (let _142_292 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _142_291 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _53_318.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _53_318.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _142_292; FStar_Syntax_Syntax.lbeff = _53_318.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _142_291}))))))
in (
# 293 "FStar.TypeChecker.Normalize.fst"
let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (
# 294 "FStar.TypeChecker.Normalize.fst"
let body = (
# 295 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun _53_321 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((true, lbs), body))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 300 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term cfg env head)
in (
# 301 "FStar.TypeChecker.Normalize.fst"
let norm_one_branch = (fun env _53_336 -> (match (_53_336) with
| (pat, w_opt, tm) -> begin
(
# 302 "FStar.TypeChecker.Normalize.fst"
let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_341) -> begin
(p, env)
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 306 "FStar.TypeChecker.Normalize.fst"
let _53_351 = (norm_pat env hd)
in (match (_53_351) with
| (hd, env') -> begin
(
# 307 "FStar.TypeChecker.Normalize.fst"
let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (let _142_304 = (norm_pat env p)
in (Prims.fst _142_304)))))
in ((
# 308 "FStar.TypeChecker.Normalize.fst"
let _53_354 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_354.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_354.FStar_Syntax_Syntax.p}), env'))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(
# 310 "FStar.TypeChecker.Normalize.fst"
let _53_371 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_362 _53_365 -> (match ((_53_362, _53_365)) with
| ((pats, env), (p, b)) -> begin
(
# 311 "FStar.TypeChecker.Normalize.fst"
let _53_368 = (norm_pat env p)
in (match (_53_368) with
| (p, env) -> begin
(((p, b))::pats, env)
end))
end)) ([], env)))
in (match (_53_371) with
| (pats, env) -> begin
((
# 313 "FStar.TypeChecker.Normalize.fst"
let _53_372 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _53_372.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_372.FStar_Syntax_Syntax.p}), env)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(
# 315 "FStar.TypeChecker.Normalize.fst"
let x = (
# 315 "FStar.TypeChecker.Normalize.fst"
let _53_376 = x
in (let _142_307 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_376.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_376.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_307}))
in ((
# 316 "FStar.TypeChecker.Normalize.fst"
let _53_379 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_379.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_379.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(
# 318 "FStar.TypeChecker.Normalize.fst"
let x = (
# 318 "FStar.TypeChecker.Normalize.fst"
let _53_383 = x
in (let _142_308 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_383.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_383.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_308}))
in ((
# 319 "FStar.TypeChecker.Normalize.fst"
let _53_386 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_386.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_386.FStar_Syntax_Syntax.p}), (Dummy)::env))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(
# 321 "FStar.TypeChecker.Normalize.fst"
let x = (
# 321 "FStar.TypeChecker.Normalize.fst"
let _53_392 = x
in (let _142_309 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_392.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_392.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_309}))
in (
# 322 "FStar.TypeChecker.Normalize.fst"
let t = (closure_as_term cfg env t)
in ((
# 323 "FStar.TypeChecker.Normalize.fst"
let _53_396 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t)); FStar_Syntax_Syntax.ty = _53_396.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_396.FStar_Syntax_Syntax.p}), env)))
end))
in (
# 324 "FStar.TypeChecker.Normalize.fst"
let _53_400 = (norm_pat env pat)
in (match (_53_400) with
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
| _53_410 when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
(closure_as_term cfg env t)
end
| [] -> begin
t
end
| _53_413 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] when (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)))) -> begin
args
end
| _53_419 -> begin
(FStar_List.map (fun _53_422 -> (match (_53_422) with
| (x, imp) -> begin
(let _142_321 = (closure_as_term_delayed cfg env x)
in (_142_321, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.binders * closure Prims.list) = (fun cfg env bs -> (
# 345 "FStar.TypeChecker.Normalize.fst"
let _53_438 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _53_428 _53_431 -> (match ((_53_428, _53_431)) with
| ((env, out), (b, imp)) -> begin
(
# 346 "FStar.TypeChecker.Normalize.fst"
let b = (
# 346 "FStar.TypeChecker.Normalize.fst"
let _53_432 = b
in (let _142_327 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_432.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_432.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_327}))
in (
# 347 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_53_438) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_right cfg.steps (FStar_List.contains BetaUVars)) -> begin
c
end
| _53_444 -> begin
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
let _53_458 = c
in {FStar_Syntax_Syntax.effect_name = _53_458.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(let _142_342 = (let _142_341 = (
# 369 "FStar.TypeChecker.Normalize.fst"
let _53_466 = lc
in (let _142_340 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _53_466.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _142_340; FStar_Syntax_Syntax.cflags = _53_466.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_468 -> (match (()) with
| () -> begin
(let _142_339 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _142_339))
end))}))
in FStar_Util.Inl (_142_341))
in Some (_142_342))
end
| _53_470 -> begin
lopt
end))

# 371 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 378 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 378 "FStar.TypeChecker.Normalize.fst"
let _53_475 = t
in {FStar_Syntax_Syntax.n = _53_475.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_475.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_475.FStar_Syntax_Syntax.vars}))
in (
# 379 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_484 -> begin
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
| _53_562 -> begin
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
| _53_605 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _53_632)::(_53_623, (arg, _53_626))::[] -> begin
arg
end
| _53_636 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _53_640)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _53_646)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_650 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _142_353 = (FStar_Syntax_Subst.compress t)
in _142_353.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_668::[], body, _53_672) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_680 -> begin
tm
end)
end
| _53_682 -> begin
tm
end)
end
| _53_684 -> begin
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
| _53_686 -> begin
tm
end)
end))))

# 429 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 438 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 439 "FStar.TypeChecker.Normalize.fst"
let _53_693 = (log cfg (fun _53_692 -> (match (()) with
| () -> begin
(let _142_380 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_379 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _142_380 _142_379)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_696) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 454 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _142_384 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_384)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 460 "FStar.TypeChecker.Normalize.fst"
let us = (let _142_386 = (let _142_385 = (FStar_List.map (norm_universe cfg env) us)
in (_142_385, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_142_386))
in (
# 461 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(
# 465 "FStar.TypeChecker.Normalize.fst"
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
# 475 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _53_758)::stack -> begin
(
# 479 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_766 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_768 -> begin
(let _142_390 = (let _142_389 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _142_389))
in (FStar_All.failwith _142_390))
end)
end else begin
(norm cfg env stack t)
end)
end)
end)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_772) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 494 "FStar.TypeChecker.Normalize.fst"
let _53_785 = (log cfg (fun _53_784 -> (match (()) with
| () -> begin
(let _142_393 = (FStar_Syntax_Print.term_to_string t)
in (let _142_392 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _142_393 _142_392)))
end)))
in (match ((let _142_394 = (FStar_Syntax_Subst.compress t')
in _142_394.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_788) -> begin
(norm cfg env stack t')
end
| _53_791 -> begin
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
| Meta (_53_801)::_53_799 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_53_807)::_53_805 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_53_813)::_53_811 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _53_819, _53_821)::stack -> begin
(match (c) with
| Univ (_53_826) -> begin
(norm cfg ((c)::env) stack t)
end
| _53_829 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _53_832::[] -> begin
(match (lopt) with
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(
# 533 "FStar.TypeChecker.Normalize.fst"
let _53_838 = (log cfg (fun _53_837 -> (match (()) with
| () -> begin
(let _142_396 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_396))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(
# 537 "FStar.TypeChecker.Normalize.fst"
let _53_844 = (log cfg (fun _53_843 -> (match (()) with
| () -> begin
(let _142_398 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_398))
end)))
in (norm cfg ((c)::env) stack body))
end
| _53_847 -> begin
(
# 542 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 542 "FStar.TypeChecker.Normalize.fst"
let _53_848 = cfg
in {steps = (WHNF)::cfg.steps; tcenv = _53_848.tcenv; delta_level = _53_848.delta_level})
in (let _142_399 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_399)))
end)
end
| _53_853::tl -> begin
(
# 546 "FStar.TypeChecker.Normalize.fst"
let _53_856 = (log cfg (fun _53_855 -> (match (()) with
| () -> begin
(let _142_401 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _142_401))
end)))
in (
# 547 "FStar.TypeChecker.Normalize.fst"
let body = (mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, lopt))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack body)))
end)
end)
end
| MemoLazy (r)::stack -> begin
(
# 553 "FStar.TypeChecker.Normalize.fst"
let _53_863 = (set_memo r (env, t))
in (
# 554 "FStar.TypeChecker.Normalize.fst"
let _53_866 = (log cfg (fun _53_865 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_403 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_403))
end else begin
(
# 562 "FStar.TypeChecker.Normalize.fst"
let _53_884 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_53_884) with
| (bs, body, opening) -> begin
(
# 563 "FStar.TypeChecker.Normalize.fst"
let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _142_409 = (let _142_407 = (let _142_405 = (let _142_404 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _142_404))
in (FStar_All.pipe_right _142_405 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _142_407 (fun _142_406 -> FStar_Util.Inl (_142_406))))
in (FStar_All.pipe_right _142_409 (fun _142_408 -> Some (_142_408))))
end
| _53_889 -> begin
lopt
end)
in (
# 566 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_892 -> (Dummy)::env) env))
in (
# 567 "FStar.TypeChecker.Normalize.fst"
let _53_896 = (log cfg (fun _53_895 -> (match (()) with
| () -> begin
(let _142_413 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _142_413))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body))))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 572 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_904 stack -> (match (_53_904) with
| (a, aq) -> begin
(let _142_420 = (let _142_419 = (let _142_418 = (let _142_417 = (let _142_416 = (FStar_Util.mk_ref None)
in (env, a, _142_416))
in Clos (_142_417))
in (_142_418, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_142_419))
in (_142_420)::stack)
end)) args))
in (
# 573 "FStar.TypeChecker.Normalize.fst"
let _53_908 = (log cfg (fun _53_907 -> (match (()) with
| () -> begin
(let _142_422 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _142_422))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(match ((env, stack)) with
| ([], []) -> begin
(
# 580 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 581 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_refine (((
# 581 "FStar.TypeChecker.Normalize.fst"
let _53_918 = x
in {FStar_Syntax_Syntax.ppname = _53_918.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_918.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), f))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| _53_922 -> begin
(let _142_423 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_423))
end)
end else begin
(
# 584 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 585 "FStar.TypeChecker.Normalize.fst"
let _53_926 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_53_926) with
| (closing, f) -> begin
(
# 586 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 587 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_426 = (let _142_425 = (let _142_424 = (FStar_Syntax_Subst.close closing f)
in ((
# 587 "FStar.TypeChecker.Normalize.fst"
let _53_928 = x
in {FStar_Syntax_Syntax.ppname = _53_928.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_928.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _142_424))
in FStar_Syntax_Syntax.Tm_refine (_142_425))
in (mk _142_426 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _142_427 = (closure_as_term cfg env t)
in (rebuild cfg env stack _142_427))
end else begin
(
# 593 "FStar.TypeChecker.Normalize.fst"
let _53_937 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_53_937) with
| (bs, c) -> begin
(
# 594 "FStar.TypeChecker.Normalize.fst"
let c = (let _142_430 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _53_939 -> (Dummy)::env) env))
in (norm_comp cfg _142_430 c))
in (
# 595 "FStar.TypeChecker.Normalize.fst"
let t = (let _142_431 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _142_431 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _53_967 -> begin
(
# 604 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 605 "FStar.TypeChecker.Normalize.fst"
let _53_970 = (log cfg (fun _53_969 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 606 "FStar.TypeChecker.Normalize.fst"
let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _142_433 = (norm cfg env [] t)
in FStar_Util.Inl (_142_433))
end
| FStar_Util.Inr (c) -> begin
(let _142_434 = (norm_comp cfg env c)
in FStar_Util.Inr (_142_434))
end)
in (let _142_435 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, tc, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _142_435)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 613 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 617 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_438 = (let _142_437 = (let _142_436 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _142_436))
in Clos (_142_437))
in (_142_438)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_53_991, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_1003); FStar_Syntax_Syntax.lbunivs = _53_1001; FStar_Syntax_Syntax.lbtyp = _53_999; FStar_Syntax_Syntax.lbeff = _53_997; FStar_Syntax_Syntax.lbdef = _53_995}::_53_993), _53_1009) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 634 "FStar.TypeChecker.Normalize.fst"
let _53_1031 = (FStar_List.fold_right (fun lb _53_1020 -> (match (_53_1020) with
| (rec_env, memos, i) -> begin
(
# 635 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _142_441 = (
# 635 "FStar.TypeChecker.Normalize.fst"
let _53_1021 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_1021.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_1021.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _142_441))
in (
# 636 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 637 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 638 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_53_1031) with
| (rec_env, memos, _53_1030) -> begin
(
# 640 "FStar.TypeChecker.Normalize.fst"
let _53_1034 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 641 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _142_448 = (let _142_447 = (let _142_446 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _142_446))
in Clos (_142_447))
in (_142_448)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _53_1046::_53_1044 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_1051) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 653 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _53_1058 -> begin
(norm cfg env stack head)
end)
end
| _53_1060 -> begin
(
# 660 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 661 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _142_449 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_142_449))
end
| _53_1065 -> begin
m
end)
in (
# 665 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_1073 -> (match (_53_1073) with
| (a, imp) -> begin
(let _142_454 = (norm cfg env [] a)
in (_142_454, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 676 "FStar.TypeChecker.Normalize.fst"
let _53_1079 = comp
in (let _142_459 = (let _142_458 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_142_458))
in {FStar_Syntax_Syntax.n = _142_459; FStar_Syntax_Syntax.tk = _53_1079.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1079.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1079.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 679 "FStar.TypeChecker.Normalize.fst"
let _53_1083 = comp
in (let _142_461 = (let _142_460 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_142_460))
in {FStar_Syntax_Syntax.n = _142_461; FStar_Syntax_Syntax.tk = _53_1083.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1083.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1083.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 682 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_1091 -> (match (_53_1091) with
| (a, i) -> begin
(let _142_465 = (norm cfg env [] a)
in (_142_465, i))
end)))))
in (
# 683 "FStar.TypeChecker.Normalize.fst"
let _53_1092 = comp
in (let _142_469 = (let _142_468 = (
# 683 "FStar.TypeChecker.Normalize.fst"
let _53_1094 = ct
in (let _142_467 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _142_466 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_1094.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _142_467; FStar_Syntax_Syntax.effect_args = _142_466; FStar_Syntax_Syntax.flags = _53_1094.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_142_468))
in {FStar_Syntax_Syntax.n = _142_469; FStar_Syntax_Syntax.tk = _53_1092.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_1092.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_1092.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _53_1100 -> (match (_53_1100) with
| (x, imp) -> begin
(let _142_474 = (
# 687 "FStar.TypeChecker.Normalize.fst"
let _53_1101 = x
in (let _142_473 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1101.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1101.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _142_473}))
in (_142_474, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 691 "FStar.TypeChecker.Normalize.fst"
let _53_1114 = (FStar_List.fold_left (fun _53_1108 b -> (match (_53_1108) with
| (nbs', env) -> begin
(
# 692 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_53_1114) with
| (nbs, _53_1113) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 706 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 710 "FStar.TypeChecker.Normalize.fst"
let _53_1131 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 714 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 715 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _142_484 = (
# 716 "FStar.TypeChecker.Normalize.fst"
let _53_1144 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _53_1144.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_1144.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _53_1144.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _142_484))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 722 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 726 "FStar.TypeChecker.Normalize.fst"
let _53_1187 = (log cfg (fun _53_1186 -> (match (()) with
| () -> begin
(let _142_486 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _142_486))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 731 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 732 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 734 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_53_1194, a) -> begin
(
# 738 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 743 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _142_487 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _142_487)))
end
| Match (env, branches, r)::stack -> begin
(
# 747 "FStar.TypeChecker.Normalize.fst"
let _53_1215 = (log cfg (fun _53_1214 -> (match (()) with
| () -> begin
(let _142_489 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _142_489))
end)))
in (
# 748 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _53_1218 -> (match (()) with
| () -> begin
(
# 749 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 750 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 750 "FStar.TypeChecker.Normalize.fst"
let _53_1220 = cfg
in (let _142_492 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _53_1220.steps; tcenv = _53_1220.tcenv; delta_level = _142_492}))
in (
# 751 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 755 "FStar.TypeChecker.Normalize.fst"
let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1228 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 759 "FStar.TypeChecker.Normalize.fst"
let _53_1233 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1233) with
| (p, wopt, e) -> begin
(
# 760 "FStar.TypeChecker.Normalize.fst"
let env = (let _142_500 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _142_500 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 762 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _142_501 = (norm_or_whnf env w)
in Some (_142_501))
end)
in (
# 765 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
end)
in (let _142_502 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _142_502))))))
end))
in (
# 769 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1247) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1272 -> begin
false
end))
in (
# 776 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 780 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 781 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 785 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 789 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 790 "FStar.TypeChecker.Normalize.fst"
let _53_1289 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1289) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 793 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 794 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1295) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1312) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1319 -> begin
(let _142_519 = (not ((is_cons head)))
in FStar_Util.Inr (_142_519))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match ((let _142_520 = (FStar_Syntax_Util.un_uinst head)
in _142_520.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1327 -> begin
(let _142_521 = (not ((is_cons head)))
in FStar_Util.Inr (_142_521))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _53_1337)::rest_a, (p, _53_1343)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1351 -> begin
FStar_Util.Inr (false)
end))
in (
# 827 "FStar.TypeChecker.Normalize.fst"
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
# 838 "FStar.TypeChecker.Normalize.fst"
let _53_1369 = (log cfg (fun _53_1368 -> (match (()) with
| () -> begin
(let _142_532 = (FStar_Syntax_Print.pat_to_string p)
in (let _142_531 = (let _142_530 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _142_530 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _142_532 _142_531)))
end)))
in (
# 843 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_left (fun env t -> (let _142_537 = (let _142_536 = (let _142_535 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _142_535))
in Clos (_142_536))
in (_142_537)::env)) env s)
in (let _142_538 = (guard_when_clause wopt b rest)
in (norm cfg env stack _142_538))))
end)
end))
in (matches t branches)))))))
end))

# 846 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 849 "FStar.TypeChecker.Normalize.fst"
let d = (match ((FStar_Util.find_map s (fun _53_5 -> (match (_53_5) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1380 -> begin
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

# 854 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _142_550 = (config s e)
in (norm _142_550 [] [] t)))

# 856 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _142_557 = (config s e)
in (norm_comp _142_557 [] t)))

# 857 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _142_562 = (config [] env)
in (norm_universe _142_562 [] u)))

# 858 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _142_567 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _142_567)))

# 860 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _142_573 = (let _142_572 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _142_572 [] c))
in (FStar_Syntax_Print.comp_to_string _142_573)))

# 861 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 864 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 865 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 866 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 869 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _142_584 = (let _142_583 = (let _142_582 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _142_582))
in FStar_Syntax_Syntax.Tm_refine (_142_583))
in (mk _142_584 t0.FStar_Syntax_Syntax.pos))
end
| _53_1414 -> begin
t
end))
end
| _53_1416 -> begin
t
end)))
in (aux t))))

# 876 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 879 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _142_589 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _142_589 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 883 "FStar.TypeChecker.Normalize.fst"
let _53_1427 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_1427) with
| (binders, cdef) -> begin
(
# 884 "FStar.TypeChecker.Normalize.fst"
let inst = (let _142_593 = (let _142_592 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_142_592)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_1431 _53_1435 -> (match ((_53_1431, _53_1435)) with
| ((x, _53_1430), (t, _53_1434)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _142_593))
in (
# 885 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 886 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 886 "FStar.TypeChecker.Normalize.fst"
let _53_1438 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_1438.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_1438.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_1438.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 887 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _53_1441 _53_1443 _53_1445 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 889 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _53_1447 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 893 "FStar.TypeChecker.Normalize.fst"
let _53_1454 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_53_1454) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1457 -> begin
(
# 897 "FStar.TypeChecker.Normalize.fst"
let _53_1460 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1460) with
| (binders, args) -> begin
(let _142_608 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _142_607 = (let _142_606 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _142_604 -> FStar_Util.Inl (_142_604)))
in (FStar_All.pipe_right _142_606 (fun _142_605 -> Some (_142_605))))
in (FStar_Syntax_Util.abs binders _142_608 _142_607)))
end))
end)
end))
end
| _53_1462 -> begin
(let _142_611 = (let _142_610 = (FStar_Syntax_Print.tag_of_term t)
in (let _142_609 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _142_610 _142_609)))
in (FStar_All.failwith _142_611))
end))





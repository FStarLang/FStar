
open Prims
# 31 "FStar.TypeChecker.Normalize.fst"
type step =
| WHNF
| Inline
| Unfold
| Beta
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
let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))

# 48 "FStar.TypeChecker.Normalize.fst"
let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))

# 49 "FStar.TypeChecker.Normalize.fst"
let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.TypeChecker.Normalize.fst"
let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Normalize.fst"
let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.TypeChecker.Normalize.fst"
let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.TypeChecker.Normalize.fst"
let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.TypeChecker.Normalize.fst"
let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))

# 56 "FStar.TypeChecker.Normalize.fst"
let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
true
end
| _ -> begin
false
end))

# 57 "FStar.TypeChecker.Normalize.fst"
type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list

# 61 "FStar.TypeChecker.Normalize.fst"
let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.TypeChecker.Normalize.fst"
let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))

# 63 "FStar.TypeChecker.Normalize.fst"
let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.TypeChecker.Normalize.fst"
let ___Clos____0 : closure  ->  (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) = (fun projectee -> (match (projectee) with
| Clos (_66_8) -> begin
_66_8
end))

# 62 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_66_11) -> begin
_66_11
end))

# 64 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _66_1 -> (match (_66_1) with
| Clos (_66_14, t, _66_17) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _66_21 -> begin
"dummy"
end))

# 68 "FStar.TypeChecker.Normalize.fst"
type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}

# 70 "FStar.TypeChecker.Normalize.fst"
let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))

# 74 "FStar.TypeChecker.Normalize.fst"
type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list

# 76 "FStar.TypeChecker.Normalize.fst"
type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

# 78 "FStar.TypeChecker.Normalize.fst"
type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)

# 81 "FStar.TypeChecker.Normalize.fst"
let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.TypeChecker.Normalize.fst"
let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.TypeChecker.Normalize.fst"
let ___Arg____0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_66_28) -> begin
_66_28
end))

# 82 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_66_31) -> begin
_66_31
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_66_34) -> begin
_66_34
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_66_37) -> begin
_66_37
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_66_40) -> begin
_66_40
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___App____0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_66_43) -> begin
_66_43
end))

# 87 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_66_46) -> begin
_66_46
end))

# 87 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 99 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 101 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_66_52) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 105 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _147_159 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _147_159 (FStar_String.concat "; "))))

# 108 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _66_2 -> (match (_66_2) with
| Arg (c, _66_59, _66_61) -> begin
(closure_to_string c)
end
| MemoLazy (_66_65) -> begin
"MemoLazy"
end
| Abs (_66_68, bs, _66_71, _66_73, _66_75) -> begin
(let _147_162 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _147_162))
end
| _66_79 -> begin
"Match"
end))

# 114 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _147_165 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _147_165 (FStar_String.concat "; "))))

# 117 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 122 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _66_3 -> (match (_66_3) with
| [] -> begin
true
end
| _66_86 -> begin
false
end))

# 126 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _66_90 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _66_89 -> (match (_66_89) with
| _66_93 -> begin
(let _147_181 = (let _147_180 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _147_180))
in (FStar_All.failwith _147_181))
end))))

# 130 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 141 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 142 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 147 "FStar.TypeChecker.Normalize.fst"
let _66_114 = (FStar_List.fold_left (fun _66_105 u -> (match (_66_105) with
| (cur_kernel, cur_max, out) -> begin
(
# 149 "FStar.TypeChecker.Normalize.fst"
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
# 160 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 161 "FStar.TypeChecker.Normalize.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _66_121 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| _66_130 -> begin
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
(let _147_196 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _147_196 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _147_198 = (aux u)
in (FStar_List.map (fun _147_197 -> FStar_Syntax_Syntax.U_succ (_147_197)) _147_198))
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

# 188 "FStar.TypeChecker.Normalize.fst"
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _66_162 -> begin
(
# 202 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_165) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _147_225 = (let _147_224 = (let _147_223 = (closure_as_term_delayed cfg env t')
in (u, _147_223))
in FStar_Syntax_Syntax.Tm_uvar (_147_224))
in (mk _147_225 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _147_227 = (let _147_226 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_147_226))
in (mk _147_227 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _147_228 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _147_228))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_190) -> begin
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
(
# 229 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (
# 230 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 234 "FStar.TypeChecker.Normalize.fst"
let _66_211 = (closures_as_binders_delayed cfg env bs)
in (match (_66_211) with
| (bs, env) -> begin
(
# 235 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _147_231 = (let _147_230 = (let _147_229 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _147_229))
in FStar_Syntax_Syntax.Tm_abs (_147_230))
in (mk _147_231 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 239 "FStar.TypeChecker.Normalize.fst"
let _66_219 = (closures_as_binders_delayed cfg env bs)
in (match (_66_219) with
| (bs, env) -> begin
(
# 240 "FStar.TypeChecker.Normalize.fst"
let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 244 "FStar.TypeChecker.Normalize.fst"
let _66_227 = (let _147_233 = (let _147_232 = (FStar_Syntax_Syntax.mk_binder x)
in (_147_232)::[])
in (closures_as_binders_delayed cfg env _147_233))
in (match (_66_227) with
| (x, env) -> begin
(
# 245 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _147_237 = (let _147_236 = (let _147_235 = (let _147_234 = (FStar_List.hd x)
in (FStar_All.pipe_right _147_234 Prims.fst))
in (_147_235, phi))
in FStar_Syntax_Syntax.Tm_refine (_147_236))
in (mk _147_237 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _147_241 = (let _147_240 = (let _147_239 = (closure_as_term_delayed cfg env t1)
in (let _147_238 = (closure_as_term_delayed cfg env t2)
in (_147_239, _147_238, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_147_240))
in (mk _147_241 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _147_244 = (let _147_243 = (let _147_242 = (closure_as_term_delayed cfg env t')
in (_147_242, m))
in FStar_Syntax_Syntax.Tm_meta (_147_243))
in (mk _147_244 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_match (_66_239) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Syntax_Syntax.Tm_let (_66_242) -> begin
(FStar_All.failwith "NYI")
end))
end))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _66_249 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inr ((fun _66_250 -> (match (()) with
| () -> begin
(closure_as_term cfg env t)
end)))) t.FStar_Syntax_Syntax.pos)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] -> begin
args
end
| _66_256 -> begin
(FStar_List.map (fun _66_259 -> (match (_66_259) with
| (x, imp) -> begin
(let _147_255 = (closure_as_term_delayed cfg env x)
in (_147_255, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * closure Prims.list) = (fun cfg env bs -> (
# 269 "FStar.TypeChecker.Normalize.fst"
let _66_275 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _66_265 _66_268 -> (match ((_66_265, _66_268)) with
| ((env, out), (b, imp)) -> begin
(
# 270 "FStar.TypeChecker.Normalize.fst"
let b = (
# 270 "FStar.TypeChecker.Normalize.fst"
let _66_269 = b
in (let _147_261 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_269.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_269.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_261}))
in (
# 271 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_66_275) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] -> begin
c
end
| _66_281 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _147_265 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _147_265))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _147_266 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _147_266))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 283 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 284 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 285 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _66_4 -> (match (_66_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _147_268 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_147_268))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 288 "FStar.TypeChecker.Normalize.fst"
let _66_295 = c
in {FStar_Syntax_Syntax.effect_name = _66_295.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _66_5 -> (match (_66_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _147_275 = (
# 294 "FStar.TypeChecker.Normalize.fst"
let _66_303 = lc
in (let _147_274 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _66_303.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _147_274; FStar_Syntax_Syntax.cflags = _66_303.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _66_305 -> (match (()) with
| () -> begin
(let _147_273 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _147_273))
end))}))
in Some (_147_275))
end))

# 295 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 302 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 302 "FStar.TypeChecker.Normalize.fst"
let _66_310 = t
in {FStar_Syntax_Syntax.n = _66_310.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_310.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_310.FStar_Syntax_Syntax.vars}))
in (
# 303 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _66_316) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _66_321) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _66_325 -> begin
None
end))
in (
# 307 "FStar.TypeChecker.Normalize.fst"
let simplify = (fun arg -> ((simp_t (Prims.fst arg)), arg))
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
| _66_409 -> begin
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
| _66_452 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _66_479)::(_66_470, (arg, _66_473))::[] -> begin
arg
end
| _66_483 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _66_487)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _66_493)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _66_497 -> begin
tm
end)
end else begin
if ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit (_)))::(t, _)::[]) -> begin
(match ((let _147_286 = (FStar_Syntax_Subst.compress t)
in _147_286.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_515::[], body, _66_519) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _66_527 -> begin
tm
end)
end
| _66_529 -> begin
tm
end)
end
| _66_531 -> begin
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
| _66_533 -> begin
tm
end)
end))))

# 353 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 362 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 363 "FStar.TypeChecker.Normalize.fst"
let _66_540 = (log cfg (fun _66_539 -> (match (()) with
| () -> begin
(let _147_313 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_312 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _147_313 _147_312)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_66_543) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 376 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _147_317 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_317)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 382 "FStar.TypeChecker.Normalize.fst"
let us = (let _147_319 = (let _147_318 = (FStar_List.map (norm_universe cfg env) us)
in (_147_318, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_147_319))
in (
# 383 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f, _66_579) -> begin
if (cfg.delta_level = FStar_TypeChecker_Env.NoDelta) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(
# 395 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _66_591)::stack -> begin
(
# 399 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _66_599 -> begin
(let _147_323 = (let _147_322 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _147_322))
in (FStar_All.failwith _147_323))
end)
end else begin
(norm cfg env stack t)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_66_603) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 412 "FStar.TypeChecker.Normalize.fst"
let _66_616 = (log cfg (fun _66_615 -> (match (()) with
| () -> begin
(let _147_326 = (FStar_Syntax_Print.term_to_string t)
in (let _147_325 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _147_326 _147_325)))
end)))
in (match ((let _147_327 = (FStar_Syntax_Subst.compress t')
in _147_327.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_66_619) -> begin
(norm cfg env stack t')
end
| _66_622 -> begin
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
| Meta (_66_632)::_66_630 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_66_638)::_66_636 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_66_644)::_66_642 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _66_650, _66_652)::stack -> begin
(match (c) with
| Univ (_66_657) -> begin
(norm cfg ((c)::env) stack t)
end
| _66_660 -> begin
(
# 440 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _66_663::[] -> begin
body
end
| _66_667::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 444 "FStar.TypeChecker.Normalize.fst"
let _66_671 = (log cfg (fun _66_670 -> (match (()) with
| () -> begin
(let _147_329 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _147_329))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 449 "FStar.TypeChecker.Normalize.fst"
let _66_677 = (set_memo r (env, t))
in (
# 450 "FStar.TypeChecker.Normalize.fst"
let _66_680 = (log cfg (fun _66_679 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_331 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_331))
end else begin
(
# 458 "FStar.TypeChecker.Normalize.fst"
let _66_697 = (FStar_Syntax_Subst.open_term bs body)
in (match (_66_697) with
| (bs, body) -> begin
(
# 459 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_699 -> (Dummy)::env) env))
in (
# 460 "FStar.TypeChecker.Normalize.fst"
let _66_703 = (log cfg (fun _66_702 -> (match (()) with
| () -> begin
(let _147_335 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _147_335))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 465 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _66_711 stack -> (match (_66_711) with
| (a, aq) -> begin
(let _147_342 = (let _147_341 = (let _147_340 = (let _147_339 = (let _147_338 = (FStar_Util.mk_ref None)
in (env, a, _147_338))
in Clos (_147_339))
in (_147_340, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_147_341))
in (_147_342)::stack)
end)) args))
in (
# 466 "FStar.TypeChecker.Normalize.fst"
let _66_715 = (log cfg (fun _66_714 -> (match (()) with
| () -> begin
(let _147_344 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _147_344))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_345 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_345))
end else begin
(
# 472 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 473 "FStar.TypeChecker.Normalize.fst"
let _66_724 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_66_724) with
| (closing, f) -> begin
(
# 474 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 475 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_348 = (let _147_347 = (let _147_346 = (FStar_Syntax_Subst.close closing f)
in ((
# 475 "FStar.TypeChecker.Normalize.fst"
let _66_726 = x
in {FStar_Syntax_Syntax.ppname = _66_726.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_726.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _147_346))
in FStar_Syntax_Syntax.Tm_refine (_147_347))
in (mk _147_348 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _147_349 = (closure_as_term cfg env t)
in (rebuild cfg env stack _147_349))
end else begin
(
# 481 "FStar.TypeChecker.Normalize.fst"
let _66_735 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_66_735) with
| (bs, c) -> begin
(
# 482 "FStar.TypeChecker.Normalize.fst"
let c = (let _147_352 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _66_737 -> (Dummy)::env) env))
in (norm_comp cfg _147_352 c))
in (
# 483 "FStar.TypeChecker.Normalize.fst"
let t = (let _147_353 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _147_353 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _66_765 -> begin
(
# 492 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 493 "FStar.TypeChecker.Normalize.fst"
let _66_768 = (log cfg (fun _66_767 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 494 "FStar.TypeChecker.Normalize.fst"
let t2 = (norm cfg env [] t2)
in (let _147_355 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _147_355)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 501 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 505 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_358 = (let _147_357 = (let _147_356 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _147_356))
in Clos (_147_357))
in (_147_358)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_66_785, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_66_797); FStar_Syntax_Syntax.lbunivs = _66_795; FStar_Syntax_Syntax.lbtyp = _66_793; FStar_Syntax_Syntax.lbeff = _66_791; FStar_Syntax_Syntax.lbdef = _66_789}::_66_787), _66_803) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 522 "FStar.TypeChecker.Normalize.fst"
let _66_825 = (FStar_List.fold_right (fun lb _66_814 -> (match (_66_814) with
| (rec_env, memos, i) -> begin
(
# 523 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _147_361 = (
# 523 "FStar.TypeChecker.Normalize.fst"
let _66_815 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _66_815.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _66_815.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _147_361))
in (
# 524 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 525 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 526 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_66_825) with
| (rec_env, memos, _66_824) -> begin
(
# 528 "FStar.TypeChecker.Normalize.fst"
let _66_828 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 529 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _147_368 = (let _147_367 = (let _147_366 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _147_366))
in Clos (_147_367))
in (_147_368)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _66_840::_66_838 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _66_845) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 541 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _66_852 -> begin
(norm cfg env stack head)
end)
end
| _66_854 -> begin
(
# 548 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 549 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _147_369 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_147_369))
end
| _66_859 -> begin
m
end)
in (
# 553 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _66_867 -> (match (_66_867) with
| (a, imp) -> begin
(let _147_374 = (norm cfg env [] a)
in (_147_374, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 564 "FStar.TypeChecker.Normalize.fst"
let _66_873 = comp
in (let _147_379 = (let _147_378 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_147_378))
in {FStar_Syntax_Syntax.n = _147_379; FStar_Syntax_Syntax.tk = _66_873.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_873.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_873.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 567 "FStar.TypeChecker.Normalize.fst"
let _66_877 = comp
in (let _147_381 = (let _147_380 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_147_380))
in {FStar_Syntax_Syntax.n = _147_381; FStar_Syntax_Syntax.tk = _66_877.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_877.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_877.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 570 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _66_885 -> (match (_66_885) with
| (a, i) -> begin
(let _147_385 = (norm cfg env [] a)
in (_147_385, i))
end)))))
in (
# 571 "FStar.TypeChecker.Normalize.fst"
let _66_886 = comp
in (let _147_389 = (let _147_388 = (
# 571 "FStar.TypeChecker.Normalize.fst"
let _66_888 = ct
in (let _147_387 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _147_386 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _66_888.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _147_387; FStar_Syntax_Syntax.effect_args = _147_386; FStar_Syntax_Syntax.flags = _66_888.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_147_388))
in {FStar_Syntax_Syntax.n = _147_389; FStar_Syntax_Syntax.tk = _66_886.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _66_886.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _66_886.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _66_894 -> (match (_66_894) with
| (x, imp) -> begin
(let _147_394 = (
# 575 "FStar.TypeChecker.Normalize.fst"
let _66_895 = x
in (let _147_393 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _66_895.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_895.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _147_393}))
in (_147_394, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 579 "FStar.TypeChecker.Normalize.fst"
let _66_908 = (FStar_List.fold_left (fun _66_902 b -> (match (_66_902) with
| (nbs', env) -> begin
(
# 580 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_66_908) with
| (nbs, _66_907) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 594 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 598 "FStar.TypeChecker.Normalize.fst"
let _66_925 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 602 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 603 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _147_404 = (
# 604 "FStar.TypeChecker.Normalize.fst"
let _66_938 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _66_938.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_938.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _66_938.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _147_404))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 610 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 614 "FStar.TypeChecker.Normalize.fst"
let _66_981 = (log cfg (fun _66_980 -> (match (()) with
| () -> begin
(let _147_406 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _147_406))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 619 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 620 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 622 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_66_988, a) -> begin
(
# 626 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 631 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _147_407 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _147_407)))
end
| Match (env, branches, r)::stack -> begin
(
# 635 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _66_1009 -> (match (()) with
| () -> begin
(
# 636 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 637 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 637 "FStar.TypeChecker.Normalize.fst"
let _66_1011 = cfg
in (let _147_410 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _66_1011.steps; tcenv = _66_1011.tcenv; delta_level = _147_410}))
in (
# 638 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 642 "FStar.TypeChecker.Normalize.fst"
let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 644 "FStar.TypeChecker.Normalize.fst"
let _66_1021 = (FStar_Syntax_Subst.open_branch branch)
in (match (_66_1021) with
| (p, wopt, e) -> begin
(
# 645 "FStar.TypeChecker.Normalize.fst"
let env = (let _147_418 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _147_418 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 647 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _147_419 = (norm_or_whnf env w)
in Some (_147_419))
end)
in (
# 650 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _147_420 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _147_420))))))
end))
in (
# 654 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _66_1035) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
true
end
| _66_1056 -> begin
false
end))
in (
# 661 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 665 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 666 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 670 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 674 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 675 "FStar.TypeChecker.Normalize.fst"
let _66_1073 = (FStar_Syntax_Util.head_and_args t)
in (match (_66_1073) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 678 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 679 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_66_1079) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_66_1096) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _66_1103 -> begin
(let _147_437 = (not ((is_cons head)))
in FStar_Util.Inr (_147_437))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _66_1111 -> begin
(let _147_438 = (not ((is_cons head)))
in FStar_Util.Inr (_147_438))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _66_1121)::rest_a, (p, _66_1127)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _66_1135 -> begin
FStar_Util.Inr (false)
end))
in (
# 712 "FStar.TypeChecker.Normalize.fst"
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
# 725 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_right (fun t env -> (let _147_450 = (let _147_449 = (let _147_448 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _147_448))
in Clos (_147_449))
in (_147_450)::env)) s env)
in (let _147_451 = (guard_when_clause wopt b rest)
in (norm cfg env stack _147_451)))
end)
end))
in (matches t branches))))))
end))

# 728 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 731 "FStar.TypeChecker.Normalize.fst"
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

# 736 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (norm (config s e) [] [] t))

# 738 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (norm_comp (config s e) [] t))

# 739 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (norm_universe (config [] env) [] u))

# 740 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _147_476 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _147_476)))

# 742 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _147_481 = (norm_comp (config ((AllowUnboundUniverses)::[]) env) [] c)
in (FStar_Syntax_Print.comp_to_string _147_481)))

# 743 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 746 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (
# 747 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 748 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 751 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _147_492 = (let _147_491 = (let _147_490 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _147_490))
in FStar_Syntax_Syntax.Tm_refine (_147_491))
in (mk _147_492 t0.FStar_Syntax_Syntax.pos))
end
| _66_1187 -> begin
t
end))
end
| _66_1189 -> begin
t
end)))
in (aux t))))

# 758 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 761 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _147_497 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _147_497 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 765 "FStar.TypeChecker.Normalize.fst"
let _66_1200 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_66_1200) with
| (binders, cdef) -> begin
(
# 766 "FStar.TypeChecker.Normalize.fst"
let inst = (let _147_501 = (let _147_500 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_147_500)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _66_1204 _66_1208 -> (match ((_66_1204, _66_1208)) with
| ((x, _66_1203), (t, _66_1207)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _147_501))
in (
# 767 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 768 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 768 "FStar.TypeChecker.Normalize.fst"
let _66_1211 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _66_1211.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _66_1211.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _66_1211.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 769 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _66_1214 _66_1216 _66_1218 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 771 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _66_1220 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 775 "FStar.TypeChecker.Normalize.fst"
let _66_1227 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_66_1227) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _66_1230 -> begin
(
# 779 "FStar.TypeChecker.Normalize.fst"
let _66_1233 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_66_1233) with
| (binders, args) -> begin
(let _147_514 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _147_513 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _147_512 -> Some (_147_512)))
in (FStar_Syntax_Util.abs binders _147_514 _147_513)))
end))
end)
end))
end
| _66_1235 -> begin
(let _147_517 = (let _147_516 = (FStar_Syntax_Print.tag_of_term t)
in (let _147_515 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _147_516 _147_515)))
in (FStar_All.failwith _147_517))
end))





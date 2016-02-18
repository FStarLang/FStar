
open Prims
# 42 "FStar.TypeChecker.Normalize.fst"
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

# 50 "FStar.TypeChecker.Normalize.fst"
let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))

# 51 "FStar.TypeChecker.Normalize.fst"
let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))

# 52 "FStar.TypeChecker.Normalize.fst"
let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))

# 53 "FStar.TypeChecker.Normalize.fst"
let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 54 "FStar.TypeChecker.Normalize.fst"
let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))

# 55 "FStar.TypeChecker.Normalize.fst"
let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
true
end
| _ -> begin
false
end))

# 59 "FStar.TypeChecker.Normalize.fst"
type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo)
| Univ of FStar_Syntax_Syntax.universe
| Dummy 
 and env =
closure Prims.list

# 60 "FStar.TypeChecker.Normalize.fst"
let is_Clos = (fun _discr_ -> (match (_discr_) with
| Clos (_) -> begin
true
end
| _ -> begin
false
end))

# 61 "FStar.TypeChecker.Normalize.fst"
let is_Univ = (fun _discr_ -> (match (_discr_) with
| Univ (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.TypeChecker.Normalize.fst"
let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))

# 60 "FStar.TypeChecker.Normalize.fst"
let ___Clos____0 : closure  ->  (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) = (fun projectee -> (match (projectee) with
| Clos (_67_8) -> begin
_67_8
end))

# 61 "FStar.TypeChecker.Normalize.fst"
let ___Univ____0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_67_11) -> begin
_67_11
end))

# 65 "FStar.TypeChecker.Normalize.fst"
let closure_to_string : closure  ->  Prims.string = (fun _67_1 -> (match (_67_1) with
| Clos (_67_14, t, _67_17) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _67_21 -> begin
"dummy"
end))

# 69 "FStar.TypeChecker.Normalize.fst"
type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level}

# 69 "FStar.TypeChecker.Normalize.fst"
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
| Abs of (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)

# 80 "FStar.TypeChecker.Normalize.fst"
let is_Arg = (fun _discr_ -> (match (_discr_) with
| Arg (_) -> begin
true
end
| _ -> begin
false
end))

# 81 "FStar.TypeChecker.Normalize.fst"
let is_UnivArgs = (fun _discr_ -> (match (_discr_) with
| UnivArgs (_) -> begin
true
end
| _ -> begin
false
end))

# 82 "FStar.TypeChecker.Normalize.fst"
let is_MemoLazy = (fun _discr_ -> (match (_discr_) with
| MemoLazy (_) -> begin
true
end
| _ -> begin
false
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let is_Match = (fun _discr_ -> (match (_discr_) with
| Match (_) -> begin
true
end
| _ -> begin
false
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let is_Abs = (fun _discr_ -> (match (_discr_) with
| Abs (_) -> begin
true
end
| _ -> begin
false
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let is_App = (fun _discr_ -> (match (_discr_) with
| App (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))

# 80 "FStar.TypeChecker.Normalize.fst"
let ___Arg____0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_67_28) -> begin
_67_28
end))

# 81 "FStar.TypeChecker.Normalize.fst"
let ___UnivArgs____0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_67_31) -> begin
_67_31
end))

# 82 "FStar.TypeChecker.Normalize.fst"
let ___MemoLazy____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_67_34) -> begin
_67_34
end))

# 83 "FStar.TypeChecker.Normalize.fst"
let ___Match____0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_67_37) -> begin
_67_37
end))

# 84 "FStar.TypeChecker.Normalize.fst"
let ___Abs____0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * FStar_Syntax_Syntax.lcomp Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_67_40) -> begin
_67_40
end))

# 85 "FStar.TypeChecker.Normalize.fst"
let ___App____0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_67_43) -> begin
_67_43
end))

# 86 "FStar.TypeChecker.Normalize.fst"
let ___Meta____0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_67_46) -> begin
_67_46
end))

# 88 "FStar.TypeChecker.Normalize.fst"
type stack =
stack_elt Prims.list

# 100 "FStar.TypeChecker.Normalize.fst"
let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))

# 101 "FStar.TypeChecker.Normalize.fst"
let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_67_52) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))

# 106 "FStar.TypeChecker.Normalize.fst"
let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _146_158 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _146_158 (FStar_String.concat "; "))))

# 109 "FStar.TypeChecker.Normalize.fst"
let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _67_2 -> (match (_67_2) with
| Arg (c, _67_59, _67_61) -> begin
(closure_to_string c)
end
| MemoLazy (_67_65) -> begin
"MemoLazy"
end
| Abs (_67_68, bs, _67_71, _67_73, _67_75) -> begin
(let _146_161 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _146_161))
end
| _67_79 -> begin
"Match"
end))

# 115 "FStar.TypeChecker.Normalize.fst"
let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _146_164 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _146_164 (FStar_String.concat "; "))))

# 118 "FStar.TypeChecker.Normalize.fst"
let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)

# 123 "FStar.TypeChecker.Normalize.fst"
let is_empty = (fun _67_3 -> (match (_67_3) with
| [] -> begin
true
end
| _67_86 -> begin
false
end))

# 127 "FStar.TypeChecker.Normalize.fst"
let lookup_bvar = (fun env x -> (FStar_All.try_with (fun _67_90 -> (match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)) (fun _67_89 -> (match (_67_89) with
| _67_93 -> begin
(let _146_180 = (let _146_179 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _146_179))
in (FStar_All.failwith _146_180))
end))))

# 139 "FStar.TypeChecker.Normalize.fst"
let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (
# 140 "FStar.TypeChecker.Normalize.fst"
let norm_univs = (fun us -> (
# 141 "FStar.TypeChecker.Normalize.fst"
let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (
# 146 "FStar.TypeChecker.Normalize.fst"
let _67_114 = (FStar_List.fold_left (fun _67_105 u -> (match (_67_105) with
| (cur_kernel, cur_max, out) -> begin
(
# 148 "FStar.TypeChecker.Normalize.fst"
let _67_109 = (FStar_Syntax_Util.univ_kernel u)
in (match (_67_109) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
(cur_kernel, u, out)
end else begin
(k_u, u, (cur_max)::out)
end
end))
end)) (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, []) us)
in (match (_67_114) with
| (_67_111, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (
# 159 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun u -> (
# 160 "FStar.TypeChecker.Normalize.fst"
let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(FStar_All.try_with (fun _67_121 -> (match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(u)::[]
end
| _67_130 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)) (fun _67_120 -> (match (_67_120) with
| _67_124 -> begin
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
(let _146_195 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _146_195 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _146_197 = (aux u)
in (FStar_List.map (fun _146_196 -> FStar_Syntax_Syntax.U_succ (_146_196)) _146_197))
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

# 195 "FStar.TypeChecker.Normalize.fst"
let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _67_162 -> begin
(
# 199 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_67_165) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (u, t') -> begin
(let _146_224 = (let _146_223 = (let _146_222 = (closure_as_term_delayed cfg env t')
in (u, _146_222))
in FStar_Syntax_Syntax.Tm_uvar (_146_223))
in (mk _146_224 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _146_226 = (let _146_225 = (norm_universe cfg env u)
in FStar_Syntax_Syntax.Tm_type (_146_225))
in (mk _146_226 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _146_227 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _146_227))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_67_190) -> begin
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
# 226 "FStar.TypeChecker.Normalize.fst"
let head = (closure_as_term_delayed cfg env head)
in (
# 227 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 231 "FStar.TypeChecker.Normalize.fst"
let _67_211 = (closures_as_binders_delayed cfg env bs)
in (match (_67_211) with
| (bs, env) -> begin
(
# 232 "FStar.TypeChecker.Normalize.fst"
let body = (closure_as_term_delayed cfg env body)
in (let _146_230 = (let _146_229 = (let _146_228 = (close_lcomp_opt cfg env lopt)
in ((FStar_List.rev bs), body, _146_228))
in FStar_Syntax_Syntax.Tm_abs (_146_229))
in (mk _146_230 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 236 "FStar.TypeChecker.Normalize.fst"
let _67_219 = (closures_as_binders_delayed cfg env bs)
in (match (_67_219) with
| (bs, env) -> begin
(
# 237 "FStar.TypeChecker.Normalize.fst"
let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 241 "FStar.TypeChecker.Normalize.fst"
let _67_227 = (let _146_232 = (let _146_231 = (FStar_Syntax_Syntax.mk_binder x)
in (_146_231)::[])
in (closures_as_binders_delayed cfg env _146_232))
in (match (_67_227) with
| (x, env) -> begin
(
# 242 "FStar.TypeChecker.Normalize.fst"
let phi = (closure_as_term_delayed cfg env phi)
in (let _146_236 = (let _146_235 = (let _146_234 = (let _146_233 = (FStar_List.hd x)
in (FStar_All.pipe_right _146_233 Prims.fst))
in (_146_234, phi))
in FStar_Syntax_Syntax.Tm_refine (_146_235))
in (mk _146_236 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, lopt) -> begin
(let _146_240 = (let _146_239 = (let _146_238 = (closure_as_term_delayed cfg env t1)
in (let _146_237 = (closure_as_term_delayed cfg env t2)
in (_146_238, _146_237, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_146_239))
in (mk _146_240 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _146_243 = (let _146_242 = (let _146_241 = (closure_as_term_delayed cfg env t')
in (_146_241, m))
in FStar_Syntax_Syntax.Tm_meta (_146_242))
in (mk _146_243 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_match (_67_239) -> begin
(FStar_All.failwith "NYI")
end
| FStar_Syntax_Syntax.Tm_let (_67_242) -> begin
(FStar_All.failwith "NYI")
end))
end))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> (match (env) with
| [] -> begin
t
end
| _67_249 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inr ((fun _67_250 -> (match (()) with
| () -> begin
(closure_as_term cfg env t)
end)))) t.FStar_Syntax_Syntax.pos)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args = (fun cfg env args -> (match (env) with
| [] -> begin
args
end
| _67_256 -> begin
(FStar_List.map (fun _67_259 -> (match (_67_259) with
| (x, imp) -> begin
(let _146_254 = (closure_as_term_delayed cfg env x)
in (_146_254, imp))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.binders  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list * closure Prims.list) = (fun cfg env bs -> (
# 265 "FStar.TypeChecker.Normalize.fst"
let _67_275 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _67_265 _67_268 -> (match ((_67_265, _67_268)) with
| ((env, out), (b, imp)) -> begin
(
# 266 "FStar.TypeChecker.Normalize.fst"
let b = (
# 266 "FStar.TypeChecker.Normalize.fst"
let _67_269 = b
in (let _146_260 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _67_269.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_269.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_260}))
in (
# 267 "FStar.TypeChecker.Normalize.fst"
let env = (Dummy)::env
in (env, ((b, imp))::out)))
end)) (env, [])))
in (match (_67_275) with
| (env, bs) -> begin
((FStar_List.rev bs), env)
end)))
and close_comp : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env c -> (match (env) with
| [] -> begin
c
end
| _67_281 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _146_264 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_Total _146_264))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _146_265 = (closure_as_term_delayed cfg env t)
in (FStar_Syntax_Syntax.mk_GTotal _146_265))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(
# 279 "FStar.TypeChecker.Normalize.fst"
let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (
# 280 "FStar.TypeChecker.Normalize.fst"
let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (
# 281 "FStar.TypeChecker.Normalize.fst"
let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun _67_4 -> (match (_67_4) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
(let _146_267 = (closure_as_term_delayed cfg env t)
in FStar_Syntax_Syntax.DECREASES (_146_267))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (
# 284 "FStar.TypeChecker.Normalize.fst"
let _67_295 = c
in {FStar_Syntax_Syntax.effect_name = _67_295.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags})))))
end)
end))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun cfg env _67_5 -> (match (_67_5) with
| None -> begin
None
end
| Some (lc) -> begin
(let _146_274 = (
# 290 "FStar.TypeChecker.Normalize.fst"
let _67_303 = lc
in (let _146_273 = (closure_as_term_delayed cfg env lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _67_303.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _146_273; FStar_Syntax_Syntax.cflags = _67_303.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _67_305 -> (match (()) with
| () -> begin
(let _146_272 = (lc.FStar_Syntax_Syntax.comp ())
in (close_comp cfg env _146_272))
end))}))
in Some (_146_274))
end))

# 297 "FStar.TypeChecker.Normalize.fst"
let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (
# 298 "FStar.TypeChecker.Normalize.fst"
let w = (fun t -> (
# 298 "FStar.TypeChecker.Normalize.fst"
let _67_310 = t
in {FStar_Syntax_Syntax.n = _67_310.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_310.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _67_310.FStar_Syntax_Syntax.vars}))
in (
# 299 "FStar.TypeChecker.Normalize.fst"
let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _67_316) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv, _67_321) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _67_325 -> begin
None
end))
in (
# 303 "FStar.TypeChecker.Normalize.fst"
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
| _67_409 -> begin
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
| _67_452 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (_::(Some (true), _)::[]) | ((Some (false), _)::_::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (Some (true), _67_479)::(_67_470, (arg, _67_473))::[] -> begin
arg
end
| _67_483 -> begin
tm
end)
end else begin
if (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (Some (true), _67_487)::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| (Some (false), _67_493)::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _67_497 -> begin
tm
end)
end else begin
if ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.forall_lid) || (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| ((t, _)::[]) | ((_, Some (FStar_Syntax_Syntax.Implicit))::(t, _)::[]) -> begin
(match ((let _146_285 = (FStar_Syntax_Subst.compress t)
in _146_285.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_67_513::[], body, _67_517) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _67_525 -> begin
tm
end)
end
| _67_527 -> begin
tm
end)
end
| _67_529 -> begin
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
| _67_531 -> begin
tm
end)
end))))

# 356 "FStar.TypeChecker.Normalize.fst"
let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (
# 358 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 359 "FStar.TypeChecker.Normalize.fst"
let _67_538 = (log cfg (fun _67_537 -> (match (()) with
| () -> begin
(let _146_312 = (FStar_Syntax_Print.tag_of_term t)
in (let _146_311 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s\nNorm %s\n" _146_312 _146_311)))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_67_541) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(
# 372 "FStar.TypeChecker.Normalize.fst"
let u = (norm_universe cfg env u)
in (let _146_316 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _146_316)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(
# 378 "FStar.TypeChecker.Normalize.fst"
let us = (let _146_318 = (let _146_317 = (FStar_List.map (norm_universe cfg env) us)
in (_146_317, t.FStar_Syntax_Syntax.pos))
in UnivArgs (_146_318))
in (
# 379 "FStar.TypeChecker.Normalize.fst"
let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_fvar (f, _67_577) -> begin
if (cfg.delta_level = FStar_TypeChecker_Env.NoDelta) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(
# 391 "FStar.TypeChecker.Normalize.fst"
let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| UnivArgs (us', _67_589)::stack -> begin
(
# 395 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _67_597 -> begin
(let _146_322 = (let _146_321 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _146_321))
in (FStar_All.failwith _146_322))
end)
end else begin
(norm cfg env stack t)
end)
end)
end
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_67_601) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Clos (env, t0, r) -> begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(
# 408 "FStar.TypeChecker.Normalize.fst"
let _67_614 = (log cfg (fun _67_613 -> (match (()) with
| () -> begin
(let _146_325 = (FStar_Syntax_Print.term_to_string t)
in (let _146_324 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _146_325 _146_324)))
end)))
in (match ((let _146_326 = (FStar_Syntax_Subst.compress t')
in _146_326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_67_617) -> begin
(norm cfg env stack t')
end
| _67_620 -> begin
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
| Meta (_67_630)::_67_628 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| UnivArgs (_67_636)::_67_634 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| Match (_67_642)::_67_640 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| Arg (c, _67_648, _67_650)::stack -> begin
(match (c) with
| Univ (_67_655) -> begin
(norm cfg ((c)::env) stack t)
end
| _67_658 -> begin
(
# 436 "FStar.TypeChecker.Normalize.fst"
let body = (match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| _67_661::[] -> begin
body
end
| _67_665::tl -> begin
(mk (FStar_Syntax_Syntax.Tm_abs ((tl, body, None))) t.FStar_Syntax_Syntax.pos)
end)
in (
# 440 "FStar.TypeChecker.Normalize.fst"
let _67_669 = (log cfg (fun _67_668 -> (match (()) with
| () -> begin
(let _146_328 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _146_328))
end)))
in (norm cfg ((c)::env) stack body)))
end)
end
| MemoLazy (r)::stack -> begin
(
# 445 "FStar.TypeChecker.Normalize.fst"
let _67_675 = (set_memo r (env, t))
in (
# 446 "FStar.TypeChecker.Normalize.fst"
let _67_678 = (log cfg (fun _67_677 -> (match (()) with
| () -> begin
(FStar_Util.print_string "\tSet memo\n")
end)))
in (norm cfg env stack t)))
end
| (App (_)::_) | (Abs (_)::_) | ([]) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _146_330 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_330))
end else begin
(
# 454 "FStar.TypeChecker.Normalize.fst"
let _67_695 = (FStar_Syntax_Subst.open_term bs body)
in (match (_67_695) with
| (bs, body) -> begin
(
# 455 "FStar.TypeChecker.Normalize.fst"
let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _67_697 -> (Dummy)::env) env))
in (
# 456 "FStar.TypeChecker.Normalize.fst"
let _67_701 = (log cfg (fun _67_700 -> (match (()) with
| () -> begin
(let _146_334 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _146_334))
end)))
in (norm cfg env' ((Abs ((env, bs, env', lopt, t.FStar_Syntax_Syntax.pos)))::stack) body)))
end))
end
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 461 "FStar.TypeChecker.Normalize.fst"
let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _67_709 stack -> (match (_67_709) with
| (a, aq) -> begin
(let _146_341 = (let _146_340 = (let _146_339 = (let _146_338 = (let _146_337 = (FStar_Util.mk_ref None)
in (env, a, _146_337))
in Clos (_146_338))
in (_146_339, aq, t.FStar_Syntax_Syntax.pos))
in Arg (_146_340))
in (_146_341)::stack)
end)) args))
in (
# 462 "FStar.TypeChecker.Normalize.fst"
let _67_713 = (log cfg (fun _67_712 -> (match (()) with
| () -> begin
(let _146_343 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _146_343))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _146_344 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_344))
end else begin
(
# 468 "FStar.TypeChecker.Normalize.fst"
let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (
# 469 "FStar.TypeChecker.Normalize.fst"
let _67_722 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_67_722) with
| (closing, f) -> begin
(
# 470 "FStar.TypeChecker.Normalize.fst"
let f = (norm cfg ((Dummy)::env) [] f)
in (
# 471 "FStar.TypeChecker.Normalize.fst"
let t = (let _146_347 = (let _146_346 = (let _146_345 = (FStar_Syntax_Subst.close closing f)
in ((
# 471 "FStar.TypeChecker.Normalize.fst"
let _67_724 = x
in {FStar_Syntax_Syntax.ppname = _67_724.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_724.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x}), _146_345))
in FStar_Syntax_Syntax.Tm_refine (_146_346))
in (mk _146_347 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(let _146_348 = (closure_as_term cfg env t)
in (rebuild cfg env stack _146_348))
end else begin
(
# 477 "FStar.TypeChecker.Normalize.fst"
let _67_733 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_67_733) with
| (bs, c) -> begin
(
# 478 "FStar.TypeChecker.Normalize.fst"
let c = (let _146_351 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env _67_735 -> (Dummy)::env) env))
in (norm_comp cfg _146_351 c))
in (
# 479 "FStar.TypeChecker.Normalize.fst"
let t = (let _146_352 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _146_352 c))
in (rebuild cfg env stack t)))
end))
end
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, t2, l) -> begin
(match (stack) with
| (Match (_)::_) | (Arg (_)::_) | (MemoLazy (_)::_) -> begin
(norm cfg env stack t1)
end
| _67_763 -> begin
(
# 488 "FStar.TypeChecker.Normalize.fst"
let t1 = (norm cfg env [] t1)
in (
# 489 "FStar.TypeChecker.Normalize.fst"
let _67_766 = (log cfg (fun _67_765 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (
# 490 "FStar.TypeChecker.Normalize.fst"
let t2 = (norm cfg env [] t2)
in (let _146_354 = (mk (FStar_Syntax_Syntax.Tm_ascribed ((t1, t2, l))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _146_354)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(
# 497 "FStar.TypeChecker.Normalize.fst"
let stack = (Match ((env, branches, t.FStar_Syntax_Syntax.pos)))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((false, lb::[]), body) -> begin
(
# 501 "FStar.TypeChecker.Normalize.fst"
let env = (let _146_357 = (let _146_356 = (let _146_355 = (FStar_Util.mk_ref None)
in (env, lb.FStar_Syntax_Syntax.lbdef, _146_355))
in Clos (_146_356))
in (_146_357)::env)
in (norm cfg env stack body))
end
| FStar_Syntax_Syntax.Tm_let ((_67_783, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_67_795); FStar_Syntax_Syntax.lbunivs = _67_793; FStar_Syntax_Syntax.lbtyp = _67_791; FStar_Syntax_Syntax.lbeff = _67_789; FStar_Syntax_Syntax.lbdef = _67_787}::_67_785), _67_801) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(
# 518 "FStar.TypeChecker.Normalize.fst"
let _67_823 = (FStar_List.fold_right (fun lb _67_812 -> (match (_67_812) with
| (rec_env, memos, i) -> begin
(
# 519 "FStar.TypeChecker.Normalize.fst"
let f_i = (let _146_360 = (
# 519 "FStar.TypeChecker.Normalize.fst"
let _67_813 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _67_813.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _67_813.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _146_360))
in (
# 520 "FStar.TypeChecker.Normalize.fst"
let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let ((lbs, f_i))) t.FStar_Syntax_Syntax.pos)
in (
# 521 "FStar.TypeChecker.Normalize.fst"
let memo = (FStar_Util.mk_ref None)
in (
# 522 "FStar.TypeChecker.Normalize.fst"
let rec_env = (Clos ((env, fix_f_i, memo)))::rec_env
in (rec_env, (memo)::memos, (i + 1))))))
end)) (Prims.snd lbs) (env, [], 0))
in (match (_67_823) with
| (rec_env, memos, _67_822) -> begin
(
# 524 "FStar.TypeChecker.Normalize.fst"
let _67_826 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some ((rec_env, lb.FStar_Syntax_Syntax.lbdef))))) (Prims.snd lbs) memos)
in (
# 525 "FStar.TypeChecker.Normalize.fst"
let body_env = (FStar_List.fold_right (fun lb env -> (let _146_367 = (let _146_366 = (let _146_365 = (FStar_Util.mk_ref None)
in (rec_env, lb.FStar_Syntax_Syntax.lbdef, _146_365))
in Clos (_146_366))
in (_146_367)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| _67_838::_67_836 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _67_843) -> begin
(norm cfg env ((Meta ((m, r)))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(
# 537 "FStar.TypeChecker.Normalize.fst"
let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta ((FStar_Syntax_Syntax.Meta_pattern (args), t.FStar_Syntax_Syntax.pos)))::stack) head))
end
| _67_850 -> begin
(norm cfg env stack head)
end)
end
| _67_852 -> begin
(
# 544 "FStar.TypeChecker.Normalize.fst"
let head = (norm cfg env [] head)
in (
# 545 "FStar.TypeChecker.Normalize.fst"
let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _146_368 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_146_368))
end
| _67_857 -> begin
m
end)
in (
# 549 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((head, m))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end))))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _67_865 -> (match (_67_865) with
| (a, imp) -> begin
(let _146_373 = (norm cfg env [] a)
in (_146_373, imp))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(
# 560 "FStar.TypeChecker.Normalize.fst"
let _67_871 = comp
in (let _146_378 = (let _146_377 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_146_377))
in {FStar_Syntax_Syntax.n = _146_378; FStar_Syntax_Syntax.tk = _67_871.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _67_871.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _67_871.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(
# 563 "FStar.TypeChecker.Normalize.fst"
let _67_875 = comp
in (let _146_380 = (let _146_379 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_146_379))
in {FStar_Syntax_Syntax.n = _146_380; FStar_Syntax_Syntax.tk = _67_875.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _67_875.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _67_875.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(
# 566 "FStar.TypeChecker.Normalize.fst"
let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _67_883 -> (match (_67_883) with
| (a, i) -> begin
(let _146_384 = (norm cfg env [] a)
in (_146_384, i))
end)))))
in (
# 567 "FStar.TypeChecker.Normalize.fst"
let _67_884 = comp
in (let _146_388 = (let _146_387 = (
# 567 "FStar.TypeChecker.Normalize.fst"
let _67_886 = ct
in (let _146_386 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _146_385 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _67_886.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _146_386; FStar_Syntax_Syntax.effect_args = _146_385; FStar_Syntax_Syntax.flags = _67_886.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_146_387))
in {FStar_Syntax_Syntax.n = _146_388; FStar_Syntax_Syntax.tk = _67_884.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _67_884.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _67_884.FStar_Syntax_Syntax.vars})))
end))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env _67_892 -> (match (_67_892) with
| (x, imp) -> begin
(let _146_393 = (
# 571 "FStar.TypeChecker.Normalize.fst"
let _67_893 = x
in (let _146_392 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _67_893.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _67_893.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _146_392}))
in (_146_393, imp))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (
# 575 "FStar.TypeChecker.Normalize.fst"
let _67_906 = (FStar_List.fold_left (fun _67_900 b -> (match (_67_900) with
| (nbs', env) -> begin
(
# 576 "FStar.TypeChecker.Normalize.fst"
let b = (norm_binder cfg env b)
in ((b)::nbs', (Dummy)::env))
end)) ([], env) bs)
in (match (_67_906) with
| (nbs, _67_905) -> begin
(FStar_List.rev nbs)
end)))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| Meta (m, r)::stack -> begin
(
# 590 "FStar.TypeChecker.Normalize.fst"
let t = (mk (FStar_Syntax_Syntax.Tm_meta ((t, m))) r)
in (rebuild cfg env stack t))
end
| MemoLazy (r)::stack -> begin
(
# 594 "FStar.TypeChecker.Normalize.fst"
let _67_923 = (set_memo r (env, t))
in (rebuild cfg env stack t))
end
| Abs (env', bs, env'', lopt, r)::stack -> begin
(
# 598 "FStar.TypeChecker.Normalize.fst"
let bs = (norm_binders cfg env' bs)
in (
# 599 "FStar.TypeChecker.Normalize.fst"
let lopt = (close_lcomp_opt cfg env'' lopt)
in (let _146_403 = (
# 600 "FStar.TypeChecker.Normalize.fst"
let _67_936 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = _67_936.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _67_936.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = _67_936.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _146_403))))
end
| (Arg (Univ (_), _, _)::_) | (Arg (Dummy, _, _)::_) -> begin
(FStar_All.failwith "Impossible")
end
| UnivArgs (us, r)::stack -> begin
(
# 606 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| Arg (Clos (env, tm, m), aq, r)::stack -> begin
(
# 610 "FStar.TypeChecker.Normalize.fst"
let _67_979 = (log cfg (fun _67_978 -> (match (()) with
| () -> begin
(let _146_405 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _146_405))
end)))
in (match ((FStar_ST.read m)) with
| None -> begin
if (FStar_List.contains WHNF cfg.steps) then begin
(
# 615 "FStar.TypeChecker.Normalize.fst"
let arg = (closure_as_term cfg env tm)
in (
# 616 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (arg, aq) None r)
in (rebuild cfg env stack t)))
end else begin
(
# 618 "FStar.TypeChecker.Normalize.fst"
let stack = (MemoLazy (m))::(App ((t, aq, r)))::stack
in (norm cfg env stack tm))
end
end
| Some (_67_986, a) -> begin
(
# 622 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app t (a, aq) None r)
in (rebuild cfg env stack t))
end))
end
| App (head, aq, r)::stack -> begin
(
# 627 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Syntax.extend_app head (t, aq) None r)
in (let _146_406 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _146_406)))
end
| Match (env, branches, r)::stack -> begin
(
# 631 "FStar.TypeChecker.Normalize.fst"
let norm_and_rebuild_match = (fun _67_1007 -> (match (()) with
| () -> begin
(
# 632 "FStar.TypeChecker.Normalize.fst"
let whnf = (FStar_List.contains WHNF cfg.steps)
in (
# 633 "FStar.TypeChecker.Normalize.fst"
let cfg = (
# 633 "FStar.TypeChecker.Normalize.fst"
let _67_1009 = cfg
in (let _146_409 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = _67_1009.steps; tcenv = _67_1009.tcenv; delta_level = _146_409}))
in (
# 634 "FStar.TypeChecker.Normalize.fst"
let norm_or_whnf = (fun env t -> if whnf then begin
(closure_as_term cfg env t)
end else begin
(norm cfg env [] t)
end)
in (
# 638 "FStar.TypeChecker.Normalize.fst"
let branches = (FStar_All.pipe_right branches (FStar_List.map (fun branch -> (
# 640 "FStar.TypeChecker.Normalize.fst"
let _67_1019 = (FStar_Syntax_Subst.open_branch branch)
in (match (_67_1019) with
| (p, wopt, e) -> begin
(
# 641 "FStar.TypeChecker.Normalize.fst"
let env = (let _146_417 = (FStar_Syntax_Syntax.pat_bvs p)
in (FStar_All.pipe_right _146_417 (FStar_List.fold_left (fun env x -> (Dummy)::env) env)))
in (
# 643 "FStar.TypeChecker.Normalize.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _146_418 = (norm_or_whnf env w)
in Some (_146_418))
end)
in (
# 646 "FStar.TypeChecker.Normalize.fst"
let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch (p, wopt, e)))))
end)))))
in (let _146_419 = (mk (FStar_Syntax_Syntax.Tm_match ((t, branches))) r)
in (rebuild cfg env stack _146_419))))))
end))
in (
# 650 "FStar.TypeChecker.Normalize.fst"
let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _67_1033) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Data_ctor))) | (FStar_Syntax_Syntax.Tm_fvar (_, Some (FStar_Syntax_Syntax.Record_ctor (_)))) -> begin
true
end
| _67_1054 -> begin
false
end))
in (
# 657 "FStar.TypeChecker.Normalize.fst"
let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(
# 661 "FStar.TypeChecker.Normalize.fst"
let then_branch = b
in (
# 662 "FStar.TypeChecker.Normalize.fst"
let else_branch = (mk (FStar_Syntax_Syntax.Tm_match ((t, rest))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (
# 666 "FStar.TypeChecker.Normalize.fst"
let rec matches_pat = (fun t p -> (
# 670 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (
# 671 "FStar.TypeChecker.Normalize.fst"
let _67_1071 = (FStar_Syntax_Util.head_and_args t)
in (match (_67_1071) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(
# 674 "FStar.TypeChecker.Normalize.fst"
let mopt = (FStar_Util.find_map ps (fun p -> (
# 675 "FStar.TypeChecker.Normalize.fst"
let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_67_1077) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_67_1094) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _67_1101 -> begin
(let _146_436 = (not ((is_cons head)))
in FStar_Util.Inr (_146_436))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _67_1109 -> begin
(let _146_437 = (not ((is_cons head)))
in FStar_Util.Inr (_146_437))
end)
end)
end))))
and matches_args = (fun out a p -> (match ((a, p)) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| ((t, _67_1119)::rest_a, (p, _67_1125)::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _67_1133 -> begin
FStar_Util.Inr (false)
end))
in (
# 708 "FStar.TypeChecker.Normalize.fst"
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
# 721 "FStar.TypeChecker.Normalize.fst"
let env = (FStar_List.fold_right (fun t env -> (let _146_449 = (let _146_448 = (let _146_447 = (FStar_Util.mk_ref (Some (([], t))))
in ([], t, _146_447))
in Clos (_146_448))
in (_146_449)::env)) s env)
in (let _146_450 = (guard_when_clause wopt b rest)
in (norm cfg env stack _146_450)))
end)
end))
in (matches t branches))))))
end))

# 726 "FStar.TypeChecker.Normalize.fst"
let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (
# 727 "FStar.TypeChecker.Normalize.fst"
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

# 734 "FStar.TypeChecker.Normalize.fst"
let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (norm (config s e) [] [] t))

# 735 "FStar.TypeChecker.Normalize.fst"
let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (norm_comp (config s e) [] t))

# 736 "FStar.TypeChecker.Normalize.fst"
let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (norm_universe (config [] env) [] u))

# 738 "FStar.TypeChecker.Normalize.fst"
let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _146_475 = (normalize ((EraseUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _146_475)))

# 739 "FStar.TypeChecker.Normalize.fst"
let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _146_480 = (norm_comp (config ((EraseUniverses)::[]) env) [] c)
in (FStar_Syntax_Print.comp_to_string _146_480)))

# 741 "FStar.TypeChecker.Normalize.fst"
let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (
# 742 "FStar.TypeChecker.Normalize.fst"
let t = (normalize (FStar_List.append steps ((Beta)::(WHNF)::[])) env t0)
in (
# 743 "FStar.TypeChecker.Normalize.fst"
let rec aux = (fun t -> (
# 744 "FStar.TypeChecker.Normalize.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(
# 747 "FStar.TypeChecker.Normalize.fst"
let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _146_491 = (let _146_490 = (let _146_489 = (FStar_Syntax_Util.mk_conj phi1 phi)
in (y, _146_489))
in FStar_Syntax_Syntax.Tm_refine (_146_490))
in (mk _146_491 t0.FStar_Syntax_Syntax.pos))
end
| _67_1185 -> begin
t
end))
end
| _67_1187 -> begin
t
end)))
in (aux t))))

# 756 "FStar.TypeChecker.Normalize.fst"
let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (
# 757 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(
# 761 "FStar.TypeChecker.Normalize.fst"
let _67_1198 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_67_1198) with
| (binders, cdef) -> begin
(
# 762 "FStar.TypeChecker.Normalize.fst"
let inst = (let _146_499 = (let _146_498 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_146_498)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _67_1202 _67_1206 -> (match ((_67_1202, _67_1206)) with
| ((x, _67_1201), (t, _67_1205)) -> begin
FStar_Syntax_Syntax.NT ((x, t))
end)) binders _146_499))
in (
# 763 "FStar.TypeChecker.Normalize.fst"
let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (
# 764 "FStar.TypeChecker.Normalize.fst"
let c = (FStar_All.pipe_right (
# 764 "FStar.TypeChecker.Normalize.fst"
let _67_1209 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _67_1209.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _67_1209.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _67_1209.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))

# 767 "FStar.TypeChecker.Normalize.fst"
let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _67_1212 _67_1214 _67_1216 -> (FStar_All.failwith "NYI: normalize_sigelt"))

# 768 "FStar.TypeChecker.Normalize.fst"
let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _67_1218 t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 771 "FStar.TypeChecker.Normalize.fst"
let _67_1225 = (FStar_Syntax_Util.arrow_formals_comp x.FStar_Syntax_Syntax.sort)
in (match (_67_1225) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _67_1228 -> begin
(
# 775 "FStar.TypeChecker.Normalize.fst"
let _67_1231 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_67_1231) with
| (binders, args) -> begin
(let _146_512 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _146_511 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _146_510 -> Some (_146_510)))
in (FStar_Syntax_Util.abs binders _146_512 _146_511)))
end))
end)
end))
end
| _67_1233 -> begin
(let _146_515 = (let _146_514 = (FStar_Syntax_Print.tag_of_term t)
in (let _146_513 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _146_514 _146_513)))
in (FStar_All.failwith _146_515))
end))






open Prims

type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Inline
| NoInline
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| DeltaComp
| SNComp
| Eta
| EtaArgs
| Unmeta
| Unlabel 
 and steps =
step Prims.list


let is_Beta = (fun _discr_ -> (match (_discr_) with
| Beta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Iota = (fun _discr_ -> (match (_discr_) with
| Iota (_) -> begin
true
end
| _ -> begin
false
end))


let is_Zeta = (fun _discr_ -> (match (_discr_) with
| Zeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Exclude = (fun _discr_ -> (match (_discr_) with
| Exclude (_) -> begin
true
end
| _ -> begin
false
end))


let is_WHNF = (fun _discr_ -> (match (_discr_) with
| WHNF (_) -> begin
true
end
| _ -> begin
false
end))


let is_Inline = (fun _discr_ -> (match (_discr_) with
| Inline (_) -> begin
true
end
| _ -> begin
false
end))


let is_NoInline = (fun _discr_ -> (match (_discr_) with
| NoInline (_) -> begin
true
end
| _ -> begin
false
end))


let is_UnfoldUntil = (fun _discr_ -> (match (_discr_) with
| UnfoldUntil (_) -> begin
true
end
| _ -> begin
false
end))


let is_Simplify = (fun _discr_ -> (match (_discr_) with
| Simplify (_) -> begin
true
end
| _ -> begin
false
end))


let is_EraseUniverses = (fun _discr_ -> (match (_discr_) with
| EraseUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_AllowUnboundUniverses = (fun _discr_ -> (match (_discr_) with
| AllowUnboundUniverses (_) -> begin
true
end
| _ -> begin
false
end))


let is_Reify = (fun _discr_ -> (match (_discr_) with
| Reify (_) -> begin
true
end
| _ -> begin
false
end))


let is_DeltaComp = (fun _discr_ -> (match (_discr_) with
| DeltaComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_SNComp = (fun _discr_ -> (match (_discr_) with
| SNComp (_) -> begin
true
end
| _ -> begin
false
end))


let is_Eta = (fun _discr_ -> (match (_discr_) with
| Eta (_) -> begin
true
end
| _ -> begin
false
end))


let is_EtaArgs = (fun _discr_ -> (match (_discr_) with
| EtaArgs (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unmeta = (fun _discr_ -> (match (_discr_) with
| Unmeta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Unlabel = (fun _discr_ -> (match (_discr_) with
| Unlabel (_) -> begin
true
end
| _ -> begin
false
end))


let ___Exclude____0 = (fun projectee -> (match (projectee) with
| Exclude (_53_7) -> begin
_53_7
end))


let ___UnfoldUntil____0 = (fun projectee -> (match (projectee) with
| UnfoldUntil (_53_10) -> begin
_53_10
end))


type closure =
| Clos of (env * FStar_Syntax_Syntax.term * (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Open of (FStar_Syntax_Syntax.bv * Prims.int)
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


let is_Open = (fun _discr_ -> (match (_discr_) with
| Open (_) -> begin
true
end
| _ -> begin
false
end))


let is_Dummy = (fun _discr_ -> (match (_discr_) with
| Dummy (_) -> begin
true
end
| _ -> begin
false
end))


let ___Clos____0 = (fun projectee -> (match (projectee) with
| Clos (_53_13) -> begin
_53_13
end))


let ___Univ____0 = (fun projectee -> (match (projectee) with
| Univ (_53_16) -> begin
_53_16
end))


let ___Open____0 = (fun projectee -> (match (projectee) with
| Open (_53_19) -> begin
_53_19
end))


let closure_to_string : closure  ->  Prims.string = (fun _53_1 -> (match (_53_1) with
| Clos (_53_22, t, _53_25, _53_27) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| _53_31 -> begin
"dummy"
end))


type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level; index_level : Prims.int; no_reduction : Prims.bool}


let is_Mkcfg : cfg  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkcfg"))))


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list


type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| Match of (env * branches * FStar_Range.range * Prims.int)
| Abs of (env * FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option * FStar_Range.range * Prims.int)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range * Prims.int)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range * Prims.int)
| Let of (env * FStar_Syntax_Syntax.letbinding * FStar_Range.range * Prims.int)


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


let is_Meta = (fun _discr_ -> (match (_discr_) with
| Meta (_) -> begin
true
end
| _ -> begin
false
end))


let is_Let = (fun _discr_ -> (match (_discr_) with
| Let (_) -> begin
true
end
| _ -> begin
false
end))


let ___Arg____0 = (fun projectee -> (match (projectee) with
| Arg (_53_40) -> begin
_53_40
end))


let ___UnivArgs____0 = (fun projectee -> (match (projectee) with
| UnivArgs (_53_43) -> begin
_53_43
end))


let ___Match____0 = (fun projectee -> (match (projectee) with
| Match (_53_46) -> begin
_53_46
end))


let ___Abs____0 = (fun projectee -> (match (projectee) with
| Abs (_53_49) -> begin
_53_49
end))


let ___App____0 = (fun projectee -> (match (projectee) with
| App (_53_52) -> begin
_53_52
end))


let ___Meta____0 = (fun projectee -> (match (projectee) with
| Meta (_53_55) -> begin
_53_55
end))


let ___Let____0 = (fun projectee -> (match (projectee) with
| Let (_53_58) -> begin
_53_58
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (match ((FStar_ST.read r)) with
| Some (_53_64) -> begin
(FStar_All.failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.op_Colon_Equals r (Some (t)))
end))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _145_210 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _145_210 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun _53_2 -> (match (_53_2) with
| Arg (c, _53_71, _53_73) -> begin
(closure_to_string c)
end
| Abs (_53_77, bs, _53_80, _53_82, _53_84) -> begin
(let _145_213 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _145_213))
end
| _53_88 -> begin
"Match"
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _145_216 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _145_216 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> if (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm"))) then begin
(f ())
end else begin
()
end)


let is_empty = (fun _53_3 -> (match (_53_3) with
| [] -> begin
true
end
| _53_95 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| _53_102 -> begin
(let _145_232 = (let _145_231 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _145_231))
in (FStar_All.failwith _145_232))
end)


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (FStar_Syntax_Util.comp_to_comp_typ comp)
in (match ((let _145_237 = (env.FStar_TypeChecker_Env.universe_of env c.FStar_Syntax_Syntax.result_typ)
in (FStar_TypeChecker_Env.lookup_effect_abbrev env _145_237 c.FStar_Syntax_Syntax.effect_name))) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let _53_115 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (_53_115) with
| (binders, cdef) -> begin
(

let inst = (let _145_241 = (let _145_240 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_145_240)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun _53_119 _53_123 -> (match (((_53_119), (_53_123))) with
| ((x, _53_118), (t, _53_122)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _145_241))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (FStar_All.pipe_right (

let _53_126 = (FStar_Syntax_Util.comp_to_comp_typ c1)
in {FStar_Syntax_Syntax.effect_name = _53_126.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _53_126.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_126.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}) FStar_Syntax_Syntax.mk_Comp)
in (unfold_effect_abbrev env c))))
end))
end)))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid) then begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid) then begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end else begin
if (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid) then begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end else begin
None
end
end
end)


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let _53_148 = (FStar_List.fold_left (fun _53_139 u -> (match (_53_139) with
| (cur_kernel, cur_max, out) -> begin
(

let _53_143 = (FStar_Syntax_Util.univ_kernel u)
in (match (_53_143) with
| (k_u, n) -> begin
if (FStar_Syntax_Util.eq_univs cur_kernel k_u) then begin
((cur_kernel), (u), (out))
end else begin
((k_u), (u), ((cur_max)::out))
end
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (_53_148) with
| (_53_145, u, out) -> begin
(FStar_List.rev ((u)::out))
end))))
in (

let rec aux = (fun u -> (

let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
try
(match (()) with
| () -> begin
(match ((FStar_List.nth env x)) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| _53_165 -> begin
(FStar_All.failwith "Impossible: universe variable bound to a term")
end)
end)
with
| _53_158 -> begin
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
(let _145_258 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _145_258 norm_univs))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _145_260 = (aux u)
in (FStar_List.map (fun _145_259 -> FStar_Syntax_Syntax.U_succ (_145_259)) _145_260))
end)))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
FStar_Syntax_Syntax.U_unknown
end else begin
(match ((aux u)) with
| ([]) | ((FStar_Syntax_Syntax.U_zero)::[]) -> begin
FStar_Syntax_Syntax.U_zero
end
| (FStar_Syntax_Syntax.U_zero)::(u)::[] -> begin
u
end
| (FStar_Syntax_Syntax.U_zero)::us -> begin
FStar_Syntax_Syntax.U_max (us)
end
| (u)::[] -> begin
u
end
| us -> begin
FStar_Syntax_Syntax.U_max (us)
end)
end)))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let _53_196 = t
in {FStar_Syntax_Syntax.n = _53_196.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _53_196.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_196.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| _53_205 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in if (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps)) then begin
tm
end else begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_283 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| _53_326 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), _53_353))::((_53_344, (arg, _53_347)))::[] -> begin
arg
end
| _53_357 -> begin
tm
end)
end else begin
if (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid) then begin
(match ((FStar_All.pipe_right args (FStar_List.map simplify))) with
| ((Some (true), _53_361))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), _53_367))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| _53_371 -> begin
tm
end)
end else begin
if ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid)) then begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(match ((let _145_271 = (FStar_Syntax_Subst.compress t)
in _145_271.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs ((_53_389)::[], body, _53_393) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| _53_401 -> begin
tm
end)
end
| _53_403 -> begin
tm
end)
end
| _53_405 -> begin
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
| _53_407 -> begin
tm
end)
end))))


let set_level : cfg  ->  Prims.int  ->  cfg = (fun cfg n -> (

let _53_410 = cfg
in {steps = _53_410.steps; tcenv = _53_410.tcenv; delta_level = _53_410.delta_level; index_level = n; no_reduction = _53_410.no_reduction}))


let incr_level : cfg  ->  cfg = (fun cfg -> (

let _53_413 = cfg
in {steps = _53_413.steps; tcenv = _53_413.tcenv; delta_level = _53_413.delta_level; index_level = (cfg.index_level + 1); no_reduction = _53_413.no_reduction}))


let no_steps_if_whnf : cfg  ->  cfg = (fun cfg -> if (FStar_List.contains WHNF cfg.steps) then begin
(

let _53_416 = cfg
in {steps = _53_416.steps; tcenv = _53_416.tcenv; delta_level = _53_416.delta_level; index_level = _53_416.index_level; no_reduction = true})
end else begin
cfg
end)


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> if (cfg.no_reduction && (FStar_List.isEmpty env)) then begin
(rebuild cfg env stack t)
end else begin
(

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_424 = (log cfg (fun _53_423 -> (match (()) with
| () -> begin
(let _145_310 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_309 = (FStar_Util.string_of_int cfg.index_level)
in (let _145_308 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print3 ">>> %s\nNorm(%s) %s\n" _145_310 _145_309 _145_308))))
end)))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_53_427) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_469; FStar_Syntax_Syntax.pos = _53_467; FStar_Syntax_Syntax.vars = _53_465}, (a1)::(a2)::rest) -> begin
(

let _53_483 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_483) with
| (hd, _53_482) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _53_491; FStar_Syntax_Syntax.pos = _53_489; FStar_Syntax_Syntax.vars = _53_487}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let _53_502 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_502) with
| (reify_head, _53_501) -> begin
(

let a = (FStar_Syntax_Subst.compress (Prims.fst a))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic (m)) -> begin
(match ((let _145_314 = (FStar_Syntax_Subst.compress e)
in _145_314.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let _53_520 = ed.FStar_Syntax_Syntax.bind_repr
in (match (_53_520) with
| (_53_518, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (let _145_319 = (let _145_318 = (let _145_317 = (let _145_315 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_315)::[])
in (let _145_316 = (FStar_Syntax_Util.mk_reify body)
in ((_145_317), (_145_316), (None))))
in FStar_Syntax_Syntax.Tm_abs (_145_318))
in (FStar_Syntax_Syntax.mk _145_319 None body.FStar_Syntax_Syntax.pos))
in (

let reified = (let _145_333 = (let _145_332 = (let _145_331 = (let _145_330 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_329 = (let _145_328 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_327 = (let _145_326 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_325 = (let _145_324 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _145_323 = (let _145_322 = (FStar_Syntax_Syntax.as_arg head)
in (let _145_321 = (let _145_320 = (FStar_Syntax_Syntax.as_arg body)
in (_145_320)::[])
in (_145_322)::_145_321))
in (_145_324)::_145_323))
in (_145_326)::_145_325))
in (_145_328)::_145_327))
in (_145_330)::_145_329))
in ((bind_repr), (_145_331)))
in FStar_Syntax_Syntax.Tm_app (_145_332))
in (FStar_Syntax_Syntax.mk _145_333 None t.FStar_Syntax_Syntax.pos))
in (norm cfg env stack reified))))
end
| FStar_Util.Inr (_53_527) -> begin
(FStar_All.failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (_53_530) -> begin
(FStar_All.failwith "NYI: monadic application")
end
| _53_533 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack
in (norm cfg env stack a))
end)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_53_542)); FStar_Syntax_Syntax.tk = _53_540; FStar_Syntax_Syntax.pos = _53_538; FStar_Syntax_Syntax.vars = _53_536}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let e = (FStar_Syntax_Util.mk_reify e)
in (

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun _53_558 -> (match (_53_558) with
| (pat, wopt, tm) -> begin
(let _145_335 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_145_335)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack tm))))
end
| _53_562 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _145_336 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_336)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
if (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) then begin
(norm cfg env stack t')
end else begin
(

let us = (let _145_338 = (let _145_337 = (FStar_List.map (norm_universe cfg env) us)
in ((_145_337), (t.FStar_Syntax_Syntax.pos)))
in UnivArgs (_145_338))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

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
in if (cfg.no_reduction || (not (should_delta))) then begin
(rebuild cfg env stack t)
end else begin
(match ((FStar_TypeChecker_Env.lookup_definition cfg.delta_level cfg.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(rebuild cfg env stack t)
end
| Some (us, t) -> begin
(

let _53_587 = (log cfg (fun _53_586 -> (match (()) with
| () -> begin
(let _145_341 = (FStar_Syntax_Print.term_to_string t0)
in (let _145_340 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _145_341 _145_340)))
end)))
in (

let n = (FStar_List.length us)
in if (n > 0) then begin
(match (stack) with
| (UnivArgs (us', _53_593))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| _53_601 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| _53_603 -> begin
(let _145_345 = (let _145_344 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _145_344))
in (FStar_All.failwith _145_345))
end)
end else begin
(norm cfg env stack t)
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(match ((lookup_bvar env x)) with
| Univ (_53_607) -> begin
(FStar_All.failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(FStar_All.failwith "Term variable not found")
end
| Open (_53_611, n) -> begin
(

let y = (

let _53_615 = x
in {FStar_Syntax_Syntax.ppname = _53_615.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = (cfg.index_level - n); FStar_Syntax_Syntax.sort = _53_615.FStar_Syntax_Syntax.sort})
in (rebuild cfg env stack (

let _53_618 = t
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_bvar (y); FStar_Syntax_Syntax.tk = _53_618.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_618.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_618.FStar_Syntax_Syntax.vars})))
end
| Clos (env, t0, r, fix) -> begin
if ((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps)))) then begin
(match ((FStar_ST.read r)) with
| Some (env, t') -> begin
(

let _53_631 = (log cfg (fun _53_630 -> (match (()) with
| () -> begin
(let _145_348 = (FStar_Syntax_Print.term_to_string t)
in (let _145_347 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _145_348 _145_347)))
end)))
in (match ((let _145_349 = (FStar_Syntax_Subst.compress t')
in _145_349.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_53_634) -> begin
(norm cfg env stack t')
end
| _53_637 -> begin
(rebuild cfg env stack t')
end))
end
| None -> begin
(norm cfg env stack t0)
end)
end else begin
(norm cfg env stack t0)
end
end)
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (Meta (_53_647))::_53_645 -> begin
(FStar_All.failwith "Labeled abstraction")
end
| (UnivArgs (_53_653))::_53_651 -> begin
(FStar_All.failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (_53_659))::_53_657 -> begin
(FStar_All.failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, _53_665, _53_667))::stack when (not (cfg.no_reduction)) -> begin
(match (c) with
| Univ (_53_672) -> begin
(norm cfg ((c)::env) stack t)
end
| _53_675 -> begin
(match (bs) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (_53_678)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
(

let _53_682 = (log cfg (fun _53_681 -> (match (()) with
| () -> begin
(let _145_351 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_351))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inr (l)) when ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) -> begin
(

let _53_688 = (log cfg (fun _53_687 -> (match (()) with
| () -> begin
(let _145_353 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_353))
end)))
in (norm cfg ((c)::env) stack body))
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
(

let _53_694 = (log cfg (fun _53_693 -> (match (()) with
| () -> begin
(let _145_355 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_355))
end)))
in (norm cfg ((c)::env) stack body))
end
| _53_697 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack body)
end
| _53_699 -> begin
(

let cfg = (

let _53_700 = cfg
in {steps = _53_700.steps; tcenv = _53_700.tcenv; delta_level = _53_700.delta_level; index_level = _53_700.index_level; no_reduction = true})
in (norm cfg env stack t))
end)
end
| (_53_705)::tl -> begin
(

let _53_708 = (log cfg (fun _53_707 -> (match (()) with
| () -> begin
(let _145_357 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _145_357))
end)))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack body)))
end)
end)
end
| ((Arg (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
(

let cfg = (no_steps_if_whnf cfg)
in (

let _53_740 = (norm_binders2 cfg env bs)
in (match (_53_740) with
| (cfg', env', bs) -> begin
(

let lopt = (norm_lcomp_opt cfg' env' lopt)
in (norm cfg' env' ((Abs (((env), (bs), (lopt), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack) body))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun _53_748 stack -> (match (_53_748) with
| (a, aq) -> begin
(let _145_364 = (let _145_363 = (let _145_362 = (let _145_361 = (let _145_360 = (FStar_Util.mk_ref None)
in ((env), (a), (_145_360), (false)))
in Clos (_145_361))
in ((_145_362), (aq), (t.FStar_Syntax_Syntax.pos)))
in Arg (_145_363))
in (_145_364)::stack)
end)) args))
in (

let _53_752 = (log cfg (fun _53_751 -> (match (()) with
| () -> begin
(let _145_366 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _145_366))
end)))
in (norm cfg env stack head)))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let cfg = (no_steps_if_whnf cfg)
in (

let cfg' = (

let _53_760 = cfg
in {steps = _53_760.steps; tcenv = _53_760.tcenv; delta_level = _53_760.delta_level; index_level = (cfg.index_level + 1); no_reduction = _53_760.no_reduction})
in (

let env' = (Open (((x), (cfg'.index_level))))::env
in (

let f = (norm cfg' env' [] f)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let _53_765 = x
in {FStar_Syntax_Syntax.ppname = _53_765.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_765.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let cfg = (no_steps_if_whnf cfg)
in (

let _53_776 = (norm_binders2 cfg env bs)
in (match (_53_776) with
| (cfg, env, bs) -> begin
(

let c = (norm_comp cfg env c)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) None t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end)))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) -> begin
(norm cfg env stack t1)
end
| _53_797 -> begin
(

let t1 = (norm cfg env [] t1)
in (

let _53_800 = (log cfg (fun _53_799 -> (match (()) with
| () -> begin
(FStar_Util.print_string "+++ Normalizing ascription \n")
end)))
in (

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
(let _145_368 = (norm cfg env [] t)
in FStar_Util.Inl (_145_368))
end
| FStar_Util.Inr (c) -> begin
(let _145_369 = (norm_comp cfg env c)
in FStar_Util.Inr (_145_369))
end)
in (let _145_370 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _145_370)))))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((_53_813, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_53_825); FStar_Syntax_Syntax.lbunivs = _53_823; FStar_Syntax_Syntax.lbtyp = _53_821; FStar_Syntax_Syntax.lbeff = _53_819; FStar_Syntax_Syntax.lbdef = _53_817})::_53_815), _53_831) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in if (((not (cfg.no_reduction)) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoInline))))) && ((FStar_Syntax_Util.is_pure_effect n) || (FStar_Syntax_Util.is_ghost_effect n))) then begin
(

let env = (let _145_373 = (let _145_372 = (let _145_371 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_145_371), (false)))
in Clos (_145_372))
in (_145_373)::env)
in (norm cfg env stack body))
end else begin
(

let t_x = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (

let x = (

let _53_844 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_844.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_844.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})
in (

let lb = (

let _53_847 = lb
in (let _145_374 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _53_847.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = t_x; FStar_Syntax_Syntax.lbeff = _53_847.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _145_374}))
in (

let cfg' = (

let _53_850 = cfg
in {steps = _53_850.steps; tcenv = _53_850.tcenv; delta_level = _53_850.delta_level; index_level = (cfg.index_level + 1); no_reduction = _53_850.no_reduction})
in (

let env' = (Open (((x), (cfg'.index_level))))::env
in (

let stack = (Let (((env), (lb), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack
in (norm cfg' env' stack body)))))))
end)
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when ((FStar_List.contains (Exclude (Zeta)) cfg.steps) || cfg.no_reduction) -> begin
(

let cfg = (

let _53_859 = cfg
in {steps = _53_859.steps; tcenv = _53_859.tcenv; delta_level = _53_859.delta_level; index_level = _53_859.index_level; no_reduction = true})
in (rebuild cfg env stack t))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let _53_881 = (FStar_List.fold_right (fun lb _53_870 -> (match (_53_870) with
| (rec_env, memos, i) -> begin
(

let f_i = (let _145_377 = (

let _53_871 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = _53_871.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _53_871.FStar_Syntax_Syntax.sort})
in (FStar_Syntax_Syntax.bv_to_tm _145_377))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + 1)))))))
end)) (Prims.snd lbs) ((env), ([]), (0)))
in (match (_53_881) with
| (rec_env, memos, _53_880) -> begin
(

let _53_884 = (FStar_List.map2 (fun lb memo -> (FStar_ST.op_Colon_Equals memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _145_384 = (let _145_383 = (let _145_382 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_145_382), (false)))
in Clos (_145_383))
in (_145_384)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (stack) with
| (_53_896)::_53_894 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, _53_901) -> begin
(norm cfg env ((Meta (((m), (r), (cfg.index_level))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos), (cfg.index_level))))::stack) head))
end
| _53_908 -> begin
(norm cfg env stack head)
end)
end
| _53_910 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(let _145_385 = (norm_pattern_args cfg env args)
in FStar_Syntax_Syntax.Meta_pattern (_145_385))
end
| _53_915 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)))
end)
and norm_binders2 : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  (cfg * env * FStar_Syntax_Syntax.binders) = (fun cfg env bs -> (

let _53_939 = (FStar_List.fold_left (fun _53_924 _53_927 -> (match (((_53_924), (_53_927))) with
| ((cfg, env, bs), (x, aq)) -> begin
(

let x = (

let _53_928 = x
in (let _145_391 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_928.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_928.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_391}))
in (

let cfg = (

let _53_931 = cfg
in {steps = _53_931.steps; tcenv = _53_931.tcenv; delta_level = _53_931.delta_level; index_level = (cfg.index_level + 1); no_reduction = _53_931.no_reduction})
in (

let env = (Open (((x), (cfg.index_level))))::env
in (

let bs = (((x), (aq)))::bs
in ((cfg), (env), (bs))))))
end)) ((cfg), (env), ([])) bs)
in (match (_53_939) with
| (cfg, env, bs) -> begin
(

let bs = (FStar_List.rev bs)
in ((cfg), (env), (bs)))
end)))
and norm_pattern_args : cfg  ->  env  ->  FStar_Syntax_Syntax.args Prims.list  ->  FStar_Syntax_Syntax.args Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun _53_946 -> (match (_53_946) with
| (a, imp) -> begin
(let _145_396 = (norm cfg env [] a)
in ((_145_396), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(

let _53_953 = comp
in (let _145_401 = (let _145_400 = (norm cfg env [] t)
in FStar_Syntax_Syntax.Total (_145_400))
in {FStar_Syntax_Syntax.n = _145_401; FStar_Syntax_Syntax.tk = _53_953.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_953.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_953.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(

let _53_957 = comp
in (let _145_403 = (let _145_402 = (norm cfg env [] t)
in FStar_Syntax_Syntax.GTotal (_145_402))
in {FStar_Syntax_Syntax.n = _145_403; FStar_Syntax_Syntax.tk = _53_957.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_957.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_957.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun _53_965 -> (match (_53_965) with
| (a, i) -> begin
(let _145_407 = (norm cfg env [] a)
in ((_145_407), (i)))
end)))))
in (

let _53_966 = comp
in (let _145_411 = (let _145_410 = (

let _53_968 = ct
in (let _145_409 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _145_408 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.effect_name = _53_968.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _145_409; FStar_Syntax_Syntax.effect_args = _145_408; FStar_Syntax_Syntax.flags = _53_968.FStar_Syntax_Syntax.flags})))
in FStar_Syntax_Syntax.Comp (_145_410))
in {FStar_Syntax_Syntax.n = _145_411; FStar_Syntax_Syntax.tk = _53_966.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_966.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_966.FStar_Syntax_Syntax.vars})))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let _53_975 = cfg
in {steps = (Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]; tcenv = _53_975.tcenv; delta_level = _53_975.delta_level; index_level = _53_975.index_level; no_reduction = _53_975.no_reduction}) env [] t))
in (

let non_info = (fun t -> (let _145_419 = (norm t)
in (FStar_Syntax_Util.non_informative _145_419)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (_53_980) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t) when (non_info t) -> begin
(

let _53_984 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (t); FStar_Syntax_Syntax.tk = _53_984.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_984.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_984.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in if ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ)) then begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let _53_991 = ct
in {FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = _53_991.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_991.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_991.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let _53_995 = ct
in {FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = _53_995.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _53_995.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = _53_995.FStar_Syntax_Syntax.flags}))
end)
in (

let _53_998 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = _53_998.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = _53_998.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = _53_998.FStar_Syntax_Syntax.vars}))
end else begin
c
end)
end
| _53_1001 -> begin
c
end))))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
if (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) then begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in if (FStar_Syntax_Util.is_total_lcomp lc) then begin
(let _145_425 = (let _145_424 = (let _145_423 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.lcomp_of_comp _145_423))
in FStar_Util.Inl (_145_424))
in Some (_145_425))
end else begin
(let _145_428 = (let _145_427 = (let _145_426 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.lcomp_of_comp _145_426))
in FStar_Util.Inl (_145_427))
in Some (_145_428))
end)
end else begin
Some (FStar_Util.Inr (lc.FStar_Syntax_Syntax.eff_name))
end
end
| _53_1010 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Meta (m, r, n))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild (set_level cfg n) env stack t))
end
| (Let (env', lb, r, n))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (t)))) None r)
in (rebuild (set_level cfg n) env' stack t))
end
| (Abs (_53_1035, bs, lopt, r, n))::stack -> begin
(let _145_433 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (t), (lopt)))) None r)
in (rebuild (set_level cfg n) env stack _145_433))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(FStar_All.failwith "Impossible")
end
| (Arg (Open (x, n), aq, r))::stack -> begin
(

let x = (

let _53_1075 = x
in {FStar_Syntax_Syntax.ppname = _53_1075.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = (cfg.index_level - n); FStar_Syntax_Syntax.sort = _53_1075.FStar_Syntax_Syntax.sort})
in (

let a = (FStar_Syntax_Syntax.bv_to_tm x)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))))
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, _53_1092), aq, r))::stack -> begin
(

let _53_1101 = (log cfg (fun _53_1100 -> (match (()) with
| () -> begin
(let _145_435 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _145_435))
end)))
in if ((FStar_List.contains (Exclude (Zeta)) cfg.steps) || cfg.no_reduction) then begin
(

let cfg = (no_steps_if_whnf cfg)
in (

let stack = (App (((t), (aq), (r), (cfg.index_level))))::stack
in (norm cfg env stack tm)))
end else begin
(match ((FStar_ST.read m)) with
| None -> begin
(

let cfg = (no_steps_if_whnf cfg)
in (

let stack = (App (((t), (aq), (r), (cfg.index_level))))::stack
in (norm cfg env stack tm)))
end
| Some (_53_1109, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end)
end)
end
| (App (head, aq, r, n))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _145_436 = (maybe_simplify cfg.steps t)
in (rebuild (

let _53_1123 = cfg
in {steps = _53_1123.steps; tcenv = _53_1123.tcenv; delta_level = _53_1123.delta_level; index_level = n; no_reduction = _53_1123.no_reduction}) env stack _145_436)))
end
| (Match (env, branches, r, n))::stack -> begin
(

let _53_1134 = (log cfg (fun _53_1133 -> (match (()) with
| () -> begin
(let _145_438 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _145_438))
end)))
in (

let norm_and_rebuild_match = (fun _53_1137 -> (match (()) with
| () -> begin
(

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg = (

let _53_1139 = cfg
in (let _145_441 = (FStar_TypeChecker_Env.glb_delta cfg.delta_level FStar_TypeChecker_Env.OnlyInline)
in {steps = (Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = _53_1139.tcenv; delta_level = _145_441; index_level = _53_1139.index_level; no_reduction = _53_1139.no_reduction}))
in (

let norm_or_close = (fun cfg env t -> (norm (no_steps_if_whnf cfg) env [] t))
in (

let rec norm_pat_and_extend_env = (fun cfg env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (_53_1151) -> begin
((cfg), (p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let _53_1162 = (norm_pat_and_extend_env cfg env hd)
in (match (_53_1162) with
| (cfg, hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (

let _53_1169 = (norm_pat_and_extend_env cfg env p)
in (match (_53_1169) with
| (_53_1165, p, _53_1168) -> begin
p
end)))))
in ((cfg), ((

let _53_1171 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = _53_1171.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1171.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _53_1191 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _53_1180 _53_1183 -> (match (((_53_1180), (_53_1183))) with
| ((cfg, pats, env), (p, b)) -> begin
(

let _53_1187 = (norm_pat_and_extend_env cfg env p)
in (match (_53_1187) with
| (cfg, p, env) -> begin
((cfg), ((((p), (b)))::pats), (env))
end))
end)) ((cfg), ([]), (env))))
in (match (_53_1191) with
| (cfg, pats, env) -> begin
((cfg), ((

let _53_1192 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = _53_1192.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1192.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _53_1196 = x
in (let _145_457 = (norm_or_close cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1196.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1196.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_457}))
in (

let cfg = (incr_level cfg)
in ((cfg), ((

let _53_1200 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _53_1200.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1200.FStar_Syntax_Syntax.p})), ((Open (((x), (cfg.index_level))))::env))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _53_1204 = x
in (let _145_458 = (norm_or_close cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1204.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1204.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_458}))
in (

let cfg = (incr_level cfg)
in ((cfg), ((

let _53_1208 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _53_1208.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1208.FStar_Syntax_Syntax.p})), ((Open (((x), (cfg.index_level))))::env))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let _53_1214 = x
in (let _145_459 = (norm_or_close cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _53_1214.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _53_1214.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_459}))
in (

let t = (norm_or_close cfg env t)
in ((cfg), ((

let _53_1218 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = _53_1218.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _53_1218.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| _53_1222 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let _53_1227 = (FStar_Syntax_Subst.open_branch branch)
in (match (_53_1227) with
| (p, wopt, e) -> begin
(

let _53_1231 = (norm_pat_and_extend_env cfg env p)
in (match (_53_1231) with
| (cfg, p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _145_461 = (norm_or_close cfg env w)
in Some (_145_461))
end)
in (

let e = (norm_or_close cfg env e)
in ((p), (wopt), (e))))
end))
end)))))
end)
in (let _145_462 = (mk (FStar_Syntax_Syntax.Tm_match (((t), (branches)))) r)
in (rebuild cfg env stack _145_462)))))))
end))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, _53_1242) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| _53_1267 -> begin
false
end))
in (

let rec matches_pat = (fun t p -> (

let t = (FStar_Syntax_Subst.compress t)
in (

let _53_1274 = (FStar_Syntax_Util.head_and_args t)
in (match (_53_1274) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat t p)
in (match (m) with
| FStar_Util.Inl (_53_1280) -> begin
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
| FStar_Syntax_Syntax.Pat_dot_term (_53_1297) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| _53_1304 -> begin
(let _145_470 = (not ((is_cons head)))
in FStar_Util.Inr (_145_470))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let rec matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, _53_1319))::rest_a, ((p, _53_1325))::rest_p) -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end)
end
| _53_1333 -> begin
FStar_Util.Inr (false)
end))
in (match ((let _145_477 = (FStar_Syntax_Util.un_uinst head)
in _145_477.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| _53_1337 -> begin
(let _145_478 = (not ((is_cons head)))
in FStar_Util.Inr (_145_478))
end))
end)
end))))
in (

let rec matches = (fun t p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(match ((matches_pat t p)) with
| FStar_Util.Inr (false) -> begin
(matches t rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
(

let _53_1355 = (log cfg (fun _53_1354 -> (match (()) with
| () -> begin
(let _145_486 = (FStar_Syntax_Print.pat_to_string p)
in (let _145_485 = (let _145_484 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _145_484 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _145_486 _145_485)))
end)))
in (

let env = (FStar_List.fold_left (fun env t -> (let _145_491 = (let _145_490 = (let _145_489 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_145_489), (false)))
in Clos (_145_490))
in (_145_491)::env)) env s)
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((t), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (let _145_498 = (guard_when_clause wopt b rest)
in (norm cfg env stack _145_498)))))
end)
end))
in if (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota)))) then begin
(norm_and_rebuild_match ())
end else begin
(matches t branches)
end)))))
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (match ((FStar_Util.find_map s (fun _53_4 -> (match (_53_4) with
| UnfoldUntil (k) -> begin
Some (k)
end
| _53_1375 -> begin
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
in {steps = (Beta)::s; tcenv = e; delta_level = d; index_level = 0; no_reduction = false}))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (

let _53_1383 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug e) (FStar_Options.Other ("Norm"))) then begin
(let _145_510 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "$$$$$$$$$$$$$Normalizing %s\n" _145_510))
end else begin
()
end
in (

let t = (let _145_511 = (config s e)
in (norm _145_511 [] [] t))
in (

let _53_1386 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug e) (FStar_Options.Other ("Norm"))) then begin
(let _145_512 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "#############Normalizing %s\n" _145_512))
end else begin
()
end
in t))))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _145_519 = (config s e)
in (norm_comp _145_519 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _145_524 = (config [] env)
in (norm_universe _145_524 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _145_529 = (config [] env)
in (ghost_to_pure_aux _145_529 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Inline)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (let _145_536 = (norm cfg [] [] t)
in (FStar_Syntax_Util.non_informative _145_536)))
in if ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ)) then begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let _53_1402 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = _53_1402.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = _53_1402.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _53_1404 -> (match (()) with
| () -> begin
(let _145_538 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _145_538))
end))})
end
| None -> begin
lc
end)
end else begin
lc
end)))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (let _145_543 = (normalize ((AllowUnboundUniverses)::[]) env t)
in (FStar_Syntax_Print.term_to_string _145_543)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (let _145_549 = (let _145_548 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _145_548 [] c))
in (FStar_Syntax_Print.comp_to_string _145_549)))


let normalize_refinement : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun steps env t0 -> (

let t = (normalize (FStar_List.append steps ((Beta)::[])) env t0)
in (

let rec aux = (fun t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let t0 = (aux x.FStar_Syntax_Syntax.sort)
in (match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (y, phi1) -> begin
(let _145_560 = (let _145_559 = (let _145_558 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_145_558)))
in FStar_Syntax_Syntax.Tm_refine (_145_559))
in (mk _145_560 t0.FStar_Syntax_Syntax.pos))
end
| _53_1427 -> begin
t
end))
end
| _53_1429 -> begin
t
end)))
in (aux t))))


let normalize_sigelt : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun _53_1430 _53_1432 _53_1434 -> (FStar_All.failwith "NYI: normalize_sigelt"))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun _53_1436 t -> (

let expand = (fun sort -> (

let _53_1443 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (_53_1443) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| _53_1446 -> begin
(

let _53_1449 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (_53_1449) with
| (binders, args) -> begin
(let _145_577 = (FStar_Syntax_Syntax.mk_Tm_app t args None t.FStar_Syntax_Syntax.pos)
in (let _145_576 = (let _145_575 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _145_573 -> FStar_Util.Inl (_145_573)))
in (FStar_All.pipe_right _145_575 (fun _145_574 -> Some (_145_574))))
in (FStar_Syntax_Util.abs binders _145_577 _145_576)))
end))
end)
end)))
in (match ((let _145_578 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_145_578), (t.FStar_Syntax_Syntax.n)))) with
| (Some (sort), _53_1453) -> begin
(let _145_579 = (mk sort t.FStar_Syntax_Syntax.pos)
in (expand _145_579))
end
| (_53_1456, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(expand x.FStar_Syntax_Syntax.sort)
end
| _53_1461 -> begin
(let _145_582 = (let _145_581 = (FStar_Syntax_Print.tag_of_term t)
in (let _145_580 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "NYI: eta_expand(%s) %s" _145_581 _145_580)))
in (FStar_All.failwith _145_582))
end)))





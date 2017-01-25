
open Prims
type step =
| Beta
| Iota
| Zeta
| Exclude of step
| WHNF
| Primops
| Eager_unfolding
| Inlining
| NoDeltaSteps
| UnfoldUntil of FStar_Syntax_Syntax.delta_depth
| PureSubtermsWithinComputations
| Simplify
| EraseUniverses
| AllowUnboundUniverses
| Reify
| CompressUvars
| NoFullNorm


let uu___is_Beta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Beta -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_Iota : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____14 -> begin
false
end))


let uu___is_Zeta : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Exclude : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
true
end
| uu____23 -> begin
false
end))


let __proj__Exclude__item___0 : step  ->  step = (fun projectee -> (match (projectee) with
| Exclude (_0) -> begin
_0
end))


let uu___is_WHNF : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| WHNF -> begin
true
end
| uu____34 -> begin
false
end))


let uu___is_Primops : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____38 -> begin
false
end))


let uu___is_Eager_unfolding : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding -> begin
true
end
| uu____42 -> begin
false
end))


let uu___is_Inlining : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____46 -> begin
false
end))


let uu___is_NoDeltaSteps : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDeltaSteps -> begin
true
end
| uu____50 -> begin
false
end))


let uu___is_UnfoldUntil : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
true
end
| uu____55 -> begin
false
end))


let __proj__UnfoldUntil__item___0 : step  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| UnfoldUntil (_0) -> begin
_0
end))


let uu___is_PureSubtermsWithinComputations : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PureSubtermsWithinComputations -> begin
true
end
| uu____66 -> begin
false
end))


let uu___is_Simplify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simplify -> begin
true
end
| uu____70 -> begin
false
end))


let uu___is_EraseUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EraseUniverses -> begin
true
end
| uu____74 -> begin
false
end))


let uu___is_AllowUnboundUniverses : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| AllowUnboundUniverses -> begin
true
end
| uu____78 -> begin
false
end))


let uu___is_Reify : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____82 -> begin
false
end))


let uu___is_CompressUvars : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CompressUvars -> begin
true
end
| uu____86 -> begin
false
end))


let uu___is_NoFullNorm : step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoFullNorm -> begin
true
end
| uu____90 -> begin
false
end))


type steps =
step Prims.list

type closure =
| Clos of (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool)
| Univ of FStar_Syntax_Syntax.universe
| Dummy


let uu___is_Clos : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
true
end
| uu____120 -> begin
false
end))


let __proj__Clos__item___0 : closure  ->  (closure Prims.list * FStar_Syntax_Syntax.term * (closure Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool) = (fun projectee -> (match (projectee) with
| Clos (_0) -> begin
_0
end))


let uu___is_Univ : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
true
end
| uu____159 -> begin
false
end))


let __proj__Univ__item___0 : closure  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| Univ (_0) -> begin
_0
end))


let uu___is_Dummy : closure  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Dummy -> begin
true
end
| uu____170 -> begin
false
end))


type env =
closure Prims.list


let closure_to_string : closure  ->  Prims.string = (fun uu___122_174 -> (match (uu___122_174) with
| Clos (uu____175, t, uu____177, uu____178) -> begin
(FStar_Syntax_Print.term_to_string t)
end
| Univ (uu____189) -> begin
"Univ"
end
| Dummy -> begin
"dummy"
end))

type cfg =
{steps : steps; tcenv : FStar_TypeChecker_Env.env; delta_level : FStar_TypeChecker_Env.delta_level Prims.list}


type branches =
(FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term Prims.option * FStar_Syntax_Syntax.term) Prims.list


type subst_t =
FStar_Syntax_Syntax.subst_elt Prims.list

type stack_elt =
| Arg of (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| UnivArgs of (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range)
| MemoLazy of (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo
| Match of (env * branches * FStar_Range.range)
| Abs of (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option * FStar_Range.range)
| App of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range)
| Meta of (FStar_Syntax_Syntax.metadata * FStar_Range.range)
| Let of (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range)
| Steps of (steps * FStar_TypeChecker_Env.delta_level Prims.list)
| Debug of FStar_Syntax_Syntax.term


let uu___is_Arg : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
true
end
| uu____290 -> begin
false
end))


let __proj__Arg__item___0 : stack_elt  ->  (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Arg (_0) -> begin
_0
end))


let uu___is_UnivArgs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
true
end
| uu____314 -> begin
false
end))


let __proj__UnivArgs__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range) = (fun projectee -> (match (projectee) with
| UnivArgs (_0) -> begin
_0
end))


let uu___is_MemoLazy : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
true
end
| uu____338 -> begin
false
end))


let __proj__MemoLazy__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo = (fun projectee -> (match (projectee) with
| MemoLazy (_0) -> begin
_0
end))


let uu___is_Match : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
true
end
| uu____365 -> begin
false
end))


let __proj__Match__item___0 : stack_elt  ->  (env * branches * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Match (_0) -> begin
_0
end))


let uu___is_Abs : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
true
end
| uu____394 -> begin
false
end))


let __proj__Abs__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * env * (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Abs (_0) -> begin
_0
end))


let uu___is_App : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| App (_0) -> begin
true
end
| uu____433 -> begin
false
end))


let __proj__App__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual * FStar_Range.range) = (fun projectee -> (match (projectee) with
| App (_0) -> begin
_0
end))


let uu___is_Meta : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
true
end
| uu____456 -> begin
false
end))


let __proj__Meta__item___0 : stack_elt  ->  (FStar_Syntax_Syntax.metadata * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Meta (_0) -> begin
_0
end))


let uu___is_Let : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
true
end
| uu____478 -> begin
false
end))


let __proj__Let__item___0 : stack_elt  ->  (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Let (_0) -> begin
_0
end))


let uu___is_Steps : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Steps (_0) -> begin
true
end
| uu____505 -> begin
false
end))


let __proj__Steps__item___0 : stack_elt  ->  (steps * FStar_TypeChecker_Env.delta_level Prims.list) = (fun projectee -> (match (projectee) with
| Steps (_0) -> begin
_0
end))


let uu___is_Debug : stack_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
true
end
| uu____526 -> begin
false
end))


let __proj__Debug__item___0 : stack_elt  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| Debug (_0) -> begin
_0
end))


type stack =
stack_elt Prims.list


let mk = (fun t r -> (FStar_Syntax_Syntax.mk t None r))


let set_memo = (fun r t -> (

let uu____574 = (FStar_ST.read r)
in (match (uu____574) with
| Some (uu____579) -> begin
(failwith "Unexpected set_memo: thunk already evaluated")
end
| None -> begin
(FStar_ST.write r (Some (t)))
end)))


let env_to_string : closure Prims.list  ->  Prims.string = (fun env -> (let _0_252 = (FStar_List.map closure_to_string env)
in (FStar_All.pipe_right _0_252 (FStar_String.concat "; "))))


let stack_elt_to_string : stack_elt  ->  Prims.string = (fun uu___123_591 -> (match (uu___123_591) with
| Arg (c, uu____593, uu____594) -> begin
(let _0_253 = (closure_to_string c)
in (FStar_Util.format1 "Closure %s" _0_253))
end
| MemoLazy (uu____595) -> begin
"MemoLazy"
end
| Abs (uu____599, bs, uu____601, uu____602, uu____603) -> begin
(let _0_254 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.format1 "Abs %s" _0_254))
end
| UnivArgs (uu____614) -> begin
"UnivArgs"
end
| Match (uu____618) -> begin
"Match"
end
| App (t, uu____623, uu____624) -> begin
(let _0_255 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "App %s" _0_255))
end
| Meta (m, uu____626) -> begin
"Meta"
end
| Let (uu____627) -> begin
"Let"
end
| Steps (s, uu____633) -> begin
"Steps"
end
| Debug (t) -> begin
(let _0_256 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Debug %s" _0_256))
end))


let stack_to_string : stack_elt Prims.list  ->  Prims.string = (fun s -> (let _0_257 = (FStar_List.map stack_elt_to_string s)
in (FStar_All.pipe_right _0_257 (FStar_String.concat "; "))))


let log : cfg  ->  (Prims.unit  ->  Prims.unit)  ->  Prims.unit = (fun cfg f -> (

let uu____654 = (FStar_TypeChecker_Env.debug cfg.tcenv (FStar_Options.Other ("Norm")))
in (match (uu____654) with
| true -> begin
(f ())
end
| uu____655 -> begin
()
end)))


let is_empty = (fun uu___124_663 -> (match (uu___124_663) with
| [] -> begin
true
end
| uu____665 -> begin
false
end))


let lookup_bvar = (fun env x -> try
(match (()) with
| () -> begin
(FStar_List.nth env x.FStar_Syntax_Syntax.index)
end)
with
| uu____683 -> begin
(failwith (let _0_258 = (FStar_Syntax_Print.db_to_string x)
in (FStar_Util.format1 "Failed to find %s\n" _0_258)))
end)


let comp_to_comp_typ : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, None) -> begin
(

let u = (env.FStar_TypeChecker_Env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (Some (u))))
end
| uu____705 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c)))


let rec unfold_effect_abbrev : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____713 = (FStar_TypeChecker_Env.lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____713) with
| None -> begin
c
end
| Some (binders, cdef) -> begin
(

let uu____723 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____723) with
| (binders, cdef) -> begin
((match (((FStar_List.length binders) <> ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((let _0_262 = (let _0_261 = (FStar_Util.string_of_int (FStar_List.length binders))
in (let _0_260 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (let _0_259 = (FStar_Syntax_Print.comp_to_string (FStar_Syntax_Syntax.mk_Comp c))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" _0_261 _0_260 _0_259))))
in ((_0_262), (comp.FStar_Syntax_Syntax.pos))))))
end
| uu____752 -> begin
()
end);
(

let inst = (let _0_264 = (let _0_263 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (_0_263)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____761 uu____762 -> (match (((uu____761), (uu____762))) with
| ((x, uu____776), (t, uu____778)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders _0_264))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst cdef)
in (

let c = (let _0_265 = (

let uu___134_793 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___134_793.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___134_793.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___134_793.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___134_793.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right _0_265 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c))));
)
end))
end))))


let downgrade_ghost_effect_name : FStar_Ident.lident  ->  FStar_Ident.lident Prims.option = (fun l -> (match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Ghost_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_Pure_lid)
end
| uu____799 -> begin
(match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_Tot_lid)
end
| uu____801 -> begin
(match ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GHOST_lid)) with
| true -> begin
Some (FStar_Syntax_Const.effect_PURE_lid)
end
| uu____803 -> begin
None
end)
end)
end))


let norm_universe : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun cfg env u -> (

let norm_univs = (fun us -> (

let us = (FStar_Util.sort_with FStar_Syntax_Util.compare_univs us)
in (

let uu____824 = (FStar_List.fold_left (fun uu____833 u -> (match (uu____833) with
| (cur_kernel, cur_max, out) -> begin
(

let uu____848 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____848) with
| (k_u, n) -> begin
(

let uu____857 = (FStar_Syntax_Util.eq_univs cur_kernel k_u)
in (match (uu____857) with
| true -> begin
((cur_kernel), (u), (out))
end
| uu____863 -> begin
((k_u), (u), ((cur_max)::out))
end))
end))
end)) ((FStar_Syntax_Syntax.U_zero), (FStar_Syntax_Syntax.U_zero), ([])) us)
in (match (uu____824) with
| (uu____867, u, out) -> begin
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
(

let uu____883 = (FStar_List.nth env x)
in (match (uu____883) with
| Univ (u) -> begin
(aux u)
end
| Dummy -> begin
(u)::[]
end
| uu____886 -> begin
(failwith "Impossible: universe variable bound to a term")
end))
end)
with
| uu____890 -> begin
(

let uu____891 = (FStar_All.pipe_right cfg.steps (FStar_List.contains AllowUnboundUniverses))
in (match (uu____891) with
| true -> begin
(FStar_Syntax_Syntax.U_unknown)::[]
end
| uu____893 -> begin
(failwith "Universe variable not found")
end))
end
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unif (_)) | (FStar_Syntax_Syntax.U_name (_)) | (FStar_Syntax_Syntax.U_unknown) -> begin
(u)::[]
end
| FStar_Syntax_Syntax.U_max ([]) -> begin
(FStar_Syntax_Syntax.U_zero)::[]
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let us = (let _0_266 = (FStar_List.collect aux us)
in (FStar_All.pipe_right _0_266 norm_univs))
in (match (us) with
| (u_k)::(hd)::rest -> begin
(

let rest = (hd)::rest
in (

let uu____910 = (FStar_Syntax_Util.univ_kernel u_k)
in (match (uu____910) with
| (FStar_Syntax_Syntax.U_zero, n) -> begin
(

let uu____915 = (FStar_All.pipe_right rest (FStar_List.for_all (fun u -> (

let uu____918 = (FStar_Syntax_Util.univ_kernel u)
in (match (uu____918) with
| (uu____921, m) -> begin
(n <= m)
end)))))
in (match (uu____915) with
| true -> begin
rest
end
| uu____924 -> begin
us
end))
end
| uu____925 -> begin
us
end)))
end
| uu____928 -> begin
us
end))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _0_268 = (aux u)
in (FStar_List.map (fun _0_267 -> FStar_Syntax_Syntax.U_succ (_0_267)) _0_268))
end)))
in (

let uu____931 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____931) with
| true -> begin
FStar_Syntax_Syntax.U_unknown
end
| uu____932 -> begin
(

let uu____933 = (aux u)
in (match (uu____933) with
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
end))
end)))))


let rec closure_as_term : cfg  ->  closure Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env t -> ((log cfg (fun uu____1030 -> (let _0_270 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_269 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> %s Closure_as_term %s\n" _0_270 _0_269)))));
(match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____1031 -> begin
(

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1034) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) -> begin
t
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1058) -> begin
t
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _0_271 = FStar_Syntax_Syntax.Tm_type ((norm_universe cfg env u))
in (mk _0_271 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(let _0_272 = (FStar_List.map (norm_universe cfg env) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t _0_272))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1075 = (lookup_bvar env x)
in (match (uu____1075) with
| Univ (uu____1076) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
t
end
| Clos (env, t0, r, uu____1080) -> begin
(closure_as_term cfg env t0)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (closure_as_term_delayed cfg env head)
in (

let args = (closures_as_args_delayed cfg env args)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))) t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____1148 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1148) with
| (bs, env) -> begin
(

let body = (closure_as_term_delayed cfg env body)
in (let _0_274 = FStar_Syntax_Syntax.Tm_abs ((let _0_273 = (close_lcomp_opt cfg env lopt)
in ((bs), (body), (_0_273))))
in (mk _0_274 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1191 = (closures_as_binders_delayed cfg env bs)
in (match (uu____1191) with
| (bs, env) -> begin
(

let c = (close_comp cfg env c)
in (mk (FStar_Syntax_Syntax.Tm_arrow (((bs), (c)))) t.FStar_Syntax_Syntax.pos))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____1222 = (let _0_276 = (let _0_275 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_275)::[])
in (closures_as_binders_delayed cfg env _0_276))
in (match (uu____1222) with
| (x, env) -> begin
(

let phi = (closure_as_term_delayed cfg env phi)
in (let _0_279 = FStar_Syntax_Syntax.Tm_refine ((let _0_278 = (let _0_277 = (FStar_List.hd x)
in (FStar_All.pipe_right _0_277 Prims.fst))
in ((_0_278), (phi))))
in (mk _0_279 t.FStar_Syntax_Syntax.pos)))
end))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inl (t2), lopt) -> begin
(let _0_284 = FStar_Syntax_Syntax.Tm_ascribed ((let _0_283 = (closure_as_term_delayed cfg env t1)
in (let _0_282 = (let _0_281 = (closure_as_term_delayed cfg env t2)
in (FStar_All.pipe_left (fun _0_280 -> FStar_Util.Inl (_0_280)) _0_281))
in ((_0_283), (_0_282), (lopt)))))
in (mk _0_284 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, FStar_Util.Inr (c), lopt) -> begin
(let _0_289 = FStar_Syntax_Syntax.Tm_ascribed ((let _0_288 = (closure_as_term_delayed cfg env t1)
in (let _0_287 = (let _0_286 = (close_comp cfg env c)
in (FStar_All.pipe_left (fun _0_285 -> FStar_Util.Inr (_0_285)) _0_286))
in ((_0_288), (_0_287), (lopt)))))
in (mk _0_289 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_pattern (args)) -> begin
(let _0_292 = FStar_Syntax_Syntax.Tm_meta ((let _0_291 = (closure_as_term_delayed cfg env t')
in (let _0_290 = FStar_Syntax_Syntax.Meta_pattern ((FStar_All.pipe_right args (FStar_List.map (closures_as_args_delayed cfg env))))
in ((_0_291), (_0_290)))))
in (mk _0_292 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic (m, tbody)) -> begin
(let _0_296 = FStar_Syntax_Syntax.Tm_meta ((let _0_295 = (closure_as_term_delayed cfg env t')
in (let _0_294 = FStar_Syntax_Syntax.Meta_monadic ((let _0_293 = (closure_as_term_delayed cfg env tbody)
in ((m), (_0_293))))
in ((_0_295), (_0_294)))))
in (mk _0_296 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, tbody)) -> begin
(let _0_300 = FStar_Syntax_Syntax.Tm_meta ((let _0_299 = (closure_as_term_delayed cfg env t')
in (let _0_298 = FStar_Syntax_Syntax.Meta_monadic_lift ((let _0_297 = (closure_as_term_delayed cfg env tbody)
in ((m1), (m2), (_0_297))))
in ((_0_299), (_0_298)))))
in (mk _0_300 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t', m) -> begin
(let _0_302 = FStar_Syntax_Syntax.Tm_meta ((let _0_301 = (closure_as_term_delayed cfg env t')
in ((_0_301), (m))))
in (mk _0_302 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let env0 = env
in (

let env = (FStar_List.fold_left (fun env uu____1423 -> (Dummy)::env) env lb.FStar_Syntax_Syntax.lbunivs)
in (

let typ = (closure_as_term_delayed cfg env lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____1434) -> begin
body
end
| FStar_Util.Inl (uu____1435) -> begin
(closure_as_term cfg ((Dummy)::env0) body)
end)
in (

let lb = (

let uu___137_1437 = lb
in {FStar_Syntax_Syntax.lbname = uu___137_1437.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___137_1437.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___137_1437.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = def})
in (mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) t.FStar_Syntax_Syntax.pos)))))))
end
| FStar_Syntax_Syntax.Tm_let ((uu____1444, lbs), body) -> begin
(

let norm_one_lb = (fun env lb -> (

let env_univs = (FStar_List.fold_right (fun uu____1468 env -> (Dummy)::env) lb.FStar_Syntax_Syntax.lbunivs env)
in (

let env = (

let uu____1473 = (FStar_Syntax_Syntax.is_top_level lbs)
in (match (uu____1473) with
| true -> begin
env_univs
end
| uu____1475 -> begin
(FStar_List.fold_right (fun uu____1477 env -> (Dummy)::env) lbs env_univs)
end))
in (

let uu___138_1480 = lb
in (let _0_304 = (closure_as_term cfg env_univs lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_303 = (closure_as_term cfg env lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___138_1480.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___138_1480.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_304; FStar_Syntax_Syntax.lbeff = uu___138_1480.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_303}))))))
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (norm_one_lb env)))
in (

let body = (

let body_env = (FStar_List.fold_right (fun uu____1489 env -> (Dummy)::env) lbs env)
in (closure_as_term cfg body_env body))
in (mk (FStar_Syntax_Syntax.Tm_let (((((true), (lbs))), (body)))) t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let head = (closure_as_term cfg env head)
in (

let norm_one_branch = (fun env uu____1544 -> (match (uu____1544) with
| (pat, w_opt, tm) -> begin
(

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____1590) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let uu____1610 = (norm_pat env hd)
in (match (uu____1610) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (Prims.fst (norm_pat env p)))))
in (((

let uu___139_1652 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = uu___139_1652.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___139_1652.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____1669 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____1703 uu____1704 -> (match (((uu____1703), (uu____1704))) with
| ((pats, env), (p, b)) -> begin
(

let uu____1769 = (norm_pat env p)
in (match (uu____1769) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (uu____1669) with
| (pats, env) -> begin
(((

let uu___140_1835 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___140_1835.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___140_1835.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___141_1849 = x
in (let _0_305 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___141_1849.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___141_1849.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_305}))
in (((

let uu___142_1853 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___142_1853.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___142_1853.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___143_1858 = x
in (let _0_306 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___143_1858.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___143_1858.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_306}))
in (((

let uu___144_1862 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___144_1862.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___144_1862.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let uu___145_1872 = x
in (let _0_307 = (closure_as_term cfg env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___145_1872.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_1872.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_307}))
in (

let t = (closure_as_term cfg env t)
in (((

let uu___146_1877 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = uu___146_1877.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___146_1877.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let uu____1880 = (norm_pat env pat)
in (match (uu____1880) with
| (pat, env) -> begin
(

let w_opt = (match (w_opt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((closure_as_term cfg env w))
end)
in (

let tm = (closure_as_term cfg env tm)
in ((pat), (w_opt), (tm))))
end)))
end))
in (let _0_309 = FStar_Syntax_Syntax.Tm_match ((let _0_308 = (FStar_All.pipe_right branches (FStar_List.map (norm_one_branch env)))
in ((head), (_0_308))))
in (mk _0_309 t.FStar_Syntax_Syntax.pos))))
end))
end);
))
and closure_as_term_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun cfg env t -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
t
end
| uu____1953 -> begin
(closure_as_term cfg env t)
end))
and closures_as_args_delayed : cfg  ->  closure Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list = (fun cfg env args -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
args
end
| uu____1969 -> begin
(FStar_List.map (fun uu____1979 -> (match (uu____1979) with
| (x, imp) -> begin
(let _0_310 = (closure_as_term_delayed cfg env x)
in ((_0_310), (imp)))
end)) args)
end))
and closures_as_binders_delayed : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list * closure Prims.list) = (fun cfg env bs -> (

let uu____2003 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2027 uu____2028 -> (match (((uu____2027), (uu____2028))) with
| ((env, out), (b, imp)) -> begin
(

let b = (

let uu___147_2072 = b
in (let _0_311 = (closure_as_term_delayed cfg env b.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___147_2072.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___147_2072.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_311}))
in (

let env = (Dummy)::env
in ((env), ((((b), (imp)))::out))))
end)) ((env), ([]))))
in (match (uu____2003) with
| (env, bs) -> begin
(((FStar_List.rev bs)), (env))
end)))
and close_comp : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (match (env) with
| [] when (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains CompressUvars cfg.steps)) -> begin
c
end
| uu____2117 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(let _0_313 = (closure_as_term_delayed cfg env t)
in (let _0_312 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_Total' _0_313 _0_312)))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(let _0_315 = (closure_as_term_delayed cfg env t)
in (let _0_314 = (FStar_Option.map (norm_universe cfg env) uopt)
in (FStar_Syntax_Syntax.mk_GTotal' _0_315 _0_314)))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let rt = (closure_as_term_delayed cfg env c.FStar_Syntax_Syntax.result_typ)
in (

let args = (closures_as_args_delayed cfg env c.FStar_Syntax_Syntax.effect_args)
in (

let flags = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___125_2151 -> (match (uu___125_2151) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
FStar_Syntax_Syntax.DECREASES ((closure_as_term_delayed cfg env t))
end
| f -> begin
f
end))))
in (FStar_Syntax_Syntax.mk_Comp (

let uu___148_2156 = c
in (let _0_316 = (FStar_List.map (norm_universe cfg env) c.FStar_Syntax_Syntax.comp_univs)
in {FStar_Syntax_Syntax.comp_univs = _0_316; FStar_Syntax_Syntax.effect_name = uu___148_2156.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = rt; FStar_Syntax_Syntax.effect_args = args; FStar_Syntax_Syntax.flags = flags}))))))
end)
end))
and filter_out_lcomp_cflags : FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun lc -> (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags (FStar_List.filter (fun uu___126_2160 -> (match (uu___126_2160) with
| FStar_Syntax_Syntax.DECREASES (uu____2161) -> begin
false
end
| uu____2164 -> begin
true
end)))))
and close_lcomp_opt : cfg  ->  closure Prims.list  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, (FStar_Ident.lident * FStar_Syntax_Syntax.cflags Prims.list)) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____2192 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____2192) with
| true -> begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), (flags))))
end
| uu____2208 -> begin
(

let uu____2209 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____2209) with
| true -> begin
Some (FStar_Util.Inr (((FStar_Syntax_Const.effect_GTot_lid), (flags))))
end
| uu____2225 -> begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end))
end)))
end
| uu____2235 -> begin
lopt
end))


let arith_ops : (FStar_Ident.lident * (Prims.int  ->  Prims.int  ->  FStar_Const.sconst)) Prims.list = (

let int_as_const = (fun i -> FStar_Const.Const_int ((let _0_317 = (FStar_Util.string_of_int i)
in ((_0_317), (None)))))
in (

let bool_as_const = (fun b -> FStar_Const.Const_bool (b))
in (let _0_326 = (FStar_List.flatten (FStar_List.map (fun m -> (let _0_325 = (let _0_318 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("add")::[]))
in ((_0_318), ((fun x y -> (int_as_const (x + y))))))
in (let _0_324 = (let _0_323 = (let _0_319 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("sub")::[]))
in ((_0_319), ((fun x y -> (int_as_const (x - y))))))
in (let _0_322 = (let _0_321 = (let _0_320 = (FStar_Syntax_Const.p2l (("FStar")::(m)::("mul")::[]))
in ((_0_320), ((fun x y -> (int_as_const (x * y))))))
in (_0_321)::[])
in (_0_323)::_0_322))
in (_0_325)::_0_324))) (("Int8")::("UInt8")::("Int16")::("UInt16")::("Int32")::("UInt32")::("Int64")::("UInt64")::("UInt128")::[])))
in (FStar_List.append ((((FStar_Syntax_Const.op_Addition), ((fun x y -> (int_as_const (x + y))))))::(((FStar_Syntax_Const.op_Subtraction), ((fun x y -> (int_as_const (x - y))))))::(((FStar_Syntax_Const.op_Multiply), ((fun x y -> (int_as_const (x * y))))))::(((FStar_Syntax_Const.op_Division), ((fun x y -> (int_as_const (x / y))))))::(((FStar_Syntax_Const.op_LT), ((fun x y -> (bool_as_const (x < y))))))::(((FStar_Syntax_Const.op_LTE), ((fun x y -> (bool_as_const (x <= y))))))::(((FStar_Syntax_Const.op_GT), ((fun x y -> (bool_as_const (x > y))))))::(((FStar_Syntax_Const.op_GTE), ((fun x y -> (bool_as_const (x >= y))))))::(((FStar_Syntax_Const.op_Modulus), ((fun x y -> (int_as_const (x mod y))))))::[]) _0_326))))


let un_ops : (FStar_Ident.lident * (Prims.string  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)) Prims.list = (

let mk = (fun x -> (mk x FStar_Range.dummyRange))
in (

let name = (fun x -> (mk (FStar_Syntax_Syntax.Tm_fvar ((let _0_327 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _0_327 FStar_Syntax_Syntax.Delta_constant None))))))
in (

let ctor = (fun x -> (mk (FStar_Syntax_Syntax.Tm_fvar ((let _0_328 = (FStar_Syntax_Const.p2l x)
in (FStar_Syntax_Syntax.lid_as_fv _0_328 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))))))
in (let _0_345 = (let _0_344 = (FStar_Syntax_Const.p2l (("FStar")::("String")::("list_of_string")::[]))
in ((_0_344), ((fun s -> (let _0_343 = (FStar_String.list_of_string s)
in (let _0_342 = (mk (FStar_Syntax_Syntax.Tm_app ((let _0_341 = (let _0_337 = (ctor (("Prims")::("Nil")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_337 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _0_340 = (let _0_339 = (let _0_338 = (name (("FStar")::("Char")::("char")::[]))
in ((_0_338), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (_0_339)::[])
in ((_0_341), (_0_340)))))))
in (FStar_List.fold_right (fun c a -> (mk (FStar_Syntax_Syntax.Tm_app ((let _0_336 = (let _0_329 = (ctor (("Prims")::("Cons")::[]))
in (FStar_Syntax_Syntax.mk_Tm_uinst _0_329 ((FStar_Syntax_Syntax.U_zero)::[])))
in (let _0_335 = (let _0_334 = (let _0_330 = (name (("FStar")::("Char")::("char")::[]))
in ((_0_330), (Some (FStar_Syntax_Syntax.Implicit (true)))))
in (let _0_333 = (let _0_332 = (let _0_331 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c))))
in ((_0_331), (None)))
in (_0_332)::(((a), (None)))::[])
in (_0_334)::_0_333))
in ((_0_336), (_0_335)))))))) _0_343 _0_342)))))))
in (_0_345)::[]))))


let reduce_equality : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun tm -> (

let is_decidable_equality = (fun t -> (

let uu____2574 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
in (match (uu____2574) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Eq)
end
| uu____2576 -> begin
false
end)))
in (

let is_propositional_equality = (fun t -> (

let uu____2581 = (FStar_Syntax_Util.un_uinst t).FStar_Syntax_Syntax.n
in (match (uu____2581) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.eq2_lid)
end
| uu____2583 -> begin
false
end)))
in (match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (op_eq_inst, ((_typ, uu____2588))::((a1, uu____2590))::((a2, uu____2592))::[]) when (is_decidable_equality op_eq_inst) -> begin
(

let tt = (

let uu____2633 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____2633) with
| FStar_Syntax_Util.Equal -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))) tm.FStar_Syntax_Syntax.pos)
end
| FStar_Syntax_Util.NotEqual -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))) tm.FStar_Syntax_Syntax.pos)
end
| uu____2636 -> begin
tm
end))
in tt)
end
| (FStar_Syntax_Syntax.Tm_app (eq2_inst, (_)::((a1, _))::((a2, _))::[])) | (FStar_Syntax_Syntax.Tm_app (eq2_inst, ((a1, _))::((a2, _))::[])) when (is_propositional_equality eq2_inst) -> begin
(

let tt = (

let uu____2708 = (FStar_Syntax_Util.eq_tm a1 a2)
in (match (uu____2708) with
| FStar_Syntax_Util.Equal -> begin
FStar_Syntax_Util.t_true
end
| FStar_Syntax_Util.NotEqual -> begin
FStar_Syntax_Util.t_false
end
| uu____2709 -> begin
tm
end))
in tt)
end
| uu____2710 -> begin
tm
end))))


let find_fv = (fun fv ops -> (match (fv.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_List.tryFind (fun uu____2738 -> (match (uu____2738) with
| (l, uu____2742) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv l)
end)) ops)
end
| uu____2743 -> begin
None
end))


let reduce_primops : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let uu____2760 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Primops steps))
in (match (uu____2760) with
| true -> begin
tm
end
| uu____2763 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, uu____2768))::((a2, uu____2770))::[]) -> begin
(

let uu____2800 = (find_fv fv arith_ops)
in (match (uu____2800) with
| None -> begin
tm
end
| Some (uu____2820, op) -> begin
(

let norm = (fun i j -> (

let c = (let _0_347 = (FStar_Util.int_of_string i)
in (let _0_346 = (FStar_Util.int_of_string j)
in (op _0_347 _0_346)))
in (mk (FStar_Syntax_Syntax.Tm_constant (c)) tm.FStar_Syntax_Syntax.pos)))
in (

let uu____2846 = (let _0_349 = (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
in (let _0_348 = (FStar_Syntax_Subst.compress a2).FStar_Syntax_Syntax.n
in ((_0_349), (_0_348))))
in (match (uu____2846) with
| (FStar_Syntax_Syntax.Tm_app (head1, ((arg1, uu____2853))::[]), FStar_Syntax_Syntax.Tm_app (head2, ((arg2, uu____2856))::[])) -> begin
(

let uu____2899 = (let _0_353 = (FStar_Syntax_Subst.compress head1).FStar_Syntax_Syntax.n
in (let _0_352 = (FStar_Syntax_Subst.compress head2).FStar_Syntax_Syntax.n
in (let _0_351 = (FStar_Syntax_Subst.compress arg1).FStar_Syntax_Syntax.n
in (let _0_350 = (FStar_Syntax_Subst.compress arg2).FStar_Syntax_Syntax.n
in ((_0_353), (_0_352), (_0_351), (_0_350))))))
in (match (uu____2899) with
| (FStar_Syntax_Syntax.Tm_fvar (fv1), FStar_Syntax_Syntax.Tm_fvar (fv2), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) when ((FStar_Util.ends_with (FStar_Ident.text_of_lid fv1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t") && (FStar_Util.ends_with (FStar_Ident.text_of_lid fv2.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) "int_to_t")) -> begin
(let _0_357 = (mk (FStar_Syntax_Syntax.Tm_fvar (fv1)) tm.FStar_Syntax_Syntax.pos)
in (let _0_356 = (let _0_355 = (let _0_354 = (norm i j)
in ((_0_354), (None)))
in (_0_355)::[])
in (FStar_Syntax_Util.mk_app _0_357 _0_356)))
end
| uu____2941 -> begin
tm
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (i, None)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (j, None))) -> begin
(norm i j)
end
| uu____2958 -> begin
tm
end)))
end))
end
| FStar_Syntax_Syntax.Tm_app (fv, ((a1, uu____2963))::[]) -> begin
(

let uu____2985 = (find_fv fv un_ops)
in (match (uu____2985) with
| None -> begin
tm
end
| Some (uu____3005, op) -> begin
(

let uu____3021 = (FStar_Syntax_Subst.compress a1).FStar_Syntax_Syntax.n
in (match (uu____3021) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (b, uu____3025)) -> begin
(op (FStar_Bytes.unicode_bytes_as_string b))
end
| uu____3028 -> begin
tm
end))
end))
end
| uu____3029 -> begin
(reduce_equality tm)
end)
end)))


let maybe_simplify : step Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun steps tm -> (

let w = (fun t -> (

let uu___149_3054 = t
in {FStar_Syntax_Syntax.n = uu___149_3054.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___149_3054.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = tm.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___149_3054.FStar_Syntax_Syntax.vars}))
in (

let simp_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.true_lid) -> begin
Some (true)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.false_lid) -> begin
Some (false)
end
| uu____3073 -> begin
None
end))
in (

let simplify = (fun arg -> (((simp_t (Prims.fst arg))), (arg)))
in (

let uu____3100 = (FStar_All.pipe_left Prims.op_Negation (FStar_List.contains Simplify steps))
in (match (uu____3100) with
| true -> begin
(reduce_primops steps tm)
end
| uu____3103 -> begin
(match (tm.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, args)) -> begin
(

let uu____3144 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.and_lid)
in (match (uu____3144) with
| true -> begin
(

let uu____3147 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3147) with
| (((Some (true), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (true), _))::[]) -> begin
arg
end
| (((Some (false), _))::(_)::[]) | ((_)::((Some (false), _))::[]) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____3315 -> begin
tm
end))
end
| uu____3324 -> begin
(

let uu____3325 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.or_lid)
in (match (uu____3325) with
| true -> begin
(

let uu____3328 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3328) with
| (((Some (true), _))::(_)::[]) | ((_)::((Some (true), _))::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| (((Some (false), _))::((_, (arg, _)))::[]) | (((_, (arg, _)))::((Some (false), _))::[]) -> begin
arg
end
| uu____3496 -> begin
tm
end))
end
| uu____3505 -> begin
(

let uu____3506 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.imp_lid)
in (match (uu____3506) with
| true -> begin
(

let uu____3509 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3509) with
| ((_)::((Some (true), _))::[]) | (((Some (false), _))::(_)::[]) -> begin
(w FStar_Syntax_Util.t_true)
end
| ((Some (true), uu____3600))::((uu____3601, (arg, uu____3603)))::[] -> begin
arg
end
| uu____3644 -> begin
tm
end))
end
| uu____3653 -> begin
(

let uu____3654 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.not_lid)
in (match (uu____3654) with
| true -> begin
(

let uu____3657 = (FStar_All.pipe_right args (FStar_List.map simplify))
in (match (uu____3657) with
| ((Some (true), uu____3692))::[] -> begin
(w FStar_Syntax_Util.t_false)
end
| ((Some (false), uu____3716))::[] -> begin
(w FStar_Syntax_Util.t_true)
end
| uu____3740 -> begin
tm
end))
end
| uu____3749 -> begin
(

let uu____3750 = ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.exists_lid))
in (match (uu____3750) with
| true -> begin
(match (args) with
| (((t, _))::[]) | (((_, Some (FStar_Syntax_Syntax.Implicit (_))))::((t, _))::[]) -> begin
(

let uu____3795 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____3795) with
| FStar_Syntax_Syntax.Tm_abs ((uu____3798)::[], body, uu____3800) -> begin
(match ((simp_t body)) with
| Some (true) -> begin
(w FStar_Syntax_Util.t_true)
end
| Some (false) -> begin
(w FStar_Syntax_Util.t_false)
end
| uu____3828 -> begin
tm
end)
end
| uu____3830 -> begin
tm
end))
end
| uu____3831 -> begin
tm
end)
end
| uu____3837 -> begin
(reduce_equality tm)
end))
end))
end))
end))
end))
end
| uu____3838 -> begin
tm
end)
end))))))


let is_norm_request = (fun hd args -> (

let uu____3853 = (let _0_358 = (FStar_Syntax_Util.un_uinst hd).FStar_Syntax_Syntax.n
in ((_0_358), (args)))
in (match (uu____3853) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3859)::(uu____3860)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize_term)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3863)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.normalize)
end
| uu____3865 -> begin
false
end)))


let get_norm_request = (fun args -> (match (args) with
| ((_)::((tm, _))::[]) | (((tm, _))::[]) -> begin
tm
end
| uu____3898 -> begin
(failwith "Impossible")
end))


let rec norm : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (

let t = (FStar_Syntax_Subst.compress t)
in ((log cfg (fun uu____3994 -> (let _0_361 = (FStar_Syntax_Print.tag_of_term t)
in (let _0_360 = (FStar_Syntax_Print.term_to_string t)
in (let _0_359 = (stack_to_string stack)
in (FStar_Util.print3 ">>> %s\nNorm %s with top of the stack %s \n" _0_361 _0_360 _0_359))))));
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3995) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_constant; FStar_Syntax_Syntax.fv_qual = _})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_app (hd, args) when (((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoFullNorm)))) && (is_norm_request hd args)) && (not ((FStar_Ident.lid_equals cfg.tcenv.FStar_TypeChecker_Env.curmodule FStar_Syntax_Const.prims_lid)))) -> begin
(

let tm = (get_norm_request args)
in (

let s = (Reify)::(Beta)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(Zeta)::(Iota)::(Primops)::[]
in (

let cfg' = (

let uu___150_4054 = cfg
in {steps = s; tcenv = uu___150_4054.tcenv; delta_level = (FStar_TypeChecker_Env.Unfold (FStar_Syntax_Syntax.Delta_constant))::[]})
in (

let stack' = (Debug (t))::(Steps (((cfg.steps), (cfg.delta_level))))::stack
in (norm cfg' env stack' tm)))))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____4058; FStar_Syntax_Syntax.pos = uu____4059; FStar_Syntax_Syntax.vars = uu____4060}, (a1)::(a2)::rest) -> begin
(

let uu____4094 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4094) with
| (hd, uu____4105) -> begin
(

let t' = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((hd), ((a1)::[])))) None t.FStar_Syntax_Syntax.pos)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (((t'), ((a2)::rest)))) None t.FStar_Syntax_Syntax.pos)
in (norm cfg env stack t)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____4160; FStar_Syntax_Syntax.pos = uu____4161; FStar_Syntax_Syntax.vars = uu____4162}, (a)::[]) when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(

let uu____4185 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4185) with
| (reify_head, uu____4196) -> begin
(

let a = (FStar_Syntax_Subst.compress (FStar_All.pipe_left FStar_Syntax_Util.unascribe (Prims.fst a)))
in (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____4214)); FStar_Syntax_Syntax.tk = uu____4215; FStar_Syntax_Syntax.pos = uu____4216; FStar_Syntax_Syntax.vars = uu____4217}, (a)::[]) -> begin
(norm cfg env stack (Prims.fst a))
end
| uu____4242 -> begin
(

let stack = (App (((reify_head), (None), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack a))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let u = (norm_universe cfg env u)
in (let _0_362 = (mk (FStar_Syntax_Syntax.Tm_type (u)) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _0_362)))
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let uu____4256 = (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses))
in (match (uu____4256) with
| true -> begin
(norm cfg env stack t')
end
| uu____4257 -> begin
(

let us = UnivArgs ((let _0_363 = (FStar_List.map (norm_universe cfg env) us)
in ((_0_363), (t.FStar_Syntax_Syntax.pos))))
in (

let stack = (us)::stack
in (norm cfg env stack t')))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(

let t0 = t
in (

let should_delta = (FStar_All.pipe_right cfg.delta_level (FStar_Util.for_some (fun uu___127_4266 -> (match (uu___127_4266) with
| FStar_TypeChecker_Env.NoDelta -> begin
false
end
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| FStar_TypeChecker_Env.Unfold (l) -> begin
(FStar_TypeChecker_Common.delta_depth_greater_than f.FStar_Syntax_Syntax.fv_delta l)
end))))
in (match ((not (should_delta))) with
| true -> begin
(rebuild cfg env stack t)
end
| uu____4268 -> begin
(

let r_env = (let _0_364 = (FStar_Syntax_Syntax.range_of_fv f)
in (FStar_TypeChecker_Env.set_range cfg.tcenv _0_364))
in (

let uu____4270 = (FStar_TypeChecker_Env.lookup_definition cfg.delta_level r_env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4270) with
| None -> begin
((log cfg (fun uu____4281 -> (FStar_Util.print "Tm_fvar case 2\n" [])));
(rebuild cfg env stack t);
)
end
| Some (us, t) -> begin
((log cfg (fun uu____4287 -> (let _0_366 = (FStar_Syntax_Print.term_to_string t0)
in (let _0_365 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 ">>> Unfolded %s to %s\n" _0_366 _0_365)))));
(

let n = (FStar_List.length us)
in (match ((n > (Prims.parse_int "0"))) with
| true -> begin
(match (stack) with
| (UnivArgs (us', uu____4294))::stack -> begin
(

let env = (FStar_All.pipe_right us' (FStar_List.fold_left (fun env u -> (Univ (u))::env) env))
in (norm cfg env stack t))
end
| uu____4307 when (FStar_All.pipe_right cfg.steps (FStar_List.contains EraseUniverses)) -> begin
(norm cfg env stack t)
end
| uu____4308 -> begin
(failwith (let _0_367 = (FStar_Syntax_Print.lid_to_string f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Impossible: missing universe instantiation on %s" _0_367)))
end)
end
| uu____4313 -> begin
(norm cfg env stack t)
end));
)
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____4315 = (lookup_bvar env x)
in (match (uu____4315) with
| Univ (uu____4316) -> begin
(failwith "Impossible: term variable is bound to a universe")
end
| Dummy -> begin
(failwith "Term variable not found")
end
| Clos (env, t0, r, fix) -> begin
(match (((not (fix)) || (not ((FStar_List.contains (Exclude (Zeta)) cfg.steps))))) with
| true -> begin
(

let uu____4331 = (FStar_ST.read r)
in (match (uu____4331) with
| Some (env, t') -> begin
((log cfg (fun uu____4350 -> (let _0_369 = (FStar_Syntax_Print.term_to_string t)
in (let _0_368 = (FStar_Syntax_Print.term_to_string t')
in (FStar_Util.print2 "Lazy hit: %s cached to %s\n" _0_369 _0_368)))));
(

let uu____4351 = (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n
in (match (uu____4351) with
| FStar_Syntax_Syntax.Tm_abs (uu____4352) -> begin
(norm cfg env stack t')
end
| uu____4367 -> begin
(rebuild cfg env stack t')
end));
)
end
| None -> begin
(norm cfg env ((MemoLazy (r))::stack) t0)
end))
end
| uu____4374 -> begin
(norm cfg env stack t0)
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(match (stack) with
| (UnivArgs (uu____4400))::uu____4401 -> begin
(failwith "Ill-typed term: universes cannot be applied to term abstraction")
end
| (Match (uu____4406))::uu____4407 -> begin
(failwith "Ill-typed term: cannot pattern match an abstraction")
end
| (Arg (c, uu____4413, uu____4414))::stack_rest -> begin
(match (c) with
| Univ (uu____4417) -> begin
(norm cfg ((c)::env) stack_rest t)
end
| uu____4418 -> begin
(match (bs) with
| [] -> begin
(failwith "Impossible")
end
| (uu____4421)::[] -> begin
(match (lopt) with
| None when (FStar_Options.__unit_tests ()) -> begin
((log cfg (fun uu____4434 -> (let _0_370 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _0_370))));
(norm cfg ((c)::env) stack_rest body);
)
end
| Some (FStar_Util.Inr (l, cflags)) when (((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_All.pipe_right cflags (FStar_Util.for_some (fun uu___128_4448 -> (match (uu___128_4448) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____4449 -> begin
false
end))))) -> begin
((log cfg (fun uu____4451 -> (let _0_371 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _0_371))));
(norm cfg ((c)::env) stack_rest body);
)
end
| Some (FStar_Util.Inl (lc)) when (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) -> begin
((log cfg (fun uu____4462 -> (let _0_372 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _0_372))));
(norm cfg ((c)::env) stack_rest body);
)
end
| uu____4463 when (FStar_All.pipe_right cfg.steps (FStar_List.contains Reify)) -> begin
(norm cfg ((c)::env) stack_rest body)
end
| uu____4470 -> begin
(

let cfg = (

let uu___151_4478 = cfg
in {steps = (WHNF)::(Exclude (Iota))::(Exclude (Zeta))::cfg.steps; tcenv = uu___151_4478.tcenv; delta_level = uu___151_4478.delta_level})
in (let _0_373 = (closure_as_term cfg env t)
in (rebuild cfg env stack _0_373)))
end)
end
| (uu____4479)::tl -> begin
((log cfg (fun uu____4489 -> (let _0_374 = (closure_to_string c)
in (FStar_Util.print1 "\tShifted %s\n" _0_374))));
(

let body = (mk (FStar_Syntax_Syntax.Tm_abs (((tl), (body), (lopt)))) t.FStar_Syntax_Syntax.pos)
in (norm cfg ((c)::env) stack_rest body));
)
end)
end)
end
| (Steps (s, dl))::stack -> begin
(norm (

let uu___152_4510 = cfg
in {steps = s; tcenv = uu___152_4510.tcenv; delta_level = dl}) env stack t)
end
| (MemoLazy (r))::stack -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____4523 -> (let _0_375 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _0_375))));
(norm cfg env stack t);
)
end
| ((Debug (_))::_) | ((Meta (_))::_) | ((Let (_))::_) | ((App (_))::_) | ((Abs (_))::_) | ([]) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(let _0_376 = (closure_as_term cfg env t)
in (rebuild cfg env stack _0_376))
end
| uu____4534 -> begin
(

let uu____4535 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____4535) with
| (bs, body, opening) -> begin
(

let lopt = (match (lopt) with
| Some (FStar_Util.Inl (l)) -> begin
(let _0_382 = (let _0_380 = (let _0_378 = (let _0_377 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _0_377))
in (FStar_All.pipe_right _0_378 FStar_Syntax_Util.lcomp_of_comp))
in (FStar_All.pipe_right _0_380 (fun _0_379 -> FStar_Util.Inl (_0_379))))
in (FStar_All.pipe_right _0_382 (fun _0_381 -> Some (_0_381))))
end
| uu____4588 -> begin
lopt
end)
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____4602 -> (Dummy)::env) env))
in ((log cfg (fun uu____4607 -> (let _0_383 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs))
in (FStar_Util.print1 "\tShifted %s dummies\n" _0_383))));
(norm cfg env' ((Abs (((env), (bs), (env'), (lopt), (t.FStar_Syntax_Syntax.pos))))::stack) body);
)))
end))
end)
end)
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let stack = (FStar_All.pipe_right stack (FStar_List.fold_right (fun uu____4641 stack -> (match (uu____4641) with
| (a, aq) -> begin
(let _0_386 = Arg ((let _0_385 = Clos ((let _0_384 = (FStar_Util.mk_ref None)
in ((env), (a), (_0_384), (false))))
in ((_0_385), (aq), (t.FStar_Syntax_Syntax.pos))))
in (_0_386)::stack)
end)) args))
in ((log cfg (fun uu____4664 -> (let _0_387 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args))
in (FStar_Util.print1 "\tPushed %s arguments\n" _0_387))));
(norm cfg env stack head);
))
end
| FStar_Syntax_Syntax.Tm_refine (x, f) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(match (((env), (stack))) with
| ([], []) -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_refine ((((

let uu___153_4685 = x
in {FStar_Syntax_Syntax.ppname = uu___153_4685.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___153_4685.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (f)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t)))
end
| uu____4686 -> begin
(let _0_388 = (closure_as_term cfg env t)
in (rebuild cfg env stack _0_388))
end)
end
| uu____4689 -> begin
(

let t_x = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in (

let uu____4691 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____4691) with
| (closing, f) -> begin
(

let f = (norm cfg ((Dummy)::env) [] f)
in (

let t = (let _0_390 = FStar_Syntax_Syntax.Tm_refine ((let _0_389 = (FStar_Syntax_Subst.close closing f)
in (((

let uu___154_4707 = x
in {FStar_Syntax_Syntax.ppname = uu___154_4707.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___154_4707.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t_x})), (_0_389))))
in (mk _0_390 t.FStar_Syntax_Syntax.pos))
in (rebuild cfg env stack t)))
end)))
end)
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(let _0_391 = (closure_as_term cfg env t)
in (rebuild cfg env stack _0_391))
end
| uu____4720 -> begin
(

let uu____4721 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4721) with
| (bs, c) -> begin
(

let c = (let _0_392 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____4732 -> (Dummy)::env) env))
in (norm_comp cfg _0_392 c))
in (

let t = (let _0_393 = (norm_binders cfg env bs)
in (FStar_Syntax_Util.arrow _0_393 c))
in (rebuild cfg env stack t)))
end))
end)
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, tc, l) -> begin
(match (stack) with
| ((Match (_))::_) | ((Arg (_))::_) | ((App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _, _))::_) | ((MemoLazy (_))::_) -> begin
(norm cfg env stack t1)
end
| uu____4774 -> begin
(

let t1 = (norm cfg env [] t1)
in ((log cfg (fun uu____4777 -> (FStar_Util.print_string "+++ Normalizing ascription \n")));
(

let tc = (match (tc) with
| FStar_Util.Inl (t) -> begin
FStar_Util.Inl ((norm cfg env [] t))
end
| FStar_Util.Inr (c) -> begin
FStar_Util.Inr ((norm_comp cfg env c))
end)
in (let _0_394 = (mk (FStar_Syntax_Syntax.Tm_ascribed (((t1), (tc), (l)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack _0_394)));
))
end)
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let stack = (Match (((env), (branches), (t.FStar_Syntax_Syntax.pos))))::stack
in (norm cfg env stack head))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4841, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4842); FStar_Syntax_Syntax.lbunivs = uu____4843; FStar_Syntax_Syntax.lbtyp = uu____4844; FStar_Syntax_Syntax.lbeff = uu____4845; FStar_Syntax_Syntax.lbdef = uu____4846})::uu____4847), uu____4848) -> begin
(rebuild cfg env stack t)
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let n = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv lb.FStar_Syntax_Syntax.lbeff)
in (

let uu____4874 = ((not ((FStar_All.pipe_right cfg.steps (FStar_List.contains NoDeltaSteps)))) && ((FStar_Syntax_Util.is_pure_effect n) || ((FStar_Syntax_Util.is_ghost_effect n) && (not ((FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))))))
in (match (uu____4874) with
| true -> begin
(

let env = (let _0_396 = Clos ((let _0_395 = (FStar_Util.mk_ref None)
in ((env), (lb.FStar_Syntax_Syntax.lbdef), (_0_395), (false))))
in (_0_396)::env)
in (norm cfg env stack body))
end
| uu____4893 -> begin
(

let uu____4894 = (let _0_399 = (let _0_398 = (let _0_397 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.left)
in (FStar_All.pipe_right _0_397 FStar_Syntax_Syntax.mk_binder))
in (_0_398)::[])
in (FStar_Syntax_Subst.open_term _0_399 body))
in (match (uu____4894) with
| (bs, body) -> begin
(

let lb = (

let uu___155_4902 = lb
in (let _0_405 = (let _0_402 = (let _0_400 = (FStar_List.hd bs)
in (FStar_All.pipe_right _0_400 Prims.fst))
in (FStar_All.pipe_right _0_402 (fun _0_401 -> FStar_Util.Inl (_0_401))))
in (let _0_404 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_403 = (norm cfg env [] lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _0_405; FStar_Syntax_Syntax.lbunivs = uu___155_4902.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _0_404; FStar_Syntax_Syntax.lbeff = uu___155_4902.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _0_403}))))
in (

let env' = (FStar_All.pipe_right bs (FStar_List.fold_left (fun env uu____4916 -> (Dummy)::env) env))
in (norm cfg env' ((Let (((env), (bs), (lb), (t.FStar_Syntax_Syntax.pos))))::stack) body)))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) when (FStar_List.contains (Exclude (Zeta)) cfg.steps) -> begin
(let _0_406 = (closure_as_term cfg env t)
in (rebuild cfg env stack _0_406))
end
| FStar_Syntax_Syntax.Tm_let (lbs, body) -> begin
(

let uu____4944 = (FStar_List.fold_right (fun lb uu____4966 -> (match (uu____4966) with
| (rec_env, memos, i) -> begin
(

let f_i = (FStar_Syntax_Syntax.bv_to_tm (

let uu___156_5005 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in {FStar_Syntax_Syntax.ppname = uu___156_5005.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = uu___156_5005.FStar_Syntax_Syntax.sort}))
in (

let fix_f_i = (mk (FStar_Syntax_Syntax.Tm_let (((lbs), (f_i)))) t.FStar_Syntax_Syntax.pos)
in (

let memo = (FStar_Util.mk_ref None)
in (

let rec_env = (Clos (((env), (fix_f_i), (memo), (true))))::rec_env
in ((rec_env), ((memo)::memos), ((i + (Prims.parse_int "1"))))))))
end)) (Prims.snd lbs) ((env), ([]), ((Prims.parse_int "0"))))
in (match (uu____4944) with
| (rec_env, memos, uu____5065) -> begin
(

let uu____5080 = (FStar_List.map2 (fun lb memo -> (FStar_ST.write memo (Some (((rec_env), (lb.FStar_Syntax_Syntax.lbdef)))))) (Prims.snd lbs) memos)
in (

let body_env = (FStar_List.fold_right (fun lb env -> (let _0_408 = Clos ((let _0_407 = (FStar_Util.mk_ref None)
in ((rec_env), (lb.FStar_Syntax_Syntax.lbdef), (_0_407), (false))))
in (_0_408)::env)) (Prims.snd lbs) env)
in (norm cfg body_env stack body)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (head, m) -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____5153; FStar_Syntax_Syntax.pos = uu____5154; FStar_Syntax_Syntax.vars = uu____5155}, uu____5156, uu____5157))::uu____5158 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____5164 -> begin
false
end)
in (match ((not (should_reify))) with
| true -> begin
(

let t = (norm cfg env [] t)
in (

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let uu___157_5170 = cfg
in {steps = (FStar_List.append ((NoDeltaSteps)::(Exclude (Zeta))::[]) cfg.steps); tcenv = uu___157_5170.tcenv; delta_level = (FStar_TypeChecker_Env.NoDelta)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic (((m), (t)))), (t.FStar_Syntax_Syntax.pos))))::stack) head))))
end
| uu____5171 -> begin
(

let uu____5172 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____5172) with
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), body) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let uu____5184 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____5184) with
| (uu____5185, bind_repr) -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
(

let head = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify lb.FStar_Syntax_Syntax.lbdef)
in (

let body = (FStar_All.pipe_left FStar_Syntax_Util.mk_reify body)
in (

let body = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((let _0_410 = (let _0_409 = (FStar_Syntax_Syntax.mk_binder x)
in (_0_409)::[])
in ((_0_410), (body), (None)))))) None body.FStar_Syntax_Syntax.pos)
in (

let bind_inst = (

let uu____5232 = (FStar_Syntax_Subst.compress bind_repr).FStar_Syntax_Syntax.n
in (match (uu____5232) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (uu____5236)::(uu____5237)::[]) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_414 = (let _0_413 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_412 = (let _0_411 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_0_411)::[])
in (_0_413)::_0_412))
in ((bind), (_0_414)))))) None t.FStar_Syntax_Syntax.pos)
end
| uu____5254 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in (

let reified = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_426 = (let _0_425 = (FStar_Syntax_Syntax.as_arg lb.FStar_Syntax_Syntax.lbtyp)
in (let _0_424 = (let _0_423 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_422 = (let _0_421 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_420 = (let _0_419 = (FStar_Syntax_Syntax.as_arg head)
in (let _0_418 = (let _0_417 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_416 = (let _0_415 = (FStar_Syntax_Syntax.as_arg body)
in (_0_415)::[])
in (_0_417)::_0_416))
in (_0_419)::_0_418))
in (_0_421)::_0_420))
in (_0_423)::_0_422))
in (_0_425)::_0_424))
in ((bind_inst), (_0_426)))))) None t.FStar_Syntax_Syntax.pos)
in (let _0_427 = (FStar_List.tl stack)
in (norm cfg env _0_427 reified)))))))
end
| FStar_Util.Inr (uu____5271) -> begin
(failwith "Cannot reify a top-level let binding")
end)
end)))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl cfg.tcenv m)
in (

let uu____5289 = ed.FStar_Syntax_Syntax.bind_repr
in (match (uu____5289) with
| (uu____5290, bind_repr) -> begin
(

let maybe_unfold_action = (fun head -> (

let maybe_extract_fv = (fun t -> (

let t = (

let uu____5313 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____5313) with
| FStar_Syntax_Syntax.Tm_uinst (t, uu____5317) -> begin
t
end
| uu____5322 -> begin
head
end))
in (

let uu____5323 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
in (match (uu____5323) with
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
Some (x)
end
| uu____5326 -> begin
None
end))))
in (

let uu____5327 = (maybe_extract_fv head)
in (match (uu____5327) with
| Some (x) when (let _0_428 = (FStar_Syntax_Syntax.lid_of_fv x)
in (FStar_TypeChecker_Env.is_action cfg.tcenv _0_428)) -> begin
(

let head = (norm cfg env [] head)
in (

let action_unfolded = (

let uu____5336 = (maybe_extract_fv head)
in (match (uu____5336) with
| Some (uu____5339) -> begin
Some (true)
end
| uu____5340 -> begin
Some (false)
end))
in ((head), (action_unfolded))))
end
| uu____5343 -> begin
((head), (None))
end))))
in (

let rec bind_on_lift = (fun args acc -> (match (args) with
| [] -> begin
(match ((FStar_List.rev acc)) with
| [] -> begin
(failwith "bind_on_lift should be always called with a non-empty list")
end
| ((head, uu____5390))::args -> begin
(

let uu____5405 = (maybe_unfold_action head)
in (match (uu____5405) with
| (head, found_action) -> begin
(

let mk = (fun tm -> ((FStar_Syntax_Syntax.mk tm) None t.FStar_Syntax_Syntax.pos))
in (

let body = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in (match (found_action) with
| None -> begin
(FStar_Syntax_Util.mk_reify body)
end
| Some (false) -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_monadic (((m), (t))))))))
end
| Some (true) -> begin
body
end)))
end))
end)
end
| ((e, q))::es -> begin
(

let uu____5451 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
in (match (uu____5451) with
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t')) when (not ((FStar_Syntax_Util.is_pure_effect m1))) -> begin
(

let x = (FStar_Syntax_Syntax.gen_bv "monadic_app_var" None t')
in (

let body = (let _0_431 = (let _0_430 = (let _0_429 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_0_429), (q)))
in (_0_430)::acc)
in (bind_on_lift es _0_431))
in (

let lifted_e0 = (reify_lift cfg.tcenv e0 m1 m2 t')
in (

let continuation = (FStar_Syntax_Util.abs ((((x), (None)))::[]) body (Some (FStar_Util.Inr (((m2), ([]))))))
in (

let bind_inst = (

let uu____5493 = (FStar_Syntax_Subst.compress bind_repr).FStar_Syntax_Syntax.n
in (match (uu____5493) with
| FStar_Syntax_Syntax.Tm_uinst (bind, (uu____5497)::(uu____5498)::[]) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_435 = (let _0_434 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t')
in (let _0_433 = (let _0_432 = (cfg.tcenv.FStar_TypeChecker_Env.universe_of cfg.tcenv t)
in (_0_432)::[])
in (_0_434)::_0_433))
in ((bind), (_0_435)))))) None e0.FStar_Syntax_Syntax.pos)
end
| uu____5515 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_447 = (let _0_446 = (FStar_Syntax_Syntax.as_arg t')
in (let _0_445 = (let _0_444 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_443 = (let _0_442 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_441 = (let _0_440 = (FStar_Syntax_Syntax.as_arg lifted_e0)
in (let _0_439 = (let _0_438 = (FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun)
in (let _0_437 = (let _0_436 = (FStar_Syntax_Syntax.as_arg continuation)
in (_0_436)::[])
in (_0_438)::_0_437))
in (_0_440)::_0_439))
in (_0_442)::_0_441))
in (_0_444)::_0_443))
in (_0_446)::_0_445))
in ((bind_inst), (_0_447)))))) None e0.FStar_Syntax_Syntax.pos))))))
end
| FStar_Syntax_Syntax.Tm_meta (e0, FStar_Syntax_Syntax.Meta_monadic_lift (uu____5530)) -> begin
(bind_on_lift es ((((e0), (q)))::acc))
end
| uu____5546 -> begin
(bind_on_lift es ((((e), (q)))::acc))
end))
end))
in (

let binded_head = (let _0_449 = (let _0_448 = (FStar_Syntax_Syntax.as_arg head)
in (_0_448)::args)
in (bind_on_lift _0_449 []))
in (let _0_450 = (FStar_List.tl stack)
in (norm cfg env _0_450 binded_head)))))
end)))
end
| FStar_Syntax_Syntax.Tm_meta (e, FStar_Syntax_Syntax.Meta_monadic_lift (msrc, mtgt, t')) -> begin
(

let lifted = (reify_lift cfg.tcenv e msrc mtgt t')
in (norm cfg env stack lifted))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let branches = (FStar_All.pipe_right branches (FStar_List.map (fun uu____5651 -> (match (uu____5651) with
| (pat, wopt, tm) -> begin
(let _0_451 = (FStar_Syntax_Util.mk_reify tm)
in ((pat), (wopt), (_0_451)))
end))))
in (

let tm = (mk (FStar_Syntax_Syntax.Tm_match (((e), (branches)))) t.FStar_Syntax_Syntax.pos)
in (let _0_452 = (FStar_List.tl stack)
in (norm cfg env _0_452 tm))))
end
| uu____5712 -> begin
(norm cfg env stack head)
end))
end))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let should_reify = (match (stack) with
| (App ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify); FStar_Syntax_Syntax.tk = uu____5721; FStar_Syntax_Syntax.pos = uu____5722; FStar_Syntax_Syntax.vars = uu____5723}, uu____5724, uu____5725))::uu____5726 -> begin
(FStar_All.pipe_right cfg.steps (FStar_List.contains Reify))
end
| uu____5732 -> begin
false
end)
in (match (should_reify) with
| true -> begin
(let _0_454 = (FStar_List.tl stack)
in (let _0_453 = (reify_lift cfg.tcenv head m m' t)
in (norm cfg env _0_454 _0_453)))
end
| uu____5733 -> begin
(

let uu____5734 = (((FStar_Syntax_Util.is_pure_effect m) || (FStar_Syntax_Util.is_ghost_effect m)) && (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations)))
in (match (uu____5734) with
| true -> begin
(

let stack = (Steps (((cfg.steps), (cfg.delta_level))))::stack
in (

let cfg = (

let uu___158_5739 = cfg
in {steps = (PureSubtermsWithinComputations)::(Primops)::(AllowUnboundUniverses)::(EraseUniverses)::(Exclude (Zeta))::[]; tcenv = uu___158_5739.tcenv; delta_level = (FStar_TypeChecker_Env.Inlining)::(FStar_TypeChecker_Env.Eager_unfolding_only)::[]})
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)))
end
| uu____5742 -> begin
(norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_monadic_lift (((m), (m'), (t)))), (head.FStar_Syntax_Syntax.pos))))::stack) head)
end))
end))
end
| uu____5745 -> begin
(match (stack) with
| (uu____5746)::uu____5747 -> begin
(match (m) with
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____5751) -> begin
(norm cfg env ((Meta (((m), (r))))::stack) head)
end
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
(

let args = (norm_pattern_args cfg env args)
in (norm cfg env ((Meta (((FStar_Syntax_Syntax.Meta_pattern (args)), (t.FStar_Syntax_Syntax.pos))))::stack) head))
end
| uu____5766 -> begin
(norm cfg env stack head)
end)
end
| uu____5767 -> begin
(

let head = (norm cfg env [] head)
in (

let m = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (args) -> begin
FStar_Syntax_Syntax.Meta_pattern ((norm_pattern_args cfg env args))
end
| uu____5777 -> begin
m
end)
in (

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((head), (m)))) t.FStar_Syntax_Syntax.pos)
in (rebuild cfg env stack t))))
end)
end)
end);
)))
and reify_lift : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.monad_name  ->  FStar_Syntax_Syntax.monad_name  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env e msrc mtgt t -> (match ((FStar_Syntax_Util.is_pure_effect msrc)) with
| true -> begin
(

let ed = (FStar_TypeChecker_Env.get_effect_decl env mtgt)
in (

let uu____5791 = ed.FStar_Syntax_Syntax.return_repr
in (match (uu____5791) with
| (uu____5792, return_repr) -> begin
(

let return_inst = (

let uu____5799 = (FStar_Syntax_Subst.compress return_repr).FStar_Syntax_Syntax.n
in (match (uu____5799) with
| FStar_Syntax_Syntax.Tm_uinst (return_tm, (uu____5803)::[]) -> begin
((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uinst ((let _0_456 = (let _0_455 = (env.FStar_TypeChecker_Env.universe_of env t)
in (_0_455)::[])
in ((return_tm), (_0_456)))))) None e.FStar_Syntax_Syntax.pos)
end
| uu____5820 -> begin
(failwith "NIY : Reification of indexed effects")
end))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((let _0_460 = (let _0_459 = (FStar_Syntax_Syntax.as_arg t)
in (let _0_458 = (let _0_457 = (FStar_Syntax_Syntax.as_arg e)
in (_0_457)::[])
in (_0_459)::_0_458))
in ((return_inst), (_0_460)))))) None e.FStar_Syntax_Syntax.pos))
end)))
end
| uu____5834 -> begin
(failwith "NYI: non pure monadic lift normalisation")
end))
and norm_pattern_args : cfg  ->  env  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list Prims.list = (fun cfg env args -> (FStar_All.pipe_right args (FStar_List.map (FStar_List.map (fun uu____5864 -> (match (uu____5864) with
| (a, imp) -> begin
(let _0_461 = (norm cfg env [] a)
in ((_0_461), (imp)))
end))))))
and norm_comp : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun cfg env comp -> (

let comp = (ghost_to_pure_aux cfg env comp)
in (match (comp.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu___159_5885 = comp
in (let _0_464 = FStar_Syntax_Syntax.Total ((let _0_463 = (norm cfg env [] t)
in (let _0_462 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_0_463), (_0_462)))))
in {FStar_Syntax_Syntax.n = _0_464; FStar_Syntax_Syntax.tk = uu___159_5885.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___159_5885.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___159_5885.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu___160_5901 = comp
in (let _0_467 = FStar_Syntax_Syntax.GTotal ((let _0_466 = (norm cfg env [] t)
in (let _0_465 = (FStar_Option.map (norm_universe cfg env) uopt)
in ((_0_466), (_0_465)))))
in {FStar_Syntax_Syntax.n = _0_467; FStar_Syntax_Syntax.tk = uu___160_5901.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___160_5901.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___160_5901.FStar_Syntax_Syntax.vars}))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let norm_args = (fun args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5933 -> (match (uu____5933) with
| (a, i) -> begin
(let _0_468 = (norm cfg env [] a)
in ((_0_468), (i)))
end)))))
in (

let flags = (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags (FStar_List.map (fun uu___129_5944 -> (match (uu___129_5944) with
| FStar_Syntax_Syntax.DECREASES (t) -> begin
FStar_Syntax_Syntax.DECREASES ((norm cfg env [] t))
end
| f -> begin
f
end))))
in (

let uu___161_5949 = comp
in (let _0_472 = FStar_Syntax_Syntax.Comp ((

let uu___162_5952 = ct
in (let _0_471 = (FStar_List.map (norm_universe cfg env) ct.FStar_Syntax_Syntax.comp_univs)
in (let _0_470 = (norm cfg env [] ct.FStar_Syntax_Syntax.result_typ)
in (let _0_469 = (norm_args ct.FStar_Syntax_Syntax.effect_args)
in {FStar_Syntax_Syntax.comp_univs = _0_471; FStar_Syntax_Syntax.effect_name = uu___162_5952.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _0_470; FStar_Syntax_Syntax.effect_args = _0_469; FStar_Syntax_Syntax.flags = flags})))))
in {FStar_Syntax_Syntax.n = _0_472; FStar_Syntax_Syntax.tk = uu___161_5949.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___161_5949.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___161_5949.FStar_Syntax_Syntax.vars}))))
end)))
and ghost_to_pure_aux : cfg  ->  env  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun cfg env c -> (

let norm = (fun t -> (norm (

let uu___163_5964 = cfg
in {steps = (Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(AllowUnboundUniverses)::[]; tcenv = uu___163_5964.tcenv; delta_level = uu___163_5964.delta_level}) env [] t))
in (

let non_info = (fun t -> (FStar_Syntax_Util.non_informative (norm t)))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (uu____5971) -> begin
c
end
| FStar_Syntax_Syntax.GTotal (t, uopt) when (non_info t) -> begin
(

let uu___164_5985 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (((t), (uopt))); FStar_Syntax_Syntax.tk = uu___164_5985.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___164_5985.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___164_5985.FStar_Syntax_Syntax.vars})
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let l = (FStar_TypeChecker_Env.norm_eff_name cfg.tcenv ct.FStar_Syntax_Syntax.effect_name)
in (

let uu____5995 = ((FStar_Syntax_Util.is_ghost_effect l) && (non_info ct.FStar_Syntax_Syntax.result_typ))
in (match (uu____5995) with
| true -> begin
(

let ct = (match ((downgrade_ghost_effect_name ct.FStar_Syntax_Syntax.effect_name)) with
| Some (pure_eff) -> begin
(

let uu___165_6000 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___165_6000.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = pure_eff; FStar_Syntax_Syntax.result_typ = uu___165_6000.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___165_6000.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___165_6000.FStar_Syntax_Syntax.flags})
end
| None -> begin
(

let ct = (unfold_effect_abbrev cfg.tcenv c)
in (

let uu___166_6002 = ct
in {FStar_Syntax_Syntax.comp_univs = uu___166_6002.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = FStar_Syntax_Const.effect_PURE_lid; FStar_Syntax_Syntax.result_typ = uu___166_6002.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___166_6002.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = uu___166_6002.FStar_Syntax_Syntax.flags}))
end)
in (

let uu___167_6003 = c
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (ct); FStar_Syntax_Syntax.tk = uu___167_6003.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = uu___167_6003.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___167_6003.FStar_Syntax_Syntax.vars}))
end
| uu____6008 -> begin
c
end)))
end
| uu____6009 -> begin
c
end))))
and norm_binder : cfg  ->  env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder = (fun cfg env uu____6012 -> (match (uu____6012) with
| (x, imp) -> begin
(let _0_474 = (

let uu___168_6015 = x
in (let _0_473 = (norm cfg env [] x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___168_6015.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___168_6015.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_473}))
in ((_0_474), (imp)))
end))
and norm_binders : cfg  ->  env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun cfg env bs -> (

let uu____6019 = (FStar_List.fold_left (fun uu____6026 b -> (match (uu____6026) with
| (nbs', env) -> begin
(

let b = (norm_binder cfg env b)
in (((b)::nbs'), ((Dummy)::env)))
end)) (([]), (env)) bs)
in (match (uu____6019) with
| (nbs, uu____6043) -> begin
(FStar_List.rev nbs)
end)))
and norm_lcomp_opt : cfg  ->  env  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option  ->  (FStar_Syntax_Syntax.lcomp, FStar_Syntax_Syntax.residual_comp) FStar_Util.either Prims.option = (fun cfg env lopt -> (match (lopt) with
| Some (FStar_Util.Inl (lc)) -> begin
(

let flags = (filter_out_lcomp_cflags lc)
in (

let uu____6060 = (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
in (match (uu____6060) with
| true -> begin
(

let t = (norm cfg env [] lc.FStar_Syntax_Syntax.res_typ)
in (

let uu____6065 = (FStar_Syntax_Util.is_total_lcomp lc)
in (match (uu____6065) with
| true -> begin
Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (let _0_475 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.comp_set_flags _0_475 flags)))))
end
| uu____6071 -> begin
Some (FStar_Util.Inl ((FStar_Syntax_Util.lcomp_of_comp (let _0_476 = (FStar_Syntax_Syntax.mk_GTotal t)
in (FStar_Syntax_Util.comp_set_flags _0_476 flags)))))
end)))
end
| uu____6074 -> begin
Some (FStar_Util.Inr (((lc.FStar_Syntax_Syntax.eff_name), (flags))))
end)))
end
| uu____6084 -> begin
lopt
end))
and rebuild : cfg  ->  env  ->  stack  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun cfg env stack t -> (match (stack) with
| [] -> begin
t
end
| (Debug (tm))::stack -> begin
((

let uu____6096 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug cfg.tcenv) (FStar_Options.Other ("print_normalized_terms")))
in (match (uu____6096) with
| true -> begin
(let _0_478 = (FStar_Syntax_Print.term_to_string tm)
in (let _0_477 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print2 "Normalized %s to %s\n" _0_478 _0_477)))
end
| uu____6097 -> begin
()
end));
(rebuild cfg env stack t);
)
end
| (Steps (s, dl))::stack -> begin
(rebuild (

let uu___169_6104 = cfg
in {steps = s; tcenv = uu___169_6104.tcenv; delta_level = dl}) env stack t)
end
| (Meta (m, r))::stack -> begin
(

let t = (mk (FStar_Syntax_Syntax.Tm_meta (((t), (m)))) r)
in (rebuild cfg env stack t))
end
| (MemoLazy (r))::stack -> begin
((set_memo r ((env), (t)));
(log cfg (fun uu____6124 -> (let _0_479 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "\tSet memo %s\n" _0_479))));
(rebuild cfg env stack t);
)
end
| (Let (env', bs, lb, r))::stack -> begin
(

let body = (FStar_Syntax_Subst.close bs t)
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (body)))) None r)
in (rebuild cfg env' stack t)))
end
| (Abs (env', bs, env'', lopt, r))::stack -> begin
(

let bs = (norm_binders cfg env' bs)
in (

let lopt = (norm_lcomp_opt cfg env'' lopt)
in (let _0_480 = (

let uu___170_6161 = (FStar_Syntax_Util.abs bs t lopt)
in {FStar_Syntax_Syntax.n = uu___170_6161.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___170_6161.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = r; FStar_Syntax_Syntax.vars = uu___170_6161.FStar_Syntax_Syntax.vars})
in (rebuild cfg env stack _0_480))))
end
| ((Arg (Univ (_), _, _))::_) | ((Arg (Dummy, _, _))::_) -> begin
(failwith "Impossible")
end
| (UnivArgs (us, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.mk_Tm_uinst t us)
in (rebuild cfg env stack t))
end
| (Arg (Clos (env, tm, m, uu____6183), aq, r))::stack -> begin
((log cfg (fun uu____6199 -> (let _0_481 = (FStar_Syntax_Print.term_to_string tm)
in (FStar_Util.print1 "Rebuilding with arg %s\n" _0_481))));
(match ((FStar_List.contains (Exclude (Iota)) cfg.steps)) with
| true -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end
| uu____6206 -> begin
(

let stack = (App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end)
end
| uu____6209 -> begin
(

let uu____6210 = (FStar_ST.read m)
in (match (uu____6210) with
| None -> begin
(match ((FStar_List.contains WHNF cfg.steps)) with
| true -> begin
(

let arg = (closure_as_term cfg env tm)
in (

let t = (FStar_Syntax_Syntax.extend_app t ((arg), (aq)) None r)
in (rebuild cfg env stack t)))
end
| uu____6230 -> begin
(

let stack = (MemoLazy (m))::(App (((t), (aq), (r))))::stack
in (norm cfg env stack tm))
end)
end
| Some (uu____6236, a) -> begin
(

let t = (FStar_Syntax_Syntax.extend_app t ((a), (aq)) None r)
in (rebuild cfg env stack t))
end))
end);
)
end
| (App (head, aq, r))::stack -> begin
(

let t = (FStar_Syntax_Syntax.extend_app head ((t), (aq)) None r)
in (let _0_482 = (maybe_simplify cfg.steps t)
in (rebuild cfg env stack _0_482)))
end
| (Match (env, branches, r))::stack -> begin
((log cfg (fun uu____6264 -> (let _0_483 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.print1 "Rebuilding with match, scrutinee is %s ...\n" _0_483))));
(

let scrutinee = t
in (

let norm_and_rebuild_match = (fun uu____6269 -> (

let whnf = (FStar_List.contains WHNF cfg.steps)
in (

let cfg_exclude_iota_zeta = (

let new_delta = (FStar_All.pipe_right cfg.delta_level (FStar_List.filter (fun uu___130_6276 -> (match (uu___130_6276) with
| (FStar_TypeChecker_Env.Inlining) | (FStar_TypeChecker_Env.Eager_unfolding_only) -> begin
true
end
| uu____6277 -> begin
false
end))))
in (

let steps' = (

let uu____6280 = (FStar_All.pipe_right cfg.steps (FStar_List.contains PureSubtermsWithinComputations))
in (match (uu____6280) with
| true -> begin
(Exclude (Zeta))::[]
end
| uu____6282 -> begin
(Exclude (Iota))::(Exclude (Zeta))::[]
end))
in (

let uu___171_6283 = cfg
in {steps = (FStar_List.append steps' cfg.steps); tcenv = uu___171_6283.tcenv; delta_level = new_delta})))
in (

let norm_or_whnf = (fun env t -> (match (whnf) with
| true -> begin
(closure_as_term cfg_exclude_iota_zeta env t)
end
| uu____6293 -> begin
(norm cfg_exclude_iota_zeta env [] t)
end))
in (

let rec norm_pat = (fun env p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (uu____6317) -> begin
((p), (env))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let uu____6337 = (norm_pat env hd)
in (match (uu____6337) with
| (hd, env') -> begin
(

let tl = (FStar_All.pipe_right tl (FStar_List.map (fun p -> (Prims.fst (norm_pat env p)))))
in (((

let uu___172_6379 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((hd)::tl); FStar_Syntax_Syntax.ty = uu___172_6379.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___172_6379.FStar_Syntax_Syntax.p})), (env')))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let uu____6396 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun uu____6430 uu____6431 -> (match (((uu____6430), (uu____6431))) with
| ((pats, env), (p, b)) -> begin
(

let uu____6496 = (norm_pat env p)
in (match (uu____6496) with
| (p, env) -> begin
(((((p), (b)))::pats), (env))
end))
end)) (([]), (env))))
in (match (uu____6396) with
| (pats, env) -> begin
(((

let uu___173_6562 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons (((fv), ((FStar_List.rev pats)))); FStar_Syntax_Syntax.ty = uu___173_6562.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___173_6562.FStar_Syntax_Syntax.p})), (env))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let uu___174_6576 = x
in (let _0_484 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___174_6576.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___174_6576.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_484}))
in (((

let uu___175_6580 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = uu___175_6580.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___175_6580.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let uu___176_6585 = x
in (let _0_485 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___176_6585.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___176_6585.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_485}))
in (((

let uu___177_6589 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = uu___177_6589.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___177_6589.FStar_Syntax_Syntax.p})), ((Dummy)::env)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t) -> begin
(

let x = (

let uu___178_6599 = x
in (let _0_486 = (norm_or_whnf env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___178_6599.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___178_6599.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _0_486}))
in (

let t = (norm_or_whnf env t)
in (((

let uu___179_6604 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term (((x), (t))); FStar_Syntax_Syntax.ty = uu___179_6604.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = uu___179_6604.FStar_Syntax_Syntax.p})), (env))))
end))
in (

let branches = (match (env) with
| [] when whnf -> begin
branches
end
| uu____6608 -> begin
(FStar_All.pipe_right branches (FStar_List.map (fun branch -> (

let uu____6611 = (FStar_Syntax_Subst.open_branch branch)
in (match (uu____6611) with
| (p, wopt, e) -> begin
(

let uu____6629 = (norm_pat env p)
in (match (uu____6629) with
| (p, env) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
Some ((norm_or_whnf env w))
end)
in (

let e = (norm_or_whnf env e)
in (FStar_Syntax_Util.branch ((p), (wopt), (e)))))
end))
end)))))
end)
in (let _0_487 = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (branches)))) r)
in (rebuild cfg env stack _0_487))))))))
in (

let rec is_cons = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst (h, uu____6666) -> begin
(is_cons h)
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Data_ctor)})) | (FStar_Syntax_Syntax.Tm_fvar ({FStar_Syntax_Syntax.fv_name = _; FStar_Syntax_Syntax.fv_delta = _; FStar_Syntax_Syntax.fv_qual = Some (FStar_Syntax_Syntax.Record_ctor (_))})) -> begin
true
end
| uu____6677 -> begin
false
end))
in (

let guard_when_clause = (fun wopt b rest -> (match (wopt) with
| None -> begin
b
end
| Some (w) -> begin
(

let then_branch = b
in (

let else_branch = (mk (FStar_Syntax_Syntax.Tm_match (((scrutinee), (rest)))) r)
in (FStar_Syntax_Util.if_then_else w then_branch else_branch)))
end))
in (

let rec matches_pat = (fun scrutinee p -> (

let scrutinee = (FStar_Syntax_Util.unmeta scrutinee)
in (

let uu____6776 = (FStar_Syntax_Util.head_and_args scrutinee)
in (match (uu____6776) with
| (head, args) -> begin
(match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let mopt = (FStar_Util.find_map ps (fun p -> (

let m = (matches_pat scrutinee p)
in (match (m) with
| FStar_Util.Inl (uu____6833) -> begin
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
FStar_Util.Inl ((scrutinee)::[])
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____6864) -> begin
FStar_Util.Inl ([])
end
| FStar_Syntax_Syntax.Pat_constant (s) -> begin
(match (scrutinee.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (s') when (s = s') -> begin
FStar_Util.Inl ([])
end
| uu____6876 -> begin
FStar_Util.Inr ((not ((is_cons head))))
end)
end
| FStar_Syntax_Syntax.Pat_cons (fv, arg_pats) -> begin
(

let uu____6890 = (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n
in (match (uu____6890) with
| FStar_Syntax_Syntax.Tm_fvar (fv') when (FStar_Syntax_Syntax.fv_eq fv fv') -> begin
(matches_args [] args arg_pats)
end
| uu____6895 -> begin
FStar_Util.Inr ((not ((is_cons head))))
end))
end)
end))))
and matches_args = (fun out a p -> (match (((a), (p))) with
| ([], []) -> begin
FStar_Util.Inl (out)
end
| (((t, uu____6929))::rest_a, ((p, uu____6932))::rest_p) -> begin
(

let uu____6960 = (matches_pat t p)
in (match (uu____6960) with
| FStar_Util.Inl (s) -> begin
(matches_args (FStar_List.append out s) rest_a rest_p)
end
| m -> begin
m
end))
end
| uu____6974 -> begin
FStar_Util.Inr (false)
end))
in (

let rec matches = (fun scrutinee p -> (match (p) with
| [] -> begin
(norm_and_rebuild_match ())
end
| ((p, wopt, b))::rest -> begin
(

let uu____7045 = (matches_pat scrutinee p)
in (match (uu____7045) with
| FStar_Util.Inr (false) -> begin
(matches scrutinee rest)
end
| FStar_Util.Inr (true) -> begin
(norm_and_rebuild_match ())
end
| FStar_Util.Inl (s) -> begin
((log cfg (fun uu____7055 -> (let _0_490 = (FStar_Syntax_Print.pat_to_string p)
in (let _0_489 = (let _0_488 = (FStar_List.map FStar_Syntax_Print.term_to_string s)
in (FStar_All.pipe_right _0_488 (FStar_String.concat "; ")))
in (FStar_Util.print2 "Matches pattern %s with subst = %s\n" _0_490 _0_489)))));
(

let env = (FStar_List.fold_left (fun env t -> (let _0_492 = Clos ((let _0_491 = (FStar_Util.mk_ref (Some ((([]), (t)))))
in (([]), (t), (_0_491), (false))))
in (_0_492)::env)) env s)
in (let _0_493 = (guard_when_clause wopt b rest)
in (norm cfg env stack _0_493)));
)
end))
end))
in (

let uu____7079 = (FStar_All.pipe_right cfg.steps (FStar_List.contains (Exclude (Iota))))
in (match (uu____7079) with
| true -> begin
(norm_and_rebuild_match ())
end
| uu____7080 -> begin
(matches scrutinee branches)
end))))))));
)
end))


let config : step Prims.list  ->  FStar_TypeChecker_Env.env  ->  cfg = (fun s e -> (

let d = (FStar_All.pipe_right s (FStar_List.collect (fun uu___131_7093 -> (match (uu___131_7093) with
| UnfoldUntil (k) -> begin
(FStar_TypeChecker_Env.Unfold (k))::[]
end
| Eager_unfolding -> begin
(FStar_TypeChecker_Env.Eager_unfolding_only)::[]
end
| Inlining -> begin
(FStar_TypeChecker_Env.Inlining)::[]
end
| uu____7096 -> begin
[]
end))))
in (

let d = (match (d) with
| [] -> begin
(FStar_TypeChecker_Env.NoDelta)::[]
end
| uu____7100 -> begin
d
end)
in {steps = s; tcenv = e; delta_level = d})))


let normalize : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s e t -> (let _0_494 = (config s e)
in (norm _0_494 [] [] t)))


let normalize_comp : steps  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s e t -> (let _0_495 = (config s e)
in (norm_comp _0_495 [] t)))


let normalize_universe : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun env u -> (let _0_496 = (config [] env)
in (norm_universe _0_496 [] u)))


let ghost_to_pure : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun env c -> (let _0_497 = (config [] env)
in (ghost_to_pure_aux _0_497 [] c)))


let ghost_to_pure_lcomp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun env lc -> (

let cfg = (config ((Eager_unfolding)::(UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(EraseUniverses)::(AllowUnboundUniverses)::[]) env)
in (

let non_info = (fun t -> (FStar_Syntax_Util.non_informative (norm cfg [] [] t)))
in (

let uu____7143 = ((FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name) && (non_info lc.FStar_Syntax_Syntax.res_typ))
in (match (uu____7143) with
| true -> begin
(match ((downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name)) with
| Some (pure_eff) -> begin
(

let uu___180_7145 = lc
in {FStar_Syntax_Syntax.eff_name = pure_eff; FStar_Syntax_Syntax.res_typ = uu___180_7145.FStar_Syntax_Syntax.res_typ; FStar_Syntax_Syntax.cflags = uu___180_7145.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun uu____7146 -> (let _0_498 = (lc.FStar_Syntax_Syntax.comp ())
in (ghost_to_pure env _0_498)))})
end
| None -> begin
lc
end)
end
| uu____7147 -> begin
lc
end)))))


let term_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env t -> (FStar_Syntax_Print.term_to_string (normalize ((AllowUnboundUniverses)::[]) env t)))


let comp_to_string : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (FStar_Syntax_Print.comp_to_string (let _0_499 = (config ((AllowUnboundUniverses)::[]) env)
in (norm_comp _0_499 [] c))))


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
(let _0_501 = FStar_Syntax_Syntax.Tm_refine ((let _0_500 = (FStar_Syntax_Util.mk_conj phi1 phi)
in ((y), (_0_500))))
in (mk _0_501 t0.FStar_Syntax_Syntax.pos))
end
| uu____7198 -> begin
t
end))
end
| uu____7199 -> begin
t
end)))
in (aux t))))


let eta_expand_with_type : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term = (fun t sort -> (

let uu____7206 = (FStar_Syntax_Util.arrow_formals_comp sort)
in (match (uu____7206) with
| (binders, c) -> begin
(match (binders) with
| [] -> begin
t
end
| uu____7222 -> begin
(

let uu____7226 = (FStar_All.pipe_right binders FStar_Syntax_Util.args_of_binders)
in (match (uu____7226) with
| (binders, args) -> begin
(let _0_506 = ((FStar_Syntax_Syntax.mk_Tm_app t args) None t.FStar_Syntax_Syntax.pos)
in (let _0_505 = (let _0_504 = (FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c) (fun _0_502 -> FStar_Util.Inl (_0_502)))
in (FStar_All.pipe_right _0_504 (fun _0_503 -> Some (_0_503))))
in (FStar_Syntax_Util.abs binders _0_506 _0_505)))
end))
end)
end)))


let eta_expand : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____7296 = (let _0_507 = (FStar_ST.read t.FStar_Syntax_Syntax.tk)
in ((_0_507), (t.FStar_Syntax_Syntax.n)))
in (match (uu____7296) with
| (Some (sort), uu____7305) -> begin
(let _0_508 = (mk sort t.FStar_Syntax_Syntax.pos)
in (eta_expand_with_type t _0_508))
end
| (uu____7307, FStar_Syntax_Syntax.Tm_name (x)) -> begin
(eta_expand_with_type t x.FStar_Syntax_Syntax.sort)
end
| uu____7311 -> begin
(

let uu____7315 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____7315) with
| (head, args) -> begin
(

let uu____7341 = (FStar_Syntax_Subst.compress head).FStar_Syntax_Syntax.n
in (match (uu____7341) with
| FStar_Syntax_Syntax.Tm_uvar (uu____7342, thead) -> begin
(

let uu____7356 = (FStar_Syntax_Util.arrow_formals thead)
in (match (uu____7356) with
| (formals, tres) -> begin
(match (((FStar_List.length formals) = (FStar_List.length args))) with
| true -> begin
t
end
| uu____7386 -> begin
(

let uu____7387 = (env.FStar_TypeChecker_Env.type_of (

let uu___181_7391 = env
in {FStar_TypeChecker_Env.solver = uu___181_7391.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___181_7391.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___181_7391.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___181_7391.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___181_7391.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___181_7391.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = uu___181_7391.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___181_7391.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___181_7391.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___181_7391.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___181_7391.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___181_7391.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___181_7391.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___181_7391.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___181_7391.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___181_7391.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___181_7391.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___181_7391.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___181_7391.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___181_7391.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___181_7391.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____7387) with
| (uu____7392, ty, uu____7394) -> begin
(eta_expand_with_type t ty)
end))
end)
end))
end
| uu____7395 -> begin
(

let uu____7396 = (env.FStar_TypeChecker_Env.type_of (

let uu___182_7400 = env
in {FStar_TypeChecker_Env.solver = uu___182_7400.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___182_7400.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___182_7400.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___182_7400.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___182_7400.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___182_7400.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = None; FStar_TypeChecker_Env.sigtab = uu___182_7400.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___182_7400.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___182_7400.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___182_7400.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___182_7400.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___182_7400.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___182_7400.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___182_7400.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___182_7400.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___182_7400.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___182_7400.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___182_7400.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___182_7400.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___182_7400.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = true; FStar_TypeChecker_Env.qname_and_index = uu___182_7400.FStar_TypeChecker_Env.qname_and_index}) t)
in (match (uu____7396) with
| (uu____7401, ty, uu____7403) -> begin
(eta_expand_with_type t ty)
end))
end))
end))
end)))





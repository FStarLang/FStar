
open Prims
open FStar_Pervasives

let env_hook : FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let inspect_aqual : FStar_Syntax_Syntax.aqual  ->  FStar_Reflection_Data.aqualv = (fun aq -> (match (aq) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____35)) -> begin
FStar_Reflection_Data.Q_Implicit
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
FStar_Reflection_Data.Q_Meta (t)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Reflection_Data.Q_Explicit
end
| FStar_Pervasives_Native.None -> begin
FStar_Reflection_Data.Q_Explicit
end))


let pack_aqual : FStar_Reflection_Data.aqualv  ->  FStar_Syntax_Syntax.aqual = (fun aqv -> (match (aqv) with
| FStar_Reflection_Data.Q_Explicit -> begin
FStar_Pervasives_Native.None
end
| FStar_Reflection_Data.Q_Implicit -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
end
| FStar_Reflection_Data.Q_Meta (t) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t))
end))


let inspect_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (

let uu____60 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____60)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (

let fallback = (fun uu____79 -> (

let quals = (

let uu____83 = (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid)
in (match (uu____83) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____88 -> begin
(

let uu____90 = (FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid)
in (match (uu____90) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____95 -> begin
(

let uu____97 = (FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid)
in (match (uu____97) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____102 -> begin
(

let uu____104 = (FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid)
in (match (uu____104) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____109 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
end))
in (

let uu____111 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____111 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) quals))))
in (

let uu____113 = (FStar_ST.op_Bang env_hook)
in (match (uu____113) with
| FStar_Pervasives_Native.None -> begin
(fallback ())
end
| FStar_Pervasives_Native.Some (env) -> begin
(

let qninfo = (FStar_TypeChecker_Env.lookup_qname env lid)
in (match (qninfo) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, _us), _rng) -> begin
(

let quals = (FStar_Syntax_DsEnv.fv_qual_of_se se)
in (

let uu____193 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____193 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) quals)))
end
| uu____195 -> begin
(fallback ())
end))
end)))))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____214)::xs -> begin
(last xs)
end))


let rec init : 'a . 'a Prims.list  ->  'a Prims.list = (fun l -> (match (l) with
| [] -> begin
(failwith "init: empty list")
end
| (x)::[] -> begin
[]
end
| (x)::xs -> begin
(

let uu____244 = (init xs)
in (x)::uu____244)
end))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____254) -> begin
(

let uu____269 = (FStar_BigInt.big_int_of_string s)
in FStar_Reflection_Data.C_Int (uu____269))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| FStar_Const.Const_string (s, uu____273) -> begin
FStar_Reflection_Data.C_String (s)
end
| FStar_Const.Const_range (r) -> begin
FStar_Reflection_Data.C_Range (r)
end
| FStar_Const.Const_reify -> begin
FStar_Reflection_Data.C_Reify
end
| FStar_Const.Const_reflect (l) -> begin
(

let uu____278 = (FStar_Ident.path_of_lid l)
in FStar_Reflection_Data.C_Reflect (uu____278))
end
| uu____279 -> begin
(

let uu____280 = (

let uu____282 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____282))
in (failwith uu____280))
end))


let rec inspect_ln : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (

let t3 = (FStar_Syntax_Util.unlazy_emb t2)
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t4, uu____295) -> begin
(inspect_ln t4)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
FStar_Reflection_Data.Tv_Var (bv)
end
| FStar_Syntax_Syntax.Tm_bvar (bv) -> begin
FStar_Reflection_Data.Tv_BVar (bv)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Reflection_Data.Tv_FVar (fv)
end
| FStar_Syntax_Syntax.Tm_app (hd1, []) -> begin
(failwith "inspect_ln: empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____353 = (last args)
in (match (uu____353) with
| (a, q) -> begin
(

let q' = (inspect_aqual q)
in (

let uu____381 = (

let uu____386 = (

let uu____387 = (

let uu____392 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____392))
in (uu____387 FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos))
in ((uu____386), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____381)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____403, uu____404) -> begin
(failwith "inspect_ln: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs ((b)::bs, t4, k) -> begin
(

let body = (match (bs) with
| [] -> begin
t4
end
| bs1 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs1), (t4), (k)))) FStar_Pervasives_Native.None t4.FStar_Syntax_Syntax.pos)
end)
in FStar_Reflection_Data.Tv_Abs (((b), (body))))
end
| FStar_Syntax_Syntax.Tm_type (uu____496) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect_ln: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____517) -> begin
(

let uu____532 = (FStar_Syntax_Util.arrow_one t3)
in (match (uu____532) with
| FStar_Pervasives_Native.Some (b, c) -> begin
FStar_Reflection_Data.Tv_Arrow (((b), (c)))
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t4) -> begin
FStar_Reflection_Data.Tv_Refine (((bv), (t4)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____557 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____557))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) -> begin
(

let uu____576 = (

let uu____581 = (

let uu____582 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____582))
in ((uu____581), (((ctx_u), (s)))))
in FStar_Reflection_Data.Tv_Uvar (uu____576))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____612 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____614) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| FStar_Util.Inl (bv) -> begin
FStar_Reflection_Data.Tv_Let (((false), (bv), (lb.FStar_Syntax_Syntax.lbdef), (t21)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_let ((true, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____638 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____640) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| FStar_Util.Inl (bv) -> begin
FStar_Reflection_Data.Tv_Let (((true), (bv), (lb.FStar_Syntax_Syntax.lbdef), (t21)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_match (t4, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____693 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____693))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____714 = (

let uu____721 = (FStar_List.map (fun uu____734 -> (match (uu____734) with
| (p1, uu____743) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____721)))
in FStar_Reflection_Data.Pat_Cons (uu____714))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, t5) -> begin
FStar_Reflection_Data.Pat_Dot_Term (((bv), (t5)))
end))
in (

let brs1 = (FStar_List.map (fun uu___239_794 -> (match (uu___239_794) with
| (pat, uu____816, t5) -> begin
(

let uu____834 = (inspect_pat pat)
in ((uu____834), (t5)))
end)) brs)
in FStar_Reflection_Data.Tv_Match (((t4), (brs1)))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____839 -> begin
((

let uu____841 = (

let uu____847 = (

let uu____849 = (FStar_Syntax_Print.tag_of_term t3)
in (

let uu____851 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format2 "inspect_ln: outside of expected syntax (%s, %s)\n" uu____849 uu____851)))
in ((FStar_Errors.Warning_CantInspect), (uu____847)))
in (FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____841));
FStar_Reflection_Data.Tv_Unknown;
)
end)))))


let inspect_comp : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.comp_view = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____862) -> begin
FStar_Reflection_Data.C_Total (((t), (FStar_Pervasives_Native.None)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____874 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____874) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, uu____878))::((post, uu____880))::uu____881 -> begin
FStar_Reflection_Data.C_Lemma (((pre), (post)))
end
| uu____924 -> begin
(failwith "inspect_comp: Lemma does not have enough arguments?")
end)
end
| uu____936 -> begin
(

let uu____938 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
in (match (uu____938) with
| true -> begin
(

let maybe_dec = (FStar_List.tryFind (fun uu___240_946 -> (match (uu___240_946) with
| FStar_Syntax_Syntax.DECREASES (uu____948) -> begin
true
end
| uu____952 -> begin
false
end)) ct.FStar_Syntax_Syntax.flags)
in (

let md = (match (maybe_dec) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES (t)) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____962 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.C_Total (((ct.FStar_Syntax_Syntax.result_typ), (md)))))
end
| uu____970 -> begin
FStar_Reflection_Data.C_Unknown
end))
end))
end
| FStar_Syntax_Syntax.GTotal (uu____972) -> begin
FStar_Reflection_Data.C_Unknown
end))


let pack_comp : FStar_Reflection_Data.comp_view  ->  FStar_Syntax_Syntax.comp = (fun cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, uu____988) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Reflection_Data.C_Lemma (pre, post) -> begin
(

let ct = (

let uu____996 = (

let uu____1007 = (FStar_Syntax_Syntax.as_arg pre)
in (

let uu____1016 = (

let uu____1027 = (FStar_Syntax_Syntax.as_arg post)
in (uu____1027)::[])
in (uu____1007)::uu____1016))
in {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Lemma_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit; FStar_Syntax_Syntax.effect_args = uu____996; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp ct))
end
| uu____1060 -> begin
(failwith "cannot pack a C_Unknown")
end))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____1069 = (

let uu____1081 = (FStar_BigInt.string_of_big_int i)
in ((uu____1081), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____1069))
end
| FStar_Reflection_Data.C_True -> begin
FStar_Const.Const_bool (true)
end
| FStar_Reflection_Data.C_False -> begin
FStar_Const.Const_bool (false)
end
| FStar_Reflection_Data.C_String (s) -> begin
FStar_Const.Const_string (((s), (FStar_Range.dummyRange)))
end
| FStar_Reflection_Data.C_Range (r) -> begin
FStar_Const.Const_range (r)
end
| FStar_Reflection_Data.C_Reify -> begin
FStar_Const.Const_reify
end
| FStar_Reflection_Data.C_Reflect (ns) -> begin
(

let uu____1101 = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in FStar_Const.Const_reflect (uu____1101))
end))


let pack_ln : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(FStar_Syntax_Syntax.bv_to_tm bv)
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(FStar_Syntax_Syntax.fv_to_tm fv)
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(

let q' = (pack_aqual q)
in (FStar_Syntax_Util.mk_app l ((((r), (q')))::[])))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(FStar_Syntax_Util.arrow ((b)::[]) c)
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
FStar_Syntax_Util.ktype
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(FStar_Syntax_Util.refine bv t)
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1166 = (

let uu____1173 = (

let uu____1174 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____1174))
in (FStar_Syntax_Syntax.mk uu____1173))
in (uu____1166 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, ctx_u_s) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u_s)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Reflection_Data.Tv_Let (false, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (t2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Let (true, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 [] FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), ((lb)::[]))), (t2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____1243 = (

let uu____1244 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____1244))
in (FStar_All.pipe_left wrap uu____1243))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____1251 = (

let uu____1252 = (

let uu____1266 = (FStar_List.map (fun p1 -> (

let uu____1284 = (pack_pat p1)
in ((uu____1284), (false)))) ps)
in ((fv), (uu____1266)))
in FStar_Syntax_Syntax.Pat_cons (uu____1252))
in (FStar_All.pipe_left wrap uu____1251))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var (bv)))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild (bv)))
end
| FStar_Reflection_Data.Pat_Dot_Term (bv, t1) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_dot_term (((bv), (t1)))))
end))
in (

let brs1 = (FStar_List.map (fun uu___241_1333 -> (match (uu___241_1333) with
| (pat, t1) -> begin
(

let uu____1350 = (pack_pat pat)
in ((uu____1350), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs1)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inl (t)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (((e), (((FStar_Util.Inr (c)), (tacopt))), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
end))


let compare_bv : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  FStar_Order.order = (fun x y -> (

let n1 = (FStar_Syntax_Syntax.order_bv x y)
in (match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Lt
end
| uu____1476 -> begin
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Eq
end
| uu____1481 -> begin
FStar_Order.Gt
end)
end)))


let is_free : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x t -> (FStar_Syntax_Util.is_free_in x t))


let lookup_attr : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv Prims.list = (fun attr env -> (

let uu____1511 = (

let uu____1512 = (FStar_Syntax_Subst.compress attr)
in uu____1512.FStar_Syntax_Syntax.n)
in (match (uu____1511) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let ses = (

let uu____1521 = (

let uu____1523 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.text_of_lid uu____1523))
in (FStar_TypeChecker_Env.lookup_attr env uu____1521))
in (FStar_List.concatMap (fun se -> (

let uu____1527 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____1527) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____1533 = (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) FStar_Pervasives_Native.None)
in (uu____1533)::[])
end))) ses))
end
| uu____1535 -> begin
[]
end)))


let lookup_typ : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (FStar_TypeChecker_Env.lookup_sigelt env lid)))


let sigelt_attrs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.attribute Prims.list = (fun se -> se.FStar_Syntax_Syntax.sigattrs)


let set_sigelt_attrs : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun attrs se -> (

let uu___242_1583 = se
in {FStar_Syntax_Syntax.sigel = uu___242_1583.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___242_1583.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___242_1583.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___242_1583.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}))


let inspect_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Reflection_Data.sigelt_view = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((r, (lb)::[]), uu____1592) -> begin
(

let fv = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv
end
| FStar_Util.Inl (uu____1603) -> begin
(failwith "impossible: global Sig_let has bv")
end)
in (

let uu____1605 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____1605) with
| (s, us) -> begin
(

let typ = (FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef)
in FStar_Reflection_Data.Sg_Let (((r), (fv), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
end)))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, ty, uu____1633, c_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid)
in (

let uu____1644 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____1644) with
| (s, us1) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders s bs)
in (

let ty1 = (FStar_Syntax_Subst.subst s ty)
in (

let uu____1665 = (

let uu____1682 = (FStar_List.map FStar_Ident.path_of_lid c_lids)
in ((nm), (us1), (bs1), (ty1), (uu____1682)))
in FStar_Reflection_Data.Sg_Inductive (uu____1665))))
end)))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, us, ty, uu____1694, n1, uu____1696) -> begin
(

let uu____1703 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____1703) with
| (s, us1) -> begin
(

let ty1 = (FStar_Syntax_Subst.subst s ty)
in (

let uu____1723 = (

let uu____1728 = (FStar_Ident.path_of_lid lid)
in ((uu____1728), (ty1)))
in FStar_Reflection_Data.Sg_Constructor (uu____1723)))
end))
end
| uu____1729 -> begin
FStar_Reflection_Data.Unk
end))


let pack_sigelt : FStar_Reflection_Data.sigelt_view  ->  FStar_Syntax_Syntax.sigelt = (fun sv -> (match (sv) with
| FStar_Reflection_Data.Sg_Let (r, fv, univs1, typ, def) -> begin
(

let s = (FStar_Syntax_Subst.univ_var_closing univs1)
in (

let typ1 = (FStar_Syntax_Subst.subst s typ)
in (

let def1 = (FStar_Syntax_Subst.subst s def)
in (

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr (fv)) univs1 typ1 FStar_Parser_Const.effect_Tot_lid def1 [] def1.FStar_Syntax_Syntax.pos)
in (

let uu____1755 = (

let uu____1756 = (

let uu____1763 = (

let uu____1766 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (uu____1766)::[])
in ((((r), ((lb)::[]))), (uu____1763)))
in FStar_Syntax_Syntax.Sig_let (uu____1756))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____1755))))))
end
| FStar_Reflection_Data.Sg_Constructor (uu____1772) -> begin
(failwith "packing Sg_Constructor, sorry")
end
| FStar_Reflection_Data.Sg_Inductive (uu____1778) -> begin
(failwith "packing Sg_Inductive, sorry")
end
| FStar_Reflection_Data.Unk -> begin
(failwith "packing Unk, sorry")
end))


let inspect_bv : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.bv_view = (fun bv -> (

let uu____1803 = (FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname)
in (

let uu____1805 = (FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index)
in {FStar_Reflection_Data.bv_ppname = uu____1803; FStar_Reflection_Data.bv_index = uu____1805; FStar_Reflection_Data.bv_sort = bv.FStar_Syntax_Syntax.sort})))


let pack_bv : FStar_Reflection_Data.bv_view  ->  FStar_Syntax_Syntax.bv = (fun bvv -> (

let uu____1812 = (FStar_Ident.mk_ident ((bvv.FStar_Reflection_Data.bv_ppname), (FStar_Range.dummyRange)))
in (

let uu____1814 = (FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index)
in {FStar_Syntax_Syntax.ppname = uu____1812; FStar_Syntax_Syntax.index = uu____1814; FStar_Syntax_Syntax.sort = bvv.FStar_Reflection_Data.bv_sort})))


let inspect_binder : FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv) = (fun b -> (

let uu____1830 = b
in (match (uu____1830) with
| (bv, aq) -> begin
(

let uu____1841 = (inspect_aqual aq)
in ((bv), (uu____1841)))
end)))


let pack_binder : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.aqualv  ->  FStar_Syntax_Syntax.binder = (fun bv aqv -> (

let uu____1853 = (pack_aqual aqv)
in ((bv), (uu____1853))))


let moduleof : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list = (fun e -> (FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule))


let binders_of_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders = (fun e -> (FStar_TypeChecker_Env.all_binders e))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let uu____1888 = (FStar_Syntax_Util.un_uinst t1)
in (

let uu____1889 = (FStar_Syntax_Util.un_uinst t2)
in (FStar_Syntax_Util.term_eq uu____1888 uu____1889))))


let term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (FStar_Syntax_Print.term_to_string t))





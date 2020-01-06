
open Prims
open FStar_Pervasives

let env_hook : FStar_TypeChecker_Env.env FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let inspect_aqual : FStar_Syntax_Syntax.aqual  ->  FStar_Reflection_Data.aqualv = (fun aq -> (match (aq) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____12)) -> begin
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

let uu____37 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____37)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (

let fallback = (fun uu____56 -> (

let quals = (

let uu____60 = (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid)
in (match (uu____60) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____65 -> begin
(

let uu____67 = (FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid)
in (match (uu____67) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____72 -> begin
(

let uu____74 = (FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid)
in (match (uu____74) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____79 -> begin
(

let uu____81 = (FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid)
in (match (uu____81) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____86 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
end))
in (

let uu____88 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____88 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) quals))))
in (

let uu____90 = (FStar_ST.op_Bang env_hook)
in (match (uu____90) with
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

let uu____170 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____170 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) quals)))
end
| uu____172 -> begin
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
| (uu____191)::xs -> begin
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

let uu____221 = (init xs)
in (x)::uu____221)
end))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____231) -> begin
(

let uu____246 = (FStar_BigInt.big_int_of_string s)
in FStar_Reflection_Data.C_Int (uu____246))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| FStar_Const.Const_string (s, uu____250) -> begin
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

let uu____255 = (FStar_Ident.path_of_lid l)
in FStar_Reflection_Data.C_Reflect (uu____255))
end
| uu____256 -> begin
(

let uu____257 = (

let uu____259 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____259))
in (failwith uu____257))
end))


let rec inspect_ln : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (

let t3 = (FStar_Syntax_Util.unlazy_emb t2)
in (match (t3.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t4, uu____272) -> begin
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

let uu____330 = (last args)
in (match (uu____330) with
| (a, q) -> begin
(

let q' = (inspect_aqual q)
in (

let uu____358 = (

let uu____363 = (

let uu____364 = (

let uu____369 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____369))
in (uu____364 FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos))
in ((uu____363), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____358)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____378, uu____379) -> begin
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
| FStar_Syntax_Syntax.Tm_type (uu____471) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect_ln: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____492) -> begin
(

let uu____507 = (FStar_Syntax_Util.arrow_one_ln t3)
in (match (uu____507) with
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

let uu____532 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____532))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) -> begin
(

let uu____551 = (

let uu____556 = (

let uu____557 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____557))
in ((uu____556), (((ctx_u), (s)))))
in FStar_Reflection_Data.Tv_Uvar (uu____551))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____587 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____589) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| FStar_Util.Inl (bv) -> begin
FStar_Reflection_Data.Tv_Let (((false), (lb.FStar_Syntax_Syntax.lbattrs), (bv), (lb.FStar_Syntax_Syntax.lbdef), (t21)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_let ((true, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____615 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____617) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| FStar_Util.Inl (bv) -> begin
FStar_Reflection_Data.Tv_Let (((true), (lb.FStar_Syntax_Syntax.lbattrs), (bv), (lb.FStar_Syntax_Syntax.lbdef), (t21)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_match (t4, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____672 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____672))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____693 = (

let uu____705 = (FStar_List.map (fun uu____729 -> (match (uu____729) with
| (p1, b) -> begin
(

let uu____750 = (inspect_pat p1)
in ((uu____750), (b)))
end)) ps)
in ((fv), (uu____705)))
in FStar_Reflection_Data.Pat_Cons (uu____693))
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

let brs1 = (FStar_List.map (fun uu___0_801 -> (match (uu___0_801) with
| (pat, uu____823, t5) -> begin
(

let uu____841 = (inspect_pat pat)
in ((uu____841), (t5)))
end)) brs)
in FStar_Reflection_Data.Tv_Match (((t4), (brs1)))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____846 -> begin
((

let uu____848 = (

let uu____854 = (

let uu____856 = (FStar_Syntax_Print.tag_of_term t3)
in (

let uu____858 = (FStar_Syntax_Print.term_to_string t3)
in (FStar_Util.format2 "inspect_ln: outside of expected syntax (%s, %s)\n" uu____856 uu____858)))
in ((FStar_Errors.Warning_CantInspect), (uu____854)))
in (FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____848));
FStar_Reflection_Data.Tv_Unknown;
)
end)))))


let inspect_comp : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.comp_view = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____869) -> begin
FStar_Reflection_Data.C_Total (((t), (FStar_Pervasives_Native.None)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____881 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____881) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, uu____885))::((post, uu____887))::uu____888 -> begin
FStar_Reflection_Data.C_Lemma (((pre), (post)))
end
| uu____931 -> begin
(failwith "inspect_comp: Lemma does not have enough arguments?")
end)
end
| uu____943 -> begin
(

let uu____945 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
in (match (uu____945) with
| true -> begin
(

let maybe_dec = (FStar_List.tryFind (fun uu___1_953 -> (match (uu___1_953) with
| FStar_Syntax_Syntax.DECREASES (uu____955) -> begin
true
end
| uu____959 -> begin
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
| uu____969 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.C_Total (((ct.FStar_Syntax_Syntax.result_typ), (md)))))
end
| uu____977 -> begin
FStar_Reflection_Data.C_Unknown
end))
end))
end
| FStar_Syntax_Syntax.GTotal (uu____979) -> begin
FStar_Reflection_Data.C_Unknown
end))


let pack_comp : FStar_Reflection_Data.comp_view  ->  FStar_Syntax_Syntax.comp = (fun cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, uu____995) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| FStar_Reflection_Data.C_Lemma (pre, post) -> begin
(

let ct = (

let uu____1003 = (

let uu____1014 = (FStar_Syntax_Syntax.as_arg pre)
in (

let uu____1023 = (

let uu____1034 = (FStar_Syntax_Syntax.as_arg post)
in (uu____1034)::[])
in (uu____1014)::uu____1023))
in {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = FStar_Parser_Const.effect_Lemma_lid; FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit; FStar_Syntax_Syntax.effect_args = uu____1003; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp ct))
end
| uu____1067 -> begin
(failwith "cannot pack a C_Unknown")
end))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____1076 = (

let uu____1088 = (FStar_BigInt.string_of_big_int i)
in ((uu____1088), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____1076))
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

let uu____1108 = (FStar_Ident.lid_of_path ns FStar_Range.dummyRange)
in FStar_Const.Const_reflect (uu____1108))
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

let uu____1173 = (

let uu____1180 = (

let uu____1181 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____1181))
in (FStar_Syntax_Syntax.mk uu____1180))
in (uu____1173 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, ctx_u_s) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (ctx_u_s)) FStar_Pervasives_Native.None FStar_Range.dummyRange)
end
| FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 attrs FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (t2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1 attrs FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((true), ((lb)::[]))), (t2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____1253 = (

let uu____1254 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____1254))
in (FStar_All.pipe_left wrap uu____1253))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____1271 = (

let uu____1272 = (

let uu____1286 = (FStar_List.map (fun uu____1310 -> (match (uu____1310) with
| (p1, b) -> begin
(

let uu____1325 = (pack_pat p1)
in ((uu____1325), (b)))
end)) ps)
in ((fv), (uu____1286)))
in FStar_Syntax_Syntax.Pat_cons (uu____1272))
in (FStar_All.pipe_left wrap uu____1271))
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

let brs1 = (FStar_List.map (fun uu___2_1373 -> (match (uu___2_1373) with
| (pat, t1) -> begin
(

let uu____1390 = (pack_pat pat)
in ((uu____1390), (FStar_Pervasives_Native.None), (t1)))
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
| uu____1516 -> begin
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Eq
end
| uu____1521 -> begin
FStar_Order.Gt
end)
end)))


let is_free : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x t -> (FStar_Syntax_Util.is_free_in x t))


let lookup_attr : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv Prims.list = (fun attr env -> (

let uu____1551 = (

let uu____1552 = (FStar_Syntax_Subst.compress attr)
in uu____1552.FStar_Syntax_Syntax.n)
in (match (uu____1551) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let ses = (

let uu____1561 = (

let uu____1563 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.text_of_lid uu____1563))
in (FStar_TypeChecker_Env.lookup_attr env uu____1561))
in (FStar_List.concatMap (fun se -> (

let uu____1567 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____1567) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (l) -> begin
(

let uu____1573 = (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) FStar_Pervasives_Native.None)
in (uu____1573)::[])
end))) ses))
end
| uu____1575 -> begin
[]
end)))


let all_defs_in_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.fv Prims.list = (fun env -> (

let uu____1586 = (FStar_TypeChecker_Env.lidents env)
in (FStar_List.map (fun l -> (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) FStar_Pervasives_Native.None)) uu____1586)))


let defs_in_module : FStar_TypeChecker_Env.env  ->  FStar_Reflection_Data.name  ->  FStar_Syntax_Syntax.fv Prims.list = (fun env modul -> (

let uu____1607 = (FStar_TypeChecker_Env.lidents env)
in (FStar_List.concatMap (fun l -> (

let ns = (

let uu____1615 = (

let uu____1618 = (FStar_Ident.ids_of_lid l)
in (FStar_All.pipe_right uu____1618 init))
in (FStar_All.pipe_right uu____1615 (FStar_List.map FStar_Ident.string_of_ident)))
in (match ((Prims.op_Equality ns modul)) with
| true -> begin
(

let uu____1631 = (FStar_Syntax_Syntax.lid_as_fv l (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "999"))) FStar_Pervasives_Native.None)
in (uu____1631)::[])
end
| uu____1633 -> begin
[]
end))) uu____1607)))


let lookup_typ : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (FStar_TypeChecker_Env.lookup_sigelt env lid)))


let sigelt_attrs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.attribute Prims.list = (fun se -> se.FStar_Syntax_Syntax.sigattrs)


let set_sigelt_attrs : FStar_Syntax_Syntax.attribute Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun attrs se -> (

let uu___376_1682 = se
in {FStar_Syntax_Syntax.sigel = uu___376_1682.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___376_1682.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___376_1682.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___376_1682.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs; FStar_Syntax_Syntax.sigopts = uu___376_1682.FStar_Syntax_Syntax.sigopts}))


let rd_to_syntax_qual : FStar_Reflection_Data.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun uu___3_1688 -> (match (uu___3_1688) with
| FStar_Reflection_Data.Assumption -> begin
FStar_Syntax_Syntax.Assumption
end
| FStar_Reflection_Data.New -> begin
FStar_Syntax_Syntax.New
end
| FStar_Reflection_Data.Private -> begin
FStar_Syntax_Syntax.Private
end
| FStar_Reflection_Data.Unfold_for_unification_and_vcgen -> begin
FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
end
| FStar_Reflection_Data.Visible_default -> begin
FStar_Syntax_Syntax.Visible_default
end
| FStar_Reflection_Data.Irreducible -> begin
FStar_Syntax_Syntax.Irreducible
end
| FStar_Reflection_Data.Abstract -> begin
FStar_Syntax_Syntax.Abstract
end
| FStar_Reflection_Data.Inline_for_extraction -> begin
FStar_Syntax_Syntax.Inline_for_extraction
end
| FStar_Reflection_Data.NoExtract -> begin
FStar_Syntax_Syntax.NoExtract
end
| FStar_Reflection_Data.Noeq -> begin
FStar_Syntax_Syntax.Noeq
end
| FStar_Reflection_Data.Unopteq -> begin
FStar_Syntax_Syntax.Unopteq
end
| FStar_Reflection_Data.TotalEffect -> begin
FStar_Syntax_Syntax.TotalEffect
end
| FStar_Reflection_Data.Logic -> begin
FStar_Syntax_Syntax.Logic
end
| FStar_Reflection_Data.Reifiable -> begin
FStar_Syntax_Syntax.Reifiable
end
| FStar_Reflection_Data.Reflectable (l) -> begin
FStar_Syntax_Syntax.Reflectable (l)
end
| FStar_Reflection_Data.Discriminator (l) -> begin
FStar_Syntax_Syntax.Discriminator (l)
end
| FStar_Reflection_Data.Projector (l, i) -> begin
FStar_Syntax_Syntax.Projector (((l), (i)))
end
| FStar_Reflection_Data.RecordType (l1, l2) -> begin
FStar_Syntax_Syntax.RecordType (((l1), (l2)))
end
| FStar_Reflection_Data.RecordConstructor (l1, l2) -> begin
FStar_Syntax_Syntax.RecordConstructor (((l1), (l2)))
end
| FStar_Reflection_Data.Action (l) -> begin
FStar_Syntax_Syntax.Action (l)
end
| FStar_Reflection_Data.ExceptionConstructor -> begin
FStar_Syntax_Syntax.ExceptionConstructor
end
| FStar_Reflection_Data.HasMaskedEffect -> begin
FStar_Syntax_Syntax.HasMaskedEffect
end
| FStar_Reflection_Data.Effect -> begin
FStar_Syntax_Syntax.Effect
end
| FStar_Reflection_Data.OnlyName -> begin
FStar_Syntax_Syntax.OnlyName
end))


let syntax_to_rd_qual : FStar_Syntax_Syntax.qualifier  ->  FStar_Reflection_Data.qualifier = (fun uu___4_1727 -> (match (uu___4_1727) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Reflection_Data.Assumption
end
| FStar_Syntax_Syntax.New -> begin
FStar_Reflection_Data.New
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Reflection_Data.Private
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
FStar_Reflection_Data.Unfold_for_unification_and_vcgen
end
| FStar_Syntax_Syntax.Visible_default -> begin
FStar_Reflection_Data.Visible_default
end
| FStar_Syntax_Syntax.Irreducible -> begin
FStar_Reflection_Data.Irreducible
end
| FStar_Syntax_Syntax.Abstract -> begin
FStar_Reflection_Data.Abstract
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
FStar_Reflection_Data.Inline_for_extraction
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Reflection_Data.NoExtract
end
| FStar_Syntax_Syntax.Noeq -> begin
FStar_Reflection_Data.Noeq
end
| FStar_Syntax_Syntax.Unopteq -> begin
FStar_Reflection_Data.Unopteq
end
| FStar_Syntax_Syntax.TotalEffect -> begin
FStar_Reflection_Data.TotalEffect
end
| FStar_Syntax_Syntax.Logic -> begin
FStar_Reflection_Data.Logic
end
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Reflection_Data.Reifiable
end
| FStar_Syntax_Syntax.Reflectable (l) -> begin
FStar_Reflection_Data.Reflectable (l)
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
FStar_Reflection_Data.Discriminator (l)
end
| FStar_Syntax_Syntax.Projector (l, i) -> begin
FStar_Reflection_Data.Projector (((l), (i)))
end
| FStar_Syntax_Syntax.RecordType (l1, l2) -> begin
FStar_Reflection_Data.RecordType (((l1), (l2)))
end
| FStar_Syntax_Syntax.RecordConstructor (l1, l2) -> begin
FStar_Reflection_Data.RecordConstructor (((l1), (l2)))
end
| FStar_Syntax_Syntax.Action (l) -> begin
FStar_Reflection_Data.Action (l)
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
FStar_Reflection_Data.ExceptionConstructor
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
FStar_Reflection_Data.HasMaskedEffect
end
| FStar_Syntax_Syntax.Effect -> begin
FStar_Reflection_Data.Effect
end
| FStar_Syntax_Syntax.OnlyName -> begin
FStar_Reflection_Data.OnlyName
end))


let sigelt_quals : FStar_Syntax_Syntax.sigelt  ->  FStar_Reflection_Data.qualifier Prims.list = (fun se -> (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.map syntax_to_rd_qual)))


let set_sigelt_quals : FStar_Reflection_Data.qualifier Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun quals se -> (

let uu___455_1790 = se
in (

let uu____1791 = (FStar_List.map rd_to_syntax_qual quals)
in {FStar_Syntax_Syntax.sigel = uu___455_1790.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___455_1790.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu____1791; FStar_Syntax_Syntax.sigmeta = uu___455_1790.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___455_1790.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___455_1790.FStar_Syntax_Syntax.sigopts})))


let e_optionstate_hook : FStar_Options.optionstate FStar_Syntax_Embeddings.embedding FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let sigelt_opts : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigopts) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (o) -> begin
(

let uu____1824 = (

let uu____1825 = (

let uu____1832 = (

let uu____1835 = (FStar_ST.op_Bang e_optionstate_hook)
in (FStar_All.pipe_right uu____1835 FStar_Util.must))
in (FStar_Syntax_Embeddings.embed uu____1832 o))
in (uu____1825 FStar_Range.dummyRange FStar_Pervasives_Native.None FStar_Syntax_Embeddings.id_norm_cb))
in FStar_Pervasives_Native.Some (uu____1824))
end))


let inspect_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Reflection_Data.sigelt_view = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((r, (lb)::[]), uu____1885) -> begin
(

let fv = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv
end
| FStar_Util.Inl (uu____1896) -> begin
(failwith "impossible: global Sig_let has bv")
end)
in (

let uu____1898 = (FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs)
in (match (uu____1898) with
| (s, us) -> begin
(

let typ = (FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp)
in (

let def = (FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef)
in FStar_Reflection_Data.Sg_Let (((r), (fv), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef)))))
end)))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, ty, uu____1926, c_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid)
in (

let uu____1937 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____1937) with
| (s, us1) -> begin
(

let bs1 = (FStar_Syntax_Subst.subst_binders s bs)
in (

let ty1 = (FStar_Syntax_Subst.subst s ty)
in (

let uu____1958 = (

let uu____1975 = (FStar_List.map FStar_Ident.path_of_lid c_lids)
in ((nm), (us1), (bs1), (ty1), (uu____1975)))
in FStar_Reflection_Data.Sg_Inductive (uu____1958))))
end)))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, us, ty, uu____1987, n1, uu____1989) -> begin
(

let uu____1996 = (FStar_Syntax_Subst.univ_var_opening us)
in (match (uu____1996) with
| (s, us1) -> begin
(

let ty1 = (FStar_Syntax_Subst.subst s ty)
in (

let uu____2016 = (

let uu____2021 = (FStar_Ident.path_of_lid lid)
in ((uu____2021), (ty1)))
in FStar_Reflection_Data.Sg_Constructor (uu____2016)))
end))
end
| uu____2022 -> begin
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

let uu____2048 = (

let uu____2049 = (

let uu____2056 = (

let uu____2059 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (uu____2059)::[])
in ((((r), ((lb)::[]))), (uu____2056)))
in FStar_Syntax_Syntax.Sig_let (uu____2049))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____2048))))))
end
| FStar_Reflection_Data.Sg_Constructor (uu____2065) -> begin
(failwith "packing Sg_Constructor, sorry")
end
| FStar_Reflection_Data.Sg_Inductive (uu____2071) -> begin
(failwith "packing Sg_Inductive, sorry")
end
| FStar_Reflection_Data.Unk -> begin
(failwith "packing Unk, sorry")
end))


let inspect_bv : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.bv_view = (fun bv -> (

let uu____2096 = (FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname)
in (

let uu____2098 = (FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index)
in {FStar_Reflection_Data.bv_ppname = uu____2096; FStar_Reflection_Data.bv_index = uu____2098; FStar_Reflection_Data.bv_sort = bv.FStar_Syntax_Syntax.sort})))


let pack_bv : FStar_Reflection_Data.bv_view  ->  FStar_Syntax_Syntax.bv = (fun bvv -> (

let uu____2105 = (FStar_Ident.mk_ident ((bvv.FStar_Reflection_Data.bv_ppname), (FStar_Range.dummyRange)))
in (

let uu____2107 = (FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index)
in {FStar_Syntax_Syntax.ppname = uu____2105; FStar_Syntax_Syntax.index = uu____2107; FStar_Syntax_Syntax.sort = bvv.FStar_Reflection_Data.bv_sort})))


let inspect_binder : FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv) = (fun b -> (

let uu____2123 = b
in (match (uu____2123) with
| (bv, aq) -> begin
(

let uu____2134 = (inspect_aqual aq)
in ((bv), (uu____2134)))
end)))


let pack_binder : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.aqualv  ->  FStar_Syntax_Syntax.binder = (fun bv aqv -> (

let uu____2146 = (pack_aqual aqv)
in ((bv), (uu____2146))))


let moduleof : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list = (fun e -> (FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule))


let env_open_modules : FStar_TypeChecker_Env.env  ->  FStar_Reflection_Data.name Prims.list = (fun e -> (

let uu____2173 = (FStar_Syntax_DsEnv.open_modules e.FStar_TypeChecker_Env.dsenv)
in (FStar_List.map (fun uu____2191 -> (match (uu____2191) with
| (l, m) -> begin
(

let uu____2201 = (FStar_Ident.ids_of_lid l)
in (FStar_List.map FStar_Ident.text_of_id uu____2201))
end)) uu____2173)))


let binders_of_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders = (fun e -> (FStar_TypeChecker_Env.all_binders e))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let uu____2223 = (FStar_Syntax_Util.un_uinst t1)
in (

let uu____2224 = (FStar_Syntax_Util.un_uinst t2)
in (FStar_Syntax_Util.term_eq uu____2223 uu____2224))))


let term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (FStar_Syntax_Print.term_to_string t))


let comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (FStar_Syntax_Print.comp_to_string c))





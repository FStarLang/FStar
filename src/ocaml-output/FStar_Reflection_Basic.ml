
open Prims
open FStar_Pervasives

let inspect_aqual : FStar_Syntax_Syntax.aqual  ->  FStar_Reflection_Data.aqualv = (fun aq -> (match (aq) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____6)) -> begin
FStar_Reflection_Data.Q_Implicit
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
end))


let inspect_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (

let uu____21 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____21)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (

let attr = (

let uu____35 = (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid)
in (match (uu____35) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____38 -> begin
(

let uu____39 = (FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid)
in (match (uu____39) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____42 -> begin
(

let uu____43 = (FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid)
in (match (uu____43) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____46 -> begin
(

let uu____47 = (FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid)
in (match (uu____47) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)
end
| uu____50 -> begin
FStar_Pervasives_Native.None
end))
end))
end))
end))
in (

let uu____51 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____51 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "999"))) attr)))))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____68)::xs -> begin
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

let uu____96 = (init xs)
in (x)::uu____96)
end))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____105) -> begin
(

let uu____118 = (FStar_BigInt.big_int_of_string s)
in FStar_Reflection_Data.C_Int (uu____118))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| FStar_Const.Const_string (s, uu____120) -> begin
FStar_Reflection_Data.C_String (s)
end
| uu____121 -> begin
(

let uu____122 = (

let uu____123 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____123))
in (failwith uu____122))
end))


let rec inspect_ln : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let t2 = (FStar_Syntax_Util.un_uinst t1)
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t3, uu____132) -> begin
(inspect_ln t3)
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

let uu____181 = (last args)
in (match (uu____181) with
| (a, q) -> begin
(

let q' = (inspect_aqual q)
in (

let uu____201 = (

let uu____206 = (

let uu____207 = (

let uu____212 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____212))
in (uu____207 FStar_Pervasives_Native.None t2.FStar_Syntax_Syntax.pos))
in ((uu____206), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____201)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____223, uu____224) -> begin
(failwith "inspect_ln: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs ((b)::bs, t3, k) -> begin
(

let body = (match (bs) with
| [] -> begin
t3
end
| bs1 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs1), (t3), (k)))) FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos)
end)
in FStar_Reflection_Data.Tv_Abs (((b), (body))))
end
| FStar_Syntax_Syntax.Tm_type (uu____301) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect_ln: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (uu____317) -> begin
(

let uu____330 = (FStar_Syntax_Util.arrow_one t2)
in (match (uu____330) with
| FStar_Pervasives_Native.Some (b, c) -> begin
FStar_Reflection_Data.Tv_Arrow (((b), (c)))
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t3) -> begin
FStar_Reflection_Data.Tv_Refine (((bv), (t3)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____354 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____354))
end
| FStar_Syntax_Syntax.Tm_uvar (ctx_u) -> begin
(

let uu____356 = (

let uu____365 = (

let uu____366 = (FStar_Syntax_Unionfind.uvar_id ctx_u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_BigInt.of_int_fs uu____366))
in ((uu____365), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders), (ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)))
in FStar_Reflection_Data.Tv_Uvar (uu____356))
end
| FStar_Syntax_Syntax.Tm_let ((false, (lb)::[]), t21) -> begin
(match ((Prims.op_disEquality lb.FStar_Syntax_Syntax.lbunivs [])) with
| true -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____383 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____384) -> begin
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
| uu____402 -> begin
(match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (uu____403) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| FStar_Util.Inl (bv) -> begin
FStar_Reflection_Data.Tv_Let (((true), (bv), (lb.FStar_Syntax_Syntax.lbdef), (t21)))
end)
end)
end
| FStar_Syntax_Syntax.Tm_match (t3, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____454 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____454))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____473 = (

let uu____480 = (FStar_List.map (fun uu____492 -> (match (uu____492) with
| (p1, uu____500) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____480)))
in FStar_Reflection_Data.Pat_Cons (uu____473))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, t4) -> begin
FStar_Reflection_Data.Pat_Dot_Term (((bv), (t4)))
end))
in (

let brs1 = (FStar_List.map (fun uu___58_549 -> (match (uu___58_549) with
| (pat, uu____571, t4) -> begin
(

let uu____589 = (inspect_pat pat)
in ((uu____589), (t4)))
end)) brs)
in FStar_Reflection_Data.Tv_Match (((t3), (brs1)))))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____594 -> begin
((

let uu____596 = (

let uu____601 = (

let uu____602 = (FStar_Syntax_Print.tag_of_term t2)
in (

let uu____603 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.format2 "inspect_ln: outside of expected syntax (%s, %s)\n" uu____602 uu____603)))
in ((FStar_Errors.Warning_CantInspect), (uu____601)))
in (FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu____596));
FStar_Reflection_Data.Tv_Unknown;
)
end))))


let inspect_comp : FStar_Syntax_Syntax.comp  ->  FStar_Reflection_Data.comp_view = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____610) -> begin
FStar_Reflection_Data.C_Total (((t), (FStar_Pervasives_Native.None)))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(

let uu____622 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____622) with
| true -> begin
(match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, uu____624))::((post, uu____626))::uu____627 -> begin
FStar_Reflection_Data.C_Lemma (((pre), (post)))
end
| uu____656 -> begin
(failwith "inspect_comp: Lemma does not have enough arguments?")
end)
end
| uu____665 -> begin
(

let uu____666 = (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Tot_lid)
in (match (uu____666) with
| true -> begin
(

let maybe_dec = (FStar_List.tryFind (fun uu___59_672 -> (match (uu___59_672) with
| FStar_Syntax_Syntax.DECREASES (uu____673) -> begin
true
end
| uu____676 -> begin
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
| uu____693 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.C_Total (((ct.FStar_Syntax_Syntax.result_typ), (md)))))
end
| uu____702 -> begin
FStar_Reflection_Data.C_Unknown
end))
end))
end
| FStar_Syntax_Syntax.GTotal (uu____703) -> begin
FStar_Reflection_Data.C_Unknown
end))


let pack_comp : FStar_Reflection_Data.comp_view  ->  FStar_Syntax_Syntax.comp = (fun cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, uu____718) -> begin
(FStar_Syntax_Syntax.mk_Total t)
end
| uu____723 -> begin
(failwith "sorry, can embed comp_views other than C_Total for now")
end))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____730 = (

let uu____741 = (FStar_BigInt.string_of_big_int i)
in ((uu____741), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____730))
end
| FStar_Reflection_Data.C_True -> begin
FStar_Const.Const_bool (true)
end
| FStar_Reflection_Data.C_False -> begin
FStar_Const.Const_bool (false)
end
| FStar_Reflection_Data.C_String (s) -> begin
FStar_Const.Const_string (((s), (FStar_Range.dummyRange)))
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

let uu____800 = (

let uu____807 = (

let uu____808 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____808))
in (FStar_Syntax_Syntax.mk uu____807))
in (uu____800 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, g, bs, t) -> begin
(

let uu____816 = (FStar_BigInt.to_int_fs u)
in (FStar_Syntax_Util.uvar_from_id uu____816 ((g), (bs), (t))))
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

let uu____880 = (

let uu____881 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____881))
in (FStar_All.pipe_left wrap uu____880))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____890 = (

let uu____891 = (

let uu____904 = (FStar_List.map (fun p1 -> (

let uu____920 = (pack_pat p1)
in ((uu____920), (false)))) ps)
in ((fv), (uu____904)))
in FStar_Syntax_Syntax.Pat_cons (uu____891))
in (FStar_All.pipe_left wrap uu____890))
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

let brs1 = (FStar_List.map (fun uu___60_974 -> (match (uu___60_974) with
| (pat, t1) -> begin
(

let uu____991 = (pack_pat pat)
in ((uu____991), (FStar_Pervasives_Native.None), (t1)))
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
| uu____1101 -> begin
(match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Eq
end
| uu____1102 -> begin
FStar_Order.Gt
end)
end)))


let is_free : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x t -> (FStar_Syntax_Util.is_free_in x t))


let lookup_typ : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (

let uu____1132 = (FStar_TypeChecker_Env.lookup_qname env lid)
in (match (uu____1132) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____1153), rng) -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
FStar_Pervasives_Native.Some (se)
end))))


let inspect_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Reflection_Data.sigelt_view = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((r, (lb)::[]), uu____1257) -> begin
(

let fv = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
fv
end
| FStar_Util.Inl (uu____1266) -> begin
(failwith "global Sig_let has bv")
end)
in FStar_Reflection_Data.Sg_Let (((r), (fv), (lb.FStar_Syntax_Syntax.lbtyp), (lb.FStar_Syntax_Syntax.lbdef))))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, us, bs, t, uu____1271, c_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid)
in (

let uu____1282 = (

let uu____1295 = (FStar_List.map FStar_Ident.path_of_lid c_lids)
in ((nm), (bs), (t), (uu____1295)))
in FStar_Reflection_Data.Sg_Inductive (uu____1282)))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, us, t, uu____1305, n1, uu____1307) -> begin
(

let uu____1312 = (

let uu____1317 = (FStar_Ident.path_of_lid lid)
in ((uu____1317), (t)))
in FStar_Reflection_Data.Sg_Constructor (uu____1312))
end
| uu____1318 -> begin
FStar_Reflection_Data.Unk
end))


let pack_sigelt : FStar_Reflection_Data.sigelt_view  ->  FStar_Syntax_Syntax.sigelt = (fun sv -> (match (sv) with
| FStar_Reflection_Data.Sg_Let (r, fv, ty, def) -> begin
(

let lb = (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr (fv)) [] ty FStar_Parser_Const.effect_Tot_lid def [] def.FStar_Syntax_Syntax.pos)
in (

let uu____1331 = (

let uu____1332 = (

let uu____1339 = (

let uu____1342 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (uu____1342)::[])
in ((((r), ((lb)::[]))), (uu____1339)))
in FStar_Syntax_Syntax.Sig_let (uu____1332))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____1331)))
end
| FStar_Reflection_Data.Sg_Constructor (uu____1347) -> begin
(failwith "packing Sg_Constructor, sorry")
end
| FStar_Reflection_Data.Sg_Inductive (uu____1352) -> begin
(failwith "packing Sg_Inductive, sorry")
end
| FStar_Reflection_Data.Unk -> begin
(failwith "packing Unk, sorry")
end))


let inspect_bv : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.bv_view = (fun bv -> (

let uu____1370 = (FStar_Ident.string_of_ident bv.FStar_Syntax_Syntax.ppname)
in (

let uu____1371 = (FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index)
in {FStar_Reflection_Data.bv_ppname = uu____1370; FStar_Reflection_Data.bv_index = uu____1371; FStar_Reflection_Data.bv_sort = bv.FStar_Syntax_Syntax.sort})))


let pack_bv : FStar_Reflection_Data.bv_view  ->  FStar_Syntax_Syntax.bv = (fun bvv -> (

let uu____1377 = (FStar_Ident.mk_ident ((bvv.FStar_Reflection_Data.bv_ppname), (FStar_Range.dummyRange)))
in (

let uu____1378 = (FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index)
in {FStar_Syntax_Syntax.ppname = uu____1377; FStar_Syntax_Syntax.index = uu____1378; FStar_Syntax_Syntax.sort = bvv.FStar_Reflection_Data.bv_sort})))


let inspect_binder : FStar_Syntax_Syntax.binder  ->  (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv) = (fun b -> (

let uu____1392 = b
in (match (uu____1392) with
| (bv, aq) -> begin
(

let uu____1399 = (inspect_aqual aq)
in ((bv), (uu____1399)))
end)))


let pack_binder : FStar_Syntax_Syntax.bv  ->  FStar_Reflection_Data.aqualv  ->  FStar_Syntax_Syntax.binder = (fun bv aqv -> (

let uu____1410 = (pack_aqual aqv)
in ((bv), (uu____1410))))


let moduleof : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list = (fun e -> (FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule))


let binders_of_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders = (fun e -> (FStar_TypeChecker_Env.all_binders e))


let term_eq : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t1 t2 -> (

let uu____1435 = (FStar_Syntax_Util.un_uinst t1)
in (

let uu____1436 = (FStar_Syntax_Util.un_uinst t2)
in (FStar_Syntax_Util.term_eq uu____1435 uu____1436))))


let term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (FStar_Syntax_Print.term_to_string t))





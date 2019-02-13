
open Prims
open FStar_Pervasives

let mkFV : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun fv us ts -> (FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us) (FStar_List.rev ts)))


let mkConstruct : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun fv us ts -> (FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us) (FStar_List.rev ts)))


let fv_as_emb_typ : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.emb_typ = (fun fv -> (

let uu____78 = (

let uu____86 = (FStar_Ident.string_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((uu____86), ([])))
in FStar_Syntax_Syntax.ET_app (uu____78)))


let mk_emb' : 'Auu____100 . (FStar_TypeChecker_NBETerm.nbe_cbs  ->  'Auu____100  ->  FStar_TypeChecker_NBETerm.t)  ->  (FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.t  ->  'Auu____100 FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.fv  ->  'Auu____100 FStar_TypeChecker_NBETerm.embedding = (fun x y fv -> (

let uu____142 = (mkFV fv [] [])
in (

let uu____147 = (fv_as_emb_typ fv)
in (FStar_TypeChecker_NBETerm.mk_emb x y uu____142 uu____147))))


let mk_lazy : 'Auu____159 . FStar_TypeChecker_NBETerm.nbe_cbs  ->  'Auu____159  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lazy_kind  ->  FStar_TypeChecker_NBETerm.t = (fun cb obj ty kind -> (

let li = (

let uu____185 = (FStar_Dyn.mkdyn obj)
in {FStar_Syntax_Syntax.blob = uu____185; FStar_Syntax_Syntax.lkind = kind; FStar_Syntax_Syntax.ltyp = ty; FStar_Syntax_Syntax.rng = FStar_Range.dummyRange})
in (

let thunk1 = (FStar_Common.mk_thunk (fun uu____191 -> (

let uu____192 = (FStar_Syntax_Util.unfold_lazy li)
in (FStar_TypeChecker_NBETerm.translate_cb cb uu____192))))
in FStar_TypeChecker_NBETerm.Lazy (((FStar_Util.Inl (li)), (thunk1))))))


let e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding = (

let embed_bv = (fun cb bv -> (mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv FStar_Syntax_Syntax.Lazy_bv))
in (

let unembed_bv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv; FStar_Syntax_Syntax.ltyp = uu____277; FStar_Syntax_Syntax.rng = uu____278}), uu____279) -> begin
(

let uu____298 = (FStar_Dyn.undyn b)
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____298))
end
| uu____301 -> begin
((

let uu____303 = (

let uu____309 = (

let uu____311 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded bv: %s" uu____311))
in ((FStar_Errors.Warning_NotEmbedded), (uu____309)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____303));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv)))


let e_binder : FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding = (

let embed_binder = (fun cb b -> (mk_lazy cb b FStar_Reflection_Data.fstar_refl_binder FStar_Syntax_Syntax.Lazy_binder))
in (

let unembed_binder = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder; FStar_Syntax_Syntax.ltyp = uu____345; FStar_Syntax_Syntax.rng = uu____346}), uu____347) -> begin
(

let uu____366 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____366))
end
| uu____367 -> begin
((

let uu____369 = (

let uu____375 = (

let uu____377 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded binder: %s" uu____377))
in ((FStar_Errors.Warning_NotEmbedded), (uu____375)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____369));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_binder unembed_binder FStar_Reflection_Data.fstar_refl_binder_fv)))


let rec mapM_opt : 'a 'b . ('a  ->  'b FStar_Pervasives_Native.option)  ->  'a Prims.list  ->  'b Prims.list FStar_Pervasives_Native.option = (fun f l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (x)::xs -> begin
(

let uu____427 = (f x)
in (FStar_Util.bind_opt uu____427 (fun x1 -> (

let uu____435 = (mapM_opt f xs)
in (FStar_Util.bind_opt uu____435 (fun xs1 -> FStar_Pervasives_Native.Some ((x1)::xs1)))))))
end))


let e_term_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let embed_term = (fun cb t -> (

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aq}
in FStar_TypeChecker_NBETerm.Quote (((t), (qi)))))
in (

let rec unembed_term = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Quote (tm, qi) -> begin
FStar_Pervasives_Native.Some (tm)
end
| uu____505 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____506 = (mkFV FStar_Reflection_Data.fstar_refl_term_fv [] [])
in (

let uu____511 = (fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv)
in {FStar_TypeChecker_NBETerm.em = embed_term; FStar_TypeChecker_NBETerm.un = unembed_term; FStar_TypeChecker_NBETerm.typ = uu____506; FStar_TypeChecker_NBETerm.emb_typ = uu____511})))))


let e_term : FStar_Syntax_Syntax.term FStar_TypeChecker_NBETerm.embedding = (e_term_aq [])


let e_aqualv : FStar_Reflection_Data.aqualv FStar_TypeChecker_NBETerm.embedding = (

let embed_aqualv = (fun cb q -> (match (q) with
| FStar_Reflection_Data.Q_Explicit -> begin
(mkConstruct FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.Q_Implicit -> begin
(mkConstruct FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.Q_Meta (t) -> begin
(

let uu____544 = (

let uu____551 = (

let uu____556 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____556))
in (uu____551)::[])
in (mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv [] uu____544))
end))
in (

let unembed_aqualv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Explicit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Implicit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((t1, uu____608))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid) -> begin
(

let uu____625 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____625 (fun t2 -> FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta (t2)))))
end
| uu____630 -> begin
((

let uu____632 = (

let uu____638 = (

let uu____640 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded aqualv: %s" uu____640))
in ((FStar_Errors.Warning_NotEmbedded), (uu____638)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____632));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____644 = (mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [])
in (

let uu____649 = (fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv)
in (FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____644 uu____649)))))


let e_binders : FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_binder)


let e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding = (

let embed_fv = (fun cb fv -> (mk_lazy cb fv FStar_Reflection_Data.fstar_refl_fv FStar_Syntax_Syntax.Lazy_fvar))
in (

let unembed_fv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar; FStar_Syntax_Syntax.ltyp = uu____683; FStar_Syntax_Syntax.rng = uu____684}), uu____685) -> begin
(

let uu____704 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____704))
end
| uu____705 -> begin
((

let uu____707 = (

let uu____713 = (

let uu____715 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded fvar: %s" uu____715))
in ((FStar_Errors.Warning_NotEmbedded), (uu____713)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____707));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv)))


let e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding = (

let embed_comp = (fun cb c -> (mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp FStar_Syntax_Syntax.Lazy_comp))
in (

let unembed_comp = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp; FStar_Syntax_Syntax.ltyp = uu____749; FStar_Syntax_Syntax.rng = uu____750}), uu____751) -> begin
(

let uu____770 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____770))
end
| uu____771 -> begin
((

let uu____773 = (

let uu____779 = (

let uu____781 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded comp: %s" uu____781))
in ((FStar_Errors.Warning_NotEmbedded), (uu____779)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____773));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv)))


let e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding = (

let embed_env = (fun cb e -> (mk_lazy cb e FStar_Reflection_Data.fstar_refl_env FStar_Syntax_Syntax.Lazy_env))
in (

let unembed_env = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env; FStar_Syntax_Syntax.ltyp = uu____815; FStar_Syntax_Syntax.rng = uu____816}), uu____817) -> begin
(

let uu____836 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____836))
end
| uu____837 -> begin
((

let uu____839 = (

let uu____845 = (

let uu____847 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded env: %s" uu____847))
in ((FStar_Errors.Warning_NotEmbedded), (uu____845)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____839));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_env unembed_env FStar_Reflection_Data.fstar_refl_env_fv)))


let e_const : FStar_Reflection_Data.vconst FStar_TypeChecker_NBETerm.embedding = (

let embed_const = (fun cb c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
(mkConstruct FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.C_True -> begin
(mkConstruct FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.C_False -> begin
(mkConstruct FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____878 = (

let uu____885 = (FStar_TypeChecker_NBETerm.as_arg (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i))))
in (uu____885)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv [] uu____878))
end
| FStar_Reflection_Data.C_String (s) -> begin
(

let uu____900 = (

let uu____907 = (

let uu____912 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string cb s)
in (FStar_TypeChecker_NBETerm.as_arg uu____912))
in (uu____907)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv [] uu____900))
end
| FStar_Reflection_Data.C_Range (r) -> begin
(

let uu____923 = (

let uu____930 = (

let uu____935 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_range cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____935))
in (uu____930)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv [] uu____923))
end
| FStar_Reflection_Data.C_Reify -> begin
(mkConstruct FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.C_Reflect (ns) -> begin
(

let uu____949 = (

let uu____956 = (

let uu____961 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string_list cb ns)
in (FStar_TypeChecker_NBETerm.as_arg uu____961))
in (uu____956)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.fv [] uu____949))
end))
in (

let unembed_const = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_Unit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_True)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_False)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((i, uu____1029))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid) -> begin
(

let uu____1046 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb i)
in (FStar_Util.bind_opt uu____1046 (fun i1 -> (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) (FStar_Reflection_Data.C_Int (i1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((s, uu____1055))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid) -> begin
(

let uu____1072 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_string cb s)
in (FStar_Util.bind_opt uu____1072 (fun s1 -> (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) (FStar_Reflection_Data.C_String (s1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((r, uu____1085))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid) -> begin
(

let uu____1102 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range cb r)
in (FStar_Util.bind_opt uu____1102 (fun r1 -> (FStar_All.pipe_left (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4)) (FStar_Reflection_Data.C_Range (r1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Reify.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_Reify)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((ns, uu____1124))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Reflect.FStar_Reflection_Data.lid) -> begin
(

let uu____1141 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_string_list cb ns)
in (FStar_Util.bind_opt uu____1141 (fun ns1 -> (FStar_All.pipe_left (fun _0_5 -> FStar_Pervasives_Native.Some (_0_5)) (FStar_Reflection_Data.C_Reflect (ns1))))))
end
| uu____1160 -> begin
((

let uu____1162 = (

let uu____1168 = (

let uu____1170 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded vconst: %s" uu____1170))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1168)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1162));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst_fv)))


let rec e_pattern' : unit  ->  FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding = (fun uu____1181 -> (

let embed_pattern = (fun cb p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____1194 = (

let uu____1201 = (

let uu____1206 = (FStar_TypeChecker_NBETerm.embed e_const cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1206))
in (uu____1201)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv [] uu____1194))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____1221 = (

let uu____1228 = (

let uu____1233 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1233))
in (

let uu____1234 = (

let uu____1241 = (

let uu____1246 = (

let uu____1247 = (

let uu____1252 = (e_pattern' ())
in (FStar_TypeChecker_NBETerm.e_list uu____1252))
in (FStar_TypeChecker_NBETerm.embed uu____1247 cb ps))
in (FStar_TypeChecker_NBETerm.as_arg uu____1246))
in (uu____1241)::[])
in (uu____1228)::uu____1234))
in (mkConstruct FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv [] uu____1221))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____1270 = (

let uu____1277 = (

let uu____1282 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1282))
in (uu____1277)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv [] uu____1270))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____1292 = (

let uu____1299 = (

let uu____1304 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1304))
in (uu____1299)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv [] uu____1292))
end
| FStar_Reflection_Data.Pat_Dot_Term (bv, t) -> begin
(

let uu____1315 = (

let uu____1322 = (

let uu____1327 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1327))
in (

let uu____1328 = (

let uu____1335 = (

let uu____1340 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____1340))
in (uu____1335)::[])
in (uu____1322)::uu____1328))
in (mkConstruct FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv [] uu____1315))
end))
in (

let unembed_pattern = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((c, uu____1370))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid) -> begin
(

let uu____1387 = (FStar_TypeChecker_NBETerm.unembed e_const cb c)
in (FStar_Util.bind_opt uu____1387 (fun c1 -> (FStar_All.pipe_left (fun _0_6 -> FStar_Pervasives_Native.Some (_0_6)) (FStar_Reflection_Data.Pat_Constant (c1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((ps, uu____1396))::((f, uu____1398))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid) -> begin
(

let uu____1419 = (FStar_TypeChecker_NBETerm.unembed e_fv cb f)
in (FStar_Util.bind_opt uu____1419 (fun f1 -> (

let uu____1425 = (

let uu____1430 = (

let uu____1435 = (e_pattern' ())
in (FStar_TypeChecker_NBETerm.e_list uu____1435))
in (FStar_TypeChecker_NBETerm.unembed uu____1430 cb ps))
in (FStar_Util.bind_opt uu____1425 (fun ps1 -> (FStar_All.pipe_left (fun _0_7 -> FStar_Pervasives_Native.Some (_0_7)) (FStar_Reflection_Data.Pat_Cons (((f1), (ps1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((bv, uu____1452))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____1469 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1469 (fun bv1 -> (FStar_All.pipe_left (fun _0_8 -> FStar_Pervasives_Native.Some (_0_8)) (FStar_Reflection_Data.Pat_Var (bv1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((bv, uu____1478))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid) -> begin
(

let uu____1495 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1495 (fun bv1 -> (FStar_All.pipe_left (fun _0_9 -> FStar_Pervasives_Native.Some (_0_9)) (FStar_Reflection_Data.Pat_Wild (bv1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((t1, uu____1504))::((bv, uu____1506))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid) -> begin
(

let uu____1527 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1527 (fun bv1 -> (

let uu____1533 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____1533 (fun t2 -> (FStar_All.pipe_left (fun _0_10 -> FStar_Pervasives_Native.Some (_0_10)) (FStar_Reflection_Data.Pat_Dot_Term (((bv1), (t2)))))))))))
end
| uu____1540 -> begin
((

let uu____1542 = (

let uu____1548 = (

let uu____1550 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded pattern: %s" uu____1550))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1548)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1542));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_pattern unembed_pattern FStar_Reflection_Data.fstar_refl_pattern_fv))))


let e_pattern : FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding = (e_pattern' ())


let e_branch : FStar_Reflection_Data.branch FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_pattern e_term)


let e_argv : FStar_Reflection_Data.argv FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv)


let e_branch_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let uu____1591 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1591)))


let e_argv_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv) FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let uu____1622 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_tuple2 uu____1622 e_aqualv)))


let rec unlazy_as_t : 'Auu____1632 . FStar_Syntax_Syntax.lazy_kind  ->  FStar_TypeChecker_NBETerm.t  ->  'Auu____1632 = (fun k t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k'; FStar_Syntax_Syntax.ltyp = uu____1645; FStar_Syntax_Syntax.rng = uu____1646}), uu____1647) when (FStar_Syntax_Util.eq_lazy_kind k k') -> begin
(FStar_Dyn.undyn v1)
end
| uu____1666 -> begin
(failwith "Not a Lazy of the expected kind (NBE)")
end))


let e_term_view_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let embed_term_view = (fun cb tv -> (match (tv) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____1704 = (

let uu____1711 = (

let uu____1716 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1716))
in (uu____1711)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv [] uu____1704))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____1726 = (

let uu____1733 = (

let uu____1738 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1738))
in (uu____1733)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv [] uu____1726))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____1748 = (

let uu____1755 = (

let uu____1760 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1760))
in (uu____1755)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv [] uu____1748))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____1771 = (

let uu____1778 = (

let uu____1783 = (

let uu____1784 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1784 cb hd1))
in (FStar_TypeChecker_NBETerm.as_arg uu____1783))
in (

let uu____1787 = (

let uu____1794 = (

let uu____1799 = (

let uu____1800 = (e_argv_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1800 cb a))
in (FStar_TypeChecker_NBETerm.as_arg uu____1799))
in (uu____1794)::[])
in (uu____1778)::uu____1787))
in (mkConstruct FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv [] uu____1771))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____1825 = (

let uu____1832 = (

let uu____1837 = (FStar_TypeChecker_NBETerm.embed e_binder cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____1837))
in (

let uu____1838 = (

let uu____1845 = (

let uu____1850 = (

let uu____1851 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1851 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____1850))
in (uu____1845)::[])
in (uu____1832)::uu____1838))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv [] uu____1825))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____1868 = (

let uu____1875 = (

let uu____1880 = (FStar_TypeChecker_NBETerm.embed e_binder cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____1880))
in (

let uu____1881 = (

let uu____1888 = (

let uu____1893 = (FStar_TypeChecker_NBETerm.embed e_comp cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1893))
in (uu____1888)::[])
in (uu____1875)::uu____1881))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv [] uu____1868))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____1907 = (

let uu____1914 = (

let uu____1919 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_unit cb ())
in (FStar_TypeChecker_NBETerm.as_arg uu____1919))
in (uu____1914)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv [] uu____1907))
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____1930 = (

let uu____1937 = (

let uu____1942 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1942))
in (

let uu____1943 = (

let uu____1950 = (

let uu____1955 = (

let uu____1956 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1956 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____1955))
in (uu____1950)::[])
in (uu____1937)::uu____1943))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv [] uu____1930))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1972 = (

let uu____1979 = (

let uu____1984 = (FStar_TypeChecker_NBETerm.embed e_const cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1984))
in (uu____1979)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv [] uu____1972))
end
| FStar_Reflection_Data.Tv_Uvar (u, d) -> begin
(

let uu____1995 = (

let uu____2002 = (

let uu____2007 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int cb u)
in (FStar_TypeChecker_NBETerm.as_arg uu____2007))
in (

let uu____2008 = (

let uu____2015 = (

let uu____2020 = (mk_lazy cb ((u), (d)) FStar_Syntax_Util.t_ctx_uvar_and_sust FStar_Syntax_Syntax.Lazy_uvar)
in (FStar_TypeChecker_NBETerm.as_arg uu____2020))
in (uu____2015)::[])
in (uu____2002)::uu____2008))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv [] uu____1995))
end
| FStar_Reflection_Data.Tv_Let (r, b, t1, t2) -> begin
(

let uu____2043 = (

let uu____2050 = (

let uu____2055 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____2055))
in (

let uu____2057 = (

let uu____2064 = (

let uu____2069 = (FStar_TypeChecker_NBETerm.embed e_bv cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____2069))
in (

let uu____2070 = (

let uu____2077 = (

let uu____2082 = (

let uu____2083 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2083 cb t1))
in (FStar_TypeChecker_NBETerm.as_arg uu____2082))
in (

let uu____2086 = (

let uu____2093 = (

let uu____2098 = (

let uu____2099 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2099 cb t2))
in (FStar_TypeChecker_NBETerm.as_arg uu____2098))
in (uu____2093)::[])
in (uu____2077)::uu____2086))
in (uu____2064)::uu____2070))
in (uu____2050)::uu____2057))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv [] uu____2043))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let uu____2128 = (

let uu____2135 = (

let uu____2140 = (

let uu____2141 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2141 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____2140))
in (

let uu____2144 = (

let uu____2151 = (

let uu____2156 = (

let uu____2157 = (

let uu____2166 = (e_branch_aq aq)
in (FStar_TypeChecker_NBETerm.e_list uu____2166))
in (FStar_TypeChecker_NBETerm.embed uu____2157 cb brs))
in (FStar_TypeChecker_NBETerm.as_arg uu____2156))
in (uu____2151)::[])
in (uu____2135)::uu____2144))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv [] uu____2128))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____2202 = (

let uu____2209 = (

let uu____2214 = (

let uu____2215 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2215 cb e))
in (FStar_TypeChecker_NBETerm.as_arg uu____2214))
in (

let uu____2218 = (

let uu____2225 = (

let uu____2230 = (

let uu____2231 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2231 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____2230))
in (

let uu____2234 = (

let uu____2241 = (

let uu____2246 = (

let uu____2247 = (

let uu____2252 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_option uu____2252))
in (FStar_TypeChecker_NBETerm.embed uu____2247 cb tacopt))
in (FStar_TypeChecker_NBETerm.as_arg uu____2246))
in (uu____2241)::[])
in (uu____2225)::uu____2234))
in (uu____2209)::uu____2218))
in (mkConstruct FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv [] uu____2202))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____2280 = (

let uu____2287 = (

let uu____2292 = (

let uu____2293 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2293 cb e))
in (FStar_TypeChecker_NBETerm.as_arg uu____2292))
in (

let uu____2296 = (

let uu____2303 = (

let uu____2308 = (FStar_TypeChecker_NBETerm.embed e_comp cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____2308))
in (

let uu____2309 = (

let uu____2316 = (

let uu____2321 = (

let uu____2322 = (

let uu____2327 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_option uu____2327))
in (FStar_TypeChecker_NBETerm.embed uu____2322 cb tacopt))
in (FStar_TypeChecker_NBETerm.as_arg uu____2321))
in (uu____2316)::[])
in (uu____2303)::uu____2309))
in (uu____2287)::uu____2296))
in (mkConstruct FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv [] uu____2280))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(mkConstruct FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_term_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2368, ((b, uu____2370))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____2389 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2389 (fun b1 -> (FStar_All.pipe_left (fun _0_11 -> FStar_Pervasives_Native.Some (_0_11)) (FStar_Reflection_Data.Tv_Var (b1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2397, ((b, uu____2399))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2418 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2418 (fun b1 -> (FStar_All.pipe_left (fun _0_12 -> FStar_Pervasives_Native.Some (_0_12)) (FStar_Reflection_Data.Tv_BVar (b1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2426, ((f, uu____2428))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2447 = (FStar_TypeChecker_NBETerm.unembed e_fv cb f)
in (FStar_Util.bind_opt uu____2447 (fun f1 -> (FStar_All.pipe_left (fun _0_13 -> FStar_Pervasives_Native.Some (_0_13)) (FStar_Reflection_Data.Tv_FVar (f1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2455, ((r, uu____2457))::((l, uu____2459))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid) -> begin
(

let uu____2482 = (FStar_TypeChecker_NBETerm.unembed e_term cb l)
in (FStar_Util.bind_opt uu____2482 (fun l1 -> (

let uu____2488 = (FStar_TypeChecker_NBETerm.unembed e_argv cb r)
in (FStar_Util.bind_opt uu____2488 (fun r1 -> (FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (FStar_Reflection_Data.Tv_App (((l1), (r1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2496, ((t1, uu____2498))::((b, uu____2500))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid) -> begin
(

let uu____2523 = (FStar_TypeChecker_NBETerm.unembed e_binder cb b)
in (FStar_Util.bind_opt uu____2523 (fun b1 -> (

let uu____2529 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2529 (fun t2 -> (FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (FStar_Reflection_Data.Tv_Abs (((b1), (t2)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2537, ((t1, uu____2539))::((b, uu____2541))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid) -> begin
(

let uu____2564 = (FStar_TypeChecker_NBETerm.unembed e_binder cb b)
in (FStar_Util.bind_opt uu____2564 (fun b1 -> (

let uu____2570 = (FStar_TypeChecker_NBETerm.unembed e_comp cb t1)
in (FStar_Util.bind_opt uu____2570 (fun c -> (FStar_All.pipe_left (fun _0_16 -> FStar_Pervasives_Native.Some (_0_16)) (FStar_Reflection_Data.Tv_Arrow (((b1), (c)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2578, ((u, uu____2580))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid) -> begin
(

let uu____2599 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_unit cb u)
in (FStar_Util.bind_opt uu____2599 (fun u1 -> (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_Reflection_Data.Tv_Type (()))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2607, ((t1, uu____2609))::((b, uu____2611))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid) -> begin
(

let uu____2634 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2634 (fun b1 -> (

let uu____2640 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2640 (fun t2 -> (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) (FStar_Reflection_Data.Tv_Refine (((b1), (t2)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2648, ((c, uu____2650))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid) -> begin
(

let uu____2669 = (FStar_TypeChecker_NBETerm.unembed e_const cb c)
in (FStar_Util.bind_opt uu____2669 (fun c1 -> (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) (FStar_Reflection_Data.Tv_Const (c1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2677, ((l, uu____2679))::((u, uu____2681))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid) -> begin
(

let uu____2704 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb u)
in (FStar_Util.bind_opt uu____2704 (fun u1 -> (

let ctx_u_s = (unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l)
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) (FStar_Reflection_Data.Tv_Uvar (((u1), (ctx_u_s)))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2714, ((t2, uu____2716))::((t1, uu____2718))::((b, uu____2720))::((r, uu____2722))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____2753 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_Util.bind_opt uu____2753 (fun r1 -> (

let uu____2763 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2763 (fun b1 -> (

let uu____2769 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2769 (fun t11 -> (

let uu____2775 = (FStar_TypeChecker_NBETerm.unembed e_term cb t2)
in (FStar_Util.bind_opt uu____2775 (fun t21 -> (FStar_All.pipe_left (fun _0_21 -> FStar_Pervasives_Native.Some (_0_21)) (FStar_Reflection_Data.Tv_Let (((r1), (b1), (t11), (t21)))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2784, ((brs, uu____2786))::((t1, uu____2788))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid) -> begin
(

let uu____2811 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2811 (fun t2 -> (

let uu____2817 = (

let uu____2822 = (FStar_TypeChecker_NBETerm.e_list e_branch)
in (FStar_TypeChecker_NBETerm.unembed uu____2822 cb brs))
in (FStar_Util.bind_opt uu____2817 (fun brs1 -> (FStar_All.pipe_left (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22)) (FStar_Reflection_Data.Tv_Match (((t2), (brs1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2840, ((tacopt, uu____2842))::((t1, uu____2844))::((e, uu____2846))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid) -> begin
(

let uu____2873 = (FStar_TypeChecker_NBETerm.unembed e_term cb e)
in (FStar_Util.bind_opt uu____2873 (fun e1 -> (

let uu____2879 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2879 (fun t2 -> (

let uu____2885 = (

let uu____2890 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____2890 cb tacopt))
in (FStar_Util.bind_opt uu____2885 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_23 -> FStar_Pervasives_Native.Some (_0_23)) (FStar_Reflection_Data.Tv_AscribedT (((e1), (t2), (tacopt1))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2908, ((tacopt, uu____2910))::((c, uu____2912))::((e, uu____2914))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid) -> begin
(

let uu____2941 = (FStar_TypeChecker_NBETerm.unembed e_term cb e)
in (FStar_Util.bind_opt uu____2941 (fun e1 -> (

let uu____2947 = (FStar_TypeChecker_NBETerm.unembed e_comp cb c)
in (FStar_Util.bind_opt uu____2947 (fun c1 -> (

let uu____2953 = (

let uu____2958 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____2958 cb tacopt))
in (FStar_Util.bind_opt uu____2953 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_24 -> FStar_Pervasives_Native.Some (_0_24)) (FStar_Reflection_Data.Tv_AscribedC (((e1), (c1), (tacopt1))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2976, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_25 -> FStar_Pervasives_Native.Some (_0_25)) FStar_Reflection_Data.Tv_Unknown)
end
| uu____2993 -> begin
((

let uu____2995 = (

let uu____3001 = (

let uu____3003 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded term_view: %s" uu____3003))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3001)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____2995));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_term_view unembed_term_view FStar_Reflection_Data.fstar_refl_term_view_fv))))


let e_term_view : FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding = (e_term_view_aq [])


let e_bv_view : FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding = (

let embed_bv_view = (fun cb bvv -> (

let uu____3030 = (

let uu____3037 = (

let uu____3042 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string cb bvv.FStar_Reflection_Data.bv_ppname)
in (FStar_TypeChecker_NBETerm.as_arg uu____3042))
in (

let uu____3044 = (

let uu____3051 = (

let uu____3056 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int cb bvv.FStar_Reflection_Data.bv_index)
in (FStar_TypeChecker_NBETerm.as_arg uu____3056))
in (

let uu____3057 = (

let uu____3064 = (

let uu____3069 = (FStar_TypeChecker_NBETerm.embed e_term cb bvv.FStar_Reflection_Data.bv_sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____3069))
in (uu____3064)::[])
in (uu____3051)::uu____3057))
in (uu____3037)::uu____3044))
in (mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv [] uu____3030)))
in (

let unembed_bv_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3102, ((s, uu____3104))::((idx, uu____3106))::((nm, uu____3108))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid) -> begin
(

let uu____3135 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_string cb nm)
in (FStar_Util.bind_opt uu____3135 (fun nm1 -> (

let uu____3145 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb idx)
in (FStar_Util.bind_opt uu____3145 (fun idx1 -> (

let uu____3151 = (FStar_TypeChecker_NBETerm.unembed e_term cb s)
in (FStar_Util.bind_opt uu____3151 (fun s1 -> (FStar_All.pipe_left (fun _0_26 -> FStar_Pervasives_Native.Some (_0_26)) {FStar_Reflection_Data.bv_ppname = nm1; FStar_Reflection_Data.bv_index = idx1; FStar_Reflection_Data.bv_sort = s1}))))))))))
end
| uu____3158 -> begin
((

let uu____3160 = (

let uu____3166 = (

let uu____3168 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded bv_view: %s" uu____3168))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3166)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3160));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_bv_view unembed_bv_view FStar_Reflection_Data.fstar_refl_bv_view_fv)))


let e_comp_view : FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding = (

let embed_comp_view = (fun cb cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, md) -> begin
(

let uu____3192 = (

let uu____3199 = (

let uu____3204 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____3204))
in (

let uu____3205 = (

let uu____3212 = (

let uu____3217 = (

let uu____3218 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.embed uu____3218 cb md))
in (FStar_TypeChecker_NBETerm.as_arg uu____3217))
in (uu____3212)::[])
in (uu____3199)::uu____3205))
in (mkConstruct FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv [] uu____3192))
end
| FStar_Reflection_Data.C_Lemma (pre, post) -> begin
(

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let uu____3242 = (

let uu____3249 = (

let uu____3254 = (FStar_TypeChecker_NBETerm.embed e_term cb pre)
in (FStar_TypeChecker_NBETerm.as_arg uu____3254))
in (

let uu____3255 = (

let uu____3262 = (

let uu____3267 = (FStar_TypeChecker_NBETerm.embed e_term cb post1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3267))
in (uu____3262)::[])
in (uu____3249)::uu____3255))
in (mkConstruct FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv [] uu____3242)))
end
| FStar_Reflection_Data.C_Unknown -> begin
(mkConstruct FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_comp_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3300, ((md, uu____3302))::((t1, uu____3304))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid) -> begin
(

let uu____3327 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____3327 (fun t2 -> (

let uu____3333 = (

let uu____3338 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____3338 cb md))
in (FStar_Util.bind_opt uu____3333 (fun md1 -> (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) (FStar_Reflection_Data.C_Total (((t2), (md1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3356, ((post, uu____3358))::((pre, uu____3360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid) -> begin
(

let uu____3383 = (FStar_TypeChecker_NBETerm.unembed e_term cb pre)
in (FStar_Util.bind_opt uu____3383 (fun pre1 -> (

let uu____3389 = (FStar_TypeChecker_NBETerm.unembed e_term cb post)
in (FStar_Util.bind_opt uu____3389 (fun post1 -> (FStar_All.pipe_left (fun _0_28 -> FStar_Pervasives_Native.Some (_0_28)) (FStar_Reflection_Data.C_Lemma (((pre1), (post1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3397, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) FStar_Reflection_Data.C_Unknown)
end
| uu____3414 -> begin
((

let uu____3416 = (

let uu____3422 = (

let uu____3424 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded comp_view: %s" uu____3424))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3422)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3416));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_comp_view unembed_comp_view FStar_Reflection_Data.fstar_refl_comp_view_fv)))


let e_order : FStar_Order.order FStar_TypeChecker_NBETerm.embedding = (

let embed_order = (fun cb o -> (match (o) with
| FStar_Order.Lt -> begin
(mkConstruct FStar_Reflection_Data.ord_Lt_fv [] [])
end
| FStar_Order.Eq -> begin
(mkConstruct FStar_Reflection_Data.ord_Eq_fv [] [])
end
| FStar_Order.Gt -> begin
(mkConstruct FStar_Reflection_Data.ord_Gt_fv [] [])
end))
in (

let unembed_order = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3470, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Lt)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3486, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Eq)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3502, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Gt)
end
| uu____3517 -> begin
((

let uu____3519 = (

let uu____3525 = (

let uu____3527 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded order: %s" uu____3527))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3525)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3519));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____3531 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mk_emb' embed_order unembed_order uu____3531))))


let e_sigelt : FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding = (

let embed_sigelt = (fun cb se -> (mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt FStar_Syntax_Syntax.Lazy_sigelt))
in (

let unembed_sigelt = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt; FStar_Syntax_Syntax.ltyp = uu____3562; FStar_Syntax_Syntax.rng = uu____3563}), uu____3564) -> begin
(

let uu____3583 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____3583))
end
| uu____3584 -> begin
((

let uu____3586 = (

let uu____3592 = (

let uu____3594 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded sigelt: %s" uu____3594))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3592)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3586));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt_fv)))


let e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding = (

let repr = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range FStar_TypeChecker_NBETerm.e_string)
in (

let embed_ident = (fun cb i -> (

let uu____3623 = (

let uu____3629 = (FStar_Ident.range_of_id i)
in (

let uu____3630 = (FStar_Ident.text_of_id i)
in ((uu____3629), (uu____3630))))
in (FStar_TypeChecker_NBETerm.embed repr cb uu____3623)))
in (

let unembed_ident = (fun cb t -> (

let uu____3653 = (FStar_TypeChecker_NBETerm.unembed repr cb t)
in (match (uu____3653) with
| FStar_Pervasives_Native.Some (rng, s) -> begin
(

let uu____3677 = (FStar_Ident.mk_ident ((s), (rng)))
in FStar_Pervasives_Native.Some (uu____3677))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))
in (

let range_fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.range_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let string_fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.string_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let et = (

let uu____3687 = (

let uu____3695 = (FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2)
in (

let uu____3697 = (

let uu____3700 = (fv_as_emb_typ range_fv)
in (

let uu____3701 = (

let uu____3704 = (fv_as_emb_typ string_fv)
in (uu____3704)::[])
in (uu____3700)::uu____3701))
in ((uu____3695), (uu____3697))))
in FStar_Syntax_Syntax.ET_app (uu____3687))
in (

let uu____3708 = (

let uu____3709 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____3710 = (

let uu____3717 = (

let uu____3722 = (mkFV range_fv [] [])
in (FStar_TypeChecker_NBETerm.as_arg uu____3722))
in (

let uu____3727 = (

let uu____3734 = (

let uu____3739 = (mkFV string_fv [] [])
in (FStar_TypeChecker_NBETerm.as_arg uu____3739))
in (uu____3734)::[])
in (uu____3717)::uu____3727))
in (mkFV uu____3709 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____3710)))
in (FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3708 et))))))))


let e_univ_name : FStar_Syntax_Syntax.univ_name FStar_TypeChecker_NBETerm.embedding = e_ident


let e_univ_names : FStar_Syntax_Syntax.univ_name Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_univ_name)


let e_string_list : Prims.string Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_string)


let e_sigelt_view : FStar_Reflection_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding = (

let embed_sigelt_view = (fun cb sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Let (r, fv, univs1, ty, t) -> begin
(

let uu____3796 = (

let uu____3803 = (

let uu____3808 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____3808))
in (

let uu____3810 = (

let uu____3817 = (

let uu____3822 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____3822))
in (

let uu____3823 = (

let uu____3830 = (

let uu____3835 = (FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3835))
in (

let uu____3838 = (

let uu____3845 = (

let uu____3850 = (FStar_TypeChecker_NBETerm.embed e_term cb ty)
in (FStar_TypeChecker_NBETerm.as_arg uu____3850))
in (

let uu____3851 = (

let uu____3858 = (

let uu____3863 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____3863))
in (uu____3858)::[])
in (uu____3845)::uu____3851))
in (uu____3830)::uu____3838))
in (uu____3817)::uu____3823))
in (uu____3803)::uu____3810))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv [] uu____3796))
end
| FStar_Reflection_Data.Sg_Constructor (nm, ty) -> begin
(

let uu____3890 = (

let uu____3897 = (

let uu____3902 = (FStar_TypeChecker_NBETerm.embed e_string_list cb nm)
in (FStar_TypeChecker_NBETerm.as_arg uu____3902))
in (

let uu____3906 = (

let uu____3913 = (

let uu____3918 = (FStar_TypeChecker_NBETerm.embed e_term cb ty)
in (FStar_TypeChecker_NBETerm.as_arg uu____3918))
in (uu____3913)::[])
in (uu____3897)::uu____3906))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv [] uu____3890))
end
| FStar_Reflection_Data.Sg_Inductive (nm, univs1, bs, t, dcs) -> begin
(

let uu____3948 = (

let uu____3955 = (

let uu____3960 = (FStar_TypeChecker_NBETerm.embed e_string_list cb nm)
in (FStar_TypeChecker_NBETerm.as_arg uu____3960))
in (

let uu____3964 = (

let uu____3971 = (

let uu____3976 = (FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3976))
in (

let uu____3979 = (

let uu____3986 = (

let uu____3991 = (FStar_TypeChecker_NBETerm.embed e_binders cb bs)
in (FStar_TypeChecker_NBETerm.as_arg uu____3991))
in (

let uu____3992 = (

let uu____3999 = (

let uu____4004 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____4004))
in (

let uu____4005 = (

let uu____4012 = (

let uu____4017 = (

let uu____4018 = (FStar_TypeChecker_NBETerm.e_list e_string_list)
in (FStar_TypeChecker_NBETerm.embed uu____4018 cb dcs))
in (FStar_TypeChecker_NBETerm.as_arg uu____4017))
in (uu____4012)::[])
in (uu____3999)::uu____4005))
in (uu____3986)::uu____3992))
in (uu____3971)::uu____3979))
in (uu____3955)::uu____3964))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv [] uu____3948))
end
| FStar_Reflection_Data.Unk -> begin
(mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_sigelt_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4078, ((dcs, uu____4080))::((t1, uu____4082))::((bs, uu____4084))::((us, uu____4086))::((nm, uu____4088))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid) -> begin
(

let uu____4123 = (FStar_TypeChecker_NBETerm.unembed e_string_list cb nm)
in (FStar_Util.bind_opt uu____4123 (fun nm1 -> (

let uu____4141 = (FStar_TypeChecker_NBETerm.unembed e_univ_names cb us)
in (FStar_Util.bind_opt uu____4141 (fun us1 -> (

let uu____4155 = (FStar_TypeChecker_NBETerm.unembed e_binders cb bs)
in (FStar_Util.bind_opt uu____4155 (fun bs1 -> (

let uu____4161 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____4161 (fun t2 -> (

let uu____4167 = (

let uu____4175 = (FStar_TypeChecker_NBETerm.e_list e_string_list)
in (FStar_TypeChecker_NBETerm.unembed uu____4175 cb dcs))
in (FStar_Util.bind_opt uu____4167 (fun dcs1 -> (FStar_All.pipe_left (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)) (FStar_Reflection_Data.Sg_Inductive (((nm1), (us1), (bs1), (t2), (dcs1))))))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4212, ((t1, uu____4214))::((ty, uu____4216))::((univs1, uu____4218))::((fvar1, uu____4220))::((r, uu____4222))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____4257 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_Util.bind_opt uu____4257 (fun r1 -> (

let uu____4267 = (FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1)
in (FStar_Util.bind_opt uu____4267 (fun fvar2 -> (

let uu____4273 = (FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1)
in (FStar_Util.bind_opt uu____4273 (fun univs2 -> (

let uu____4287 = (FStar_TypeChecker_NBETerm.unembed e_term cb ty)
in (FStar_Util.bind_opt uu____4287 (fun ty1 -> (

let uu____4293 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____4293 (fun t2 -> (FStar_All.pipe_left (fun _0_31 -> FStar_Pervasives_Native.Some (_0_31)) (FStar_Reflection_Data.Sg_Let (((r1), (fvar2), (univs2), (ty1), (t2))))))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4304, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unk)
end
| uu____4319 -> begin
((

let uu____4321 = (

let uu____4327 = (

let uu____4329 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4329))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4327)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4321));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_sigelt_view unembed_sigelt_view FStar_Reflection_Data.fstar_refl_sigelt_view_fv)))


let e_exp : FStar_Reflection_Data.exp FStar_TypeChecker_NBETerm.embedding = (

let rec embed_exp = (fun cb e -> (match (e) with
| FStar_Reflection_Data.Unit -> begin
(mkConstruct FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.fv [] [])
end
| FStar_Reflection_Data.Var (i) -> begin
(

let uu____4352 = (

let uu____4359 = (FStar_TypeChecker_NBETerm.as_arg (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i))))
in (uu____4359)::[])
in (mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv [] uu____4352))
end
| FStar_Reflection_Data.Mult (e1, e2) -> begin
(

let uu____4374 = (

let uu____4381 = (

let uu____4386 = (embed_exp cb e1)
in (FStar_TypeChecker_NBETerm.as_arg uu____4386))
in (

let uu____4387 = (

let uu____4394 = (

let uu____4399 = (embed_exp cb e2)
in (FStar_TypeChecker_NBETerm.as_arg uu____4399))
in (uu____4394)::[])
in (uu____4381)::uu____4387))
in (mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv [] uu____4374))
end))
in (

let rec unembed_exp = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4428, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4444, ((i, uu____4446))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____4465 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb i)
in (FStar_Util.bind_opt uu____4465 (fun i1 -> (FStar_All.pipe_left (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32)) (FStar_Reflection_Data.Var (i1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4473, ((e2, uu____4475))::((e1, uu____4477))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid) -> begin
(

let uu____4500 = (unembed_exp cb e1)
in (FStar_Util.bind_opt uu____4500 (fun e11 -> (

let uu____4506 = (unembed_exp cb e2)
in (FStar_Util.bind_opt uu____4506 (fun e21 -> (FStar_All.pipe_left (fun _0_33 -> FStar_Pervasives_Native.Some (_0_33)) (FStar_Reflection_Data.Mult (((e11), (e21)))))))))))
end
| uu____4513 -> begin
((

let uu____4515 = (

let uu____4521 = (

let uu____4523 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded exp: %s" uu____4523))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4521)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4515));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp_fv)))


let e_binder_view : FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv)


let e_attribute : FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding = e_term


let e_attributes : FStar_Syntax_Syntax.attribute Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_attribute)





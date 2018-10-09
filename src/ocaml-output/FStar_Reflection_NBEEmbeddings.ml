
open Prims
open FStar_Pervasives

let mkFV : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun fv us ts -> (FStar_TypeChecker_NBETerm.mkFV fv (FStar_List.rev us) (FStar_List.rev ts)))


let mkConstruct : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.universe Prims.list  ->  (FStar_TypeChecker_NBETerm.t * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_TypeChecker_NBETerm.t = (fun fv us ts -> (FStar_TypeChecker_NBETerm.mkConstruct fv (FStar_List.rev us) (FStar_List.rev ts)))


let fv_as_emb_typ : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.emb_typ = (fun fv -> (

let uu____76 = (

let uu____83 = (FStar_Ident.string_of_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((uu____83), ([])))
in FStar_Syntax_Syntax.ET_app (uu____76)))


let mk_emb' : 'Auu____94 . (FStar_TypeChecker_NBETerm.nbe_cbs  ->  'Auu____94  ->  FStar_TypeChecker_NBETerm.t)  ->  (FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.t  ->  'Auu____94 FStar_Pervasives_Native.option)  ->  FStar_Syntax_Syntax.fv  ->  'Auu____94 FStar_TypeChecker_NBETerm.embedding = (fun x y fv -> (

let uu____136 = (mkFV fv [] [])
in (

let uu____141 = (fv_as_emb_typ fv)
in (FStar_TypeChecker_NBETerm.mk_emb x y uu____136 uu____141))))


let mk_lazy : 'Auu____152 . FStar_TypeChecker_NBETerm.nbe_cbs  ->  'Auu____152  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.lazy_kind  ->  FStar_TypeChecker_NBETerm.t = (fun cb obj ty kind -> (

let li = (

let uu____178 = (FStar_Dyn.mkdyn obj)
in {FStar_Syntax_Syntax.blob = uu____178; FStar_Syntax_Syntax.lkind = kind; FStar_Syntax_Syntax.ltyp = ty; FStar_Syntax_Syntax.rng = FStar_Range.dummyRange})
in (

let thunk = (FStar_Common.mk_thunk (fun uu____184 -> (

let uu____185 = (FStar_Syntax_Util.unfold_lazy li)
in (FStar_TypeChecker_NBETerm.translate_cb cb uu____185))))
in FStar_TypeChecker_NBETerm.Lazy (((FStar_Util.Inl (li)), (thunk))))))


let e_bv : FStar_Syntax_Syntax.bv FStar_TypeChecker_NBETerm.embedding = (

let embed_bv = (fun cb bv -> (mk_lazy cb bv FStar_Reflection_Data.fstar_refl_bv FStar_Syntax_Syntax.Lazy_bv))
in (

let unembed_bv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_bv; FStar_Syntax_Syntax.ltyp = uu____269; FStar_Syntax_Syntax.rng = uu____270}), uu____271) -> begin
(

let uu____290 = (FStar_Dyn.undyn b)
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____290))
end
| uu____293 -> begin
((

let uu____295 = (

let uu____300 = (

let uu____301 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded bv: %s" uu____301))
in ((FStar_Errors.Warning_NotEmbedded), (uu____300)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____295));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv_fv)))


let e_binder : FStar_Syntax_Syntax.binder FStar_TypeChecker_NBETerm.embedding = (

let embed_binder = (fun cb b -> (mk_lazy cb b FStar_Reflection_Data.fstar_refl_binder FStar_Syntax_Syntax.Lazy_binder))
in (

let unembed_binder = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_binder; FStar_Syntax_Syntax.ltyp = uu____331; FStar_Syntax_Syntax.rng = uu____332}), uu____333) -> begin
(

let uu____352 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____352))
end
| uu____353 -> begin
((

let uu____355 = (

let uu____360 = (

let uu____361 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded binder: %s" uu____361))
in ((FStar_Errors.Warning_NotEmbedded), (uu____360)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____355));
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

let uu____407 = (f x)
in (FStar_Util.bind_opt uu____407 (fun x1 -> (

let uu____415 = (mapM_opt f xs)
in (FStar_Util.bind_opt uu____415 (fun xs1 -> FStar_Pervasives_Native.Some ((x1)::xs1)))))))
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
| uu____484 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____485 = (mkFV FStar_Reflection_Data.fstar_refl_term_fv [] [])
in (

let uu____490 = (fv_as_emb_typ FStar_Reflection_Data.fstar_refl_term_fv)
in {FStar_TypeChecker_NBETerm.em = embed_term; FStar_TypeChecker_NBETerm.un = unembed_term; FStar_TypeChecker_NBETerm.typ = uu____485; FStar_TypeChecker_NBETerm.emb_typ = uu____490})))))


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

let uu____521 = (

let uu____528 = (

let uu____533 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____533))
in (uu____528)::[])
in (mkConstruct FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.fv [] uu____521))
end))
in (

let unembed_aqualv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Explicit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Implicit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((t1, uu____585))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Meta.FStar_Reflection_Data.lid) -> begin
(

let uu____602 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____602 (fun t2 -> FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Meta (t2)))))
end
| uu____607 -> begin
((

let uu____609 = (

let uu____614 = (

let uu____615 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded aqualv: %s" uu____615))
in ((FStar_Errors.Warning_NotEmbedded), (uu____614)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____609));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____616 = (mkConstruct FStar_Reflection_Data.fstar_refl_aqualv_fv [] [])
in (

let uu____621 = (fv_as_emb_typ FStar_Reflection_Data.fstar_refl_aqualv_fv)
in (FStar_TypeChecker_NBETerm.mk_emb embed_aqualv unembed_aqualv uu____616 uu____621)))))


let e_binders : FStar_Syntax_Syntax.binders FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_binder)


let e_fv : FStar_Syntax_Syntax.fv FStar_TypeChecker_NBETerm.embedding = (

let embed_fv = (fun cb fv -> (mk_lazy cb fv FStar_Reflection_Data.fstar_refl_fv FStar_Syntax_Syntax.Lazy_fvar))
in (

let unembed_fv = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_fvar; FStar_Syntax_Syntax.ltyp = uu____653; FStar_Syntax_Syntax.rng = uu____654}), uu____655) -> begin
(

let uu____674 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____674))
end
| uu____675 -> begin
((

let uu____677 = (

let uu____682 = (

let uu____683 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded fvar: %s" uu____683))
in ((FStar_Errors.Warning_NotEmbedded), (uu____682)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____677));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv_fv)))


let e_comp : FStar_Syntax_Syntax.comp FStar_TypeChecker_NBETerm.embedding = (

let embed_comp = (fun cb c -> (mk_lazy cb c FStar_Reflection_Data.fstar_refl_comp FStar_Syntax_Syntax.Lazy_comp))
in (

let unembed_comp = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_comp; FStar_Syntax_Syntax.ltyp = uu____713; FStar_Syntax_Syntax.rng = uu____714}), uu____715) -> begin
(

let uu____734 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____734))
end
| uu____735 -> begin
((

let uu____737 = (

let uu____742 = (

let uu____743 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded comp: %s" uu____743))
in ((FStar_Errors.Warning_NotEmbedded), (uu____742)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____737));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp_fv)))


let e_env : FStar_TypeChecker_Env.env FStar_TypeChecker_NBETerm.embedding = (

let embed_env = (fun cb e -> (mk_lazy cb e FStar_Reflection_Data.fstar_refl_env FStar_Syntax_Syntax.Lazy_env))
in (

let unembed_env = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_env; FStar_Syntax_Syntax.ltyp = uu____773; FStar_Syntax_Syntax.rng = uu____774}), uu____775) -> begin
(

let uu____794 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____794))
end
| uu____795 -> begin
((

let uu____797 = (

let uu____802 = (

let uu____803 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded env: %s" uu____803))
in ((FStar_Errors.Warning_NotEmbedded), (uu____802)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____797));
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

let uu____830 = (

let uu____837 = (FStar_TypeChecker_NBETerm.as_arg (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i))))
in (uu____837)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.fv [] uu____830))
end
| FStar_Reflection_Data.C_String (s) -> begin
(

let uu____851 = (

let uu____858 = (

let uu____863 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string cb s)
in (FStar_TypeChecker_NBETerm.as_arg uu____863))
in (uu____858)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.fv [] uu____851))
end
| FStar_Reflection_Data.C_Range (r) -> begin
(

let uu____873 = (

let uu____880 = (

let uu____885 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_range cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____885))
in (uu____880)::[])
in (mkConstruct FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.fv [] uu____873))
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
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((i, uu____950))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid) -> begin
(

let uu____967 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb i)
in (FStar_Util.bind_opt uu____967 (fun i1 -> (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) (FStar_Reflection_Data.C_Int (i1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((s, uu____976))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid) -> begin
(

let uu____993 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_string cb s)
in (FStar_Util.bind_opt uu____993 (fun s1 -> (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) (FStar_Reflection_Data.C_String (s1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((r, uu____1002))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Range.FStar_Reflection_Data.lid) -> begin
(

let uu____1019 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_range cb r)
in (FStar_Util.bind_opt uu____1019 (fun r1 -> (FStar_All.pipe_left (fun _0_4 -> FStar_Pervasives_Native.Some (_0_4)) (FStar_Reflection_Data.C_Range (r1))))))
end
| uu____1026 -> begin
((

let uu____1028 = (

let uu____1033 = (

let uu____1034 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded vconst: %s" uu____1034))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1033)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1028));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst_fv)))


let rec e_pattern' : unit  ->  FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding = (fun uu____1041 -> (

let embed_pattern = (fun cb p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____1054 = (

let uu____1061 = (

let uu____1066 = (FStar_TypeChecker_NBETerm.embed e_const cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1066))
in (uu____1061)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.fv [] uu____1054))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____1081 = (

let uu____1088 = (

let uu____1093 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1093))
in (

let uu____1094 = (

let uu____1101 = (

let uu____1106 = (

let uu____1107 = (

let uu____1112 = (e_pattern' ())
in (FStar_TypeChecker_NBETerm.e_list uu____1112))
in (FStar_TypeChecker_NBETerm.embed uu____1107 cb ps))
in (FStar_TypeChecker_NBETerm.as_arg uu____1106))
in (uu____1101)::[])
in (uu____1088)::uu____1094))
in (mkConstruct FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.fv [] uu____1081))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____1130 = (

let uu____1137 = (

let uu____1142 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1142))
in (uu____1137)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.fv [] uu____1130))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____1152 = (

let uu____1159 = (

let uu____1164 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1164))
in (uu____1159)::[])
in (mkConstruct FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.fv [] uu____1152))
end
| FStar_Reflection_Data.Pat_Dot_Term (bv, t) -> begin
(

let uu____1175 = (

let uu____1182 = (

let uu____1187 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1187))
in (

let uu____1188 = (

let uu____1195 = (

let uu____1200 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____1200))
in (uu____1195)::[])
in (uu____1182)::uu____1188))
in (mkConstruct FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.fv [] uu____1175))
end))
in (

let unembed_pattern = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((c, uu____1230))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid) -> begin
(

let uu____1247 = (FStar_TypeChecker_NBETerm.unembed e_const cb c)
in (FStar_Util.bind_opt uu____1247 (fun c1 -> (FStar_All.pipe_left (fun _0_5 -> FStar_Pervasives_Native.Some (_0_5)) (FStar_Reflection_Data.Pat_Constant (c1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((ps, uu____1256))::((f, uu____1258))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid) -> begin
(

let uu____1279 = (FStar_TypeChecker_NBETerm.unembed e_fv cb f)
in (FStar_Util.bind_opt uu____1279 (fun f1 -> (

let uu____1285 = (

let uu____1290 = (

let uu____1295 = (e_pattern' ())
in (FStar_TypeChecker_NBETerm.e_list uu____1295))
in (FStar_TypeChecker_NBETerm.unembed uu____1290 cb ps))
in (FStar_Util.bind_opt uu____1285 (fun ps1 -> (FStar_All.pipe_left (fun _0_6 -> FStar_Pervasives_Native.Some (_0_6)) (FStar_Reflection_Data.Pat_Cons (((f1), (ps1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((bv, uu____1312))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____1329 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1329 (fun bv1 -> (FStar_All.pipe_left (fun _0_7 -> FStar_Pervasives_Native.Some (_0_7)) (FStar_Reflection_Data.Pat_Var (bv1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((bv, uu____1338))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid) -> begin
(

let uu____1355 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1355 (fun bv1 -> (FStar_All.pipe_left (fun _0_8 -> FStar_Pervasives_Native.Some (_0_8)) (FStar_Reflection_Data.Pat_Wild (bv1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, [], ((t1, uu____1364))::((bv, uu____1366))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid) -> begin
(

let uu____1387 = (FStar_TypeChecker_NBETerm.unembed e_bv cb bv)
in (FStar_Util.bind_opt uu____1387 (fun bv1 -> (

let uu____1393 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____1393 (fun t2 -> (FStar_All.pipe_left (fun _0_9 -> FStar_Pervasives_Native.Some (_0_9)) (FStar_Reflection_Data.Pat_Dot_Term (((bv1), (t2)))))))))))
end
| uu____1400 -> begin
((

let uu____1402 = (

let uu____1407 = (

let uu____1408 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded pattern: %s" uu____1408))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1407)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1402));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_pattern unembed_pattern FStar_Reflection_Data.fstar_refl_pattern_fv))))


let e_pattern : FStar_Reflection_Data.pattern FStar_TypeChecker_NBETerm.embedding = (e_pattern' ())


let e_branch : FStar_Reflection_Data.branch FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_pattern e_term)


let e_argv : FStar_Reflection_Data.argv FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_term e_aqualv)


let e_branch_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let uu____1442 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_tuple2 e_pattern uu____1442)))


let e_argv_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv) FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let uu____1472 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_tuple2 uu____1472 e_aqualv)))


let rec unlazy_as_t : 'Auu____1481 . FStar_Syntax_Syntax.lazy_kind  ->  FStar_TypeChecker_NBETerm.t  ->  'Auu____1481 = (fun k t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k'; FStar_Syntax_Syntax.ltyp = uu____1494; FStar_Syntax_Syntax.rng = uu____1495}), uu____1496) when (FStar_Syntax_Util.eq_lazy_kind k k') -> begin
(FStar_Dyn.undyn v1)
end
| uu____1515 -> begin
(failwith "Not a Lazy of the expected kind (NBE)")
end))


let e_term_view_aq : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list  ->  FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding = (fun aq -> (

let embed_term_view = (fun cb tv -> (match (tv) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____1551 = (

let uu____1558 = (

let uu____1563 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1563))
in (uu____1558)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.fv [] uu____1551))
end
| FStar_Reflection_Data.Tv_BVar (bv) -> begin
(

let uu____1573 = (

let uu____1580 = (

let uu____1585 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1585))
in (uu____1580)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.fv [] uu____1573))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____1595 = (

let uu____1602 = (

let uu____1607 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1607))
in (uu____1602)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.fv [] uu____1595))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____1618 = (

let uu____1625 = (

let uu____1630 = (

let uu____1631 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1631 cb hd1))
in (FStar_TypeChecker_NBETerm.as_arg uu____1630))
in (

let uu____1634 = (

let uu____1641 = (

let uu____1646 = (

let uu____1647 = (e_argv_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1647 cb a))
in (FStar_TypeChecker_NBETerm.as_arg uu____1646))
in (uu____1641)::[])
in (uu____1625)::uu____1634))
in (mkConstruct FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.fv [] uu____1618))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(

let uu____1672 = (

let uu____1679 = (

let uu____1684 = (FStar_TypeChecker_NBETerm.embed e_binder cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____1684))
in (

let uu____1685 = (

let uu____1692 = (

let uu____1697 = (

let uu____1698 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1698 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____1697))
in (uu____1692)::[])
in (uu____1679)::uu____1685))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.fv [] uu____1672))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____1715 = (

let uu____1722 = (

let uu____1727 = (FStar_TypeChecker_NBETerm.embed e_binder cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____1727))
in (

let uu____1728 = (

let uu____1735 = (

let uu____1740 = (FStar_TypeChecker_NBETerm.embed e_comp cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1740))
in (uu____1735)::[])
in (uu____1722)::uu____1728))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.fv [] uu____1715))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____1754 = (

let uu____1761 = (

let uu____1766 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_unit cb ())
in (FStar_TypeChecker_NBETerm.as_arg uu____1766))
in (uu____1761)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.fv [] uu____1754))
end
| FStar_Reflection_Data.Tv_Refine (bv, t) -> begin
(

let uu____1777 = (

let uu____1784 = (

let uu____1789 = (FStar_TypeChecker_NBETerm.embed e_bv cb bv)
in (FStar_TypeChecker_NBETerm.as_arg uu____1789))
in (

let uu____1790 = (

let uu____1797 = (

let uu____1802 = (

let uu____1803 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1803 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____1802))
in (uu____1797)::[])
in (uu____1784)::uu____1790))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.fv [] uu____1777))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1819 = (

let uu____1826 = (

let uu____1831 = (FStar_TypeChecker_NBETerm.embed e_const cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____1831))
in (uu____1826)::[])
in (mkConstruct FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.fv [] uu____1819))
end
| FStar_Reflection_Data.Tv_Uvar (u, d) -> begin
(

let uu____1842 = (

let uu____1849 = (

let uu____1854 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int cb u)
in (FStar_TypeChecker_NBETerm.as_arg uu____1854))
in (

let uu____1855 = (

let uu____1862 = (

let uu____1867 = (mk_lazy cb ((u), (d)) FStar_Syntax_Util.t_ctx_uvar_and_sust FStar_Syntax_Syntax.Lazy_uvar)
in (FStar_TypeChecker_NBETerm.as_arg uu____1867))
in (uu____1862)::[])
in (uu____1849)::uu____1855))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.fv [] uu____1842))
end
| FStar_Reflection_Data.Tv_Let (r, b, t1, t2) -> begin
(

let uu____1888 = (

let uu____1895 = (

let uu____1900 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____1900))
in (

let uu____1901 = (

let uu____1908 = (

let uu____1913 = (FStar_TypeChecker_NBETerm.embed e_bv cb b)
in (FStar_TypeChecker_NBETerm.as_arg uu____1913))
in (

let uu____1914 = (

let uu____1921 = (

let uu____1926 = (

let uu____1927 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1927 cb t1))
in (FStar_TypeChecker_NBETerm.as_arg uu____1926))
in (

let uu____1930 = (

let uu____1937 = (

let uu____1942 = (

let uu____1943 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1943 cb t2))
in (FStar_TypeChecker_NBETerm.as_arg uu____1942))
in (uu____1937)::[])
in (uu____1921)::uu____1930))
in (uu____1908)::uu____1914))
in (uu____1895)::uu____1901))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.fv [] uu____1888))
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let uu____1972 = (

let uu____1979 = (

let uu____1984 = (

let uu____1985 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____1985 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____1984))
in (

let uu____1988 = (

let uu____1995 = (

let uu____2000 = (

let uu____2001 = (

let uu____2010 = (e_branch_aq aq)
in (FStar_TypeChecker_NBETerm.e_list uu____2010))
in (FStar_TypeChecker_NBETerm.embed uu____2001 cb brs))
in (FStar_TypeChecker_NBETerm.as_arg uu____2000))
in (uu____1995)::[])
in (uu____1979)::uu____1988))
in (mkConstruct FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.fv [] uu____1972))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) -> begin
(

let uu____2046 = (

let uu____2053 = (

let uu____2058 = (

let uu____2059 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2059 cb e))
in (FStar_TypeChecker_NBETerm.as_arg uu____2058))
in (

let uu____2062 = (

let uu____2069 = (

let uu____2074 = (

let uu____2075 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2075 cb t))
in (FStar_TypeChecker_NBETerm.as_arg uu____2074))
in (

let uu____2078 = (

let uu____2085 = (

let uu____2090 = (

let uu____2091 = (

let uu____2096 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_option uu____2096))
in (FStar_TypeChecker_NBETerm.embed uu____2091 cb tacopt))
in (FStar_TypeChecker_NBETerm.as_arg uu____2090))
in (uu____2085)::[])
in (uu____2069)::uu____2078))
in (uu____2053)::uu____2062))
in (mkConstruct FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv [] uu____2046))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____2124 = (

let uu____2131 = (

let uu____2136 = (

let uu____2137 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.embed uu____2137 cb e))
in (FStar_TypeChecker_NBETerm.as_arg uu____2136))
in (

let uu____2140 = (

let uu____2147 = (

let uu____2152 = (FStar_TypeChecker_NBETerm.embed e_comp cb c)
in (FStar_TypeChecker_NBETerm.as_arg uu____2152))
in (

let uu____2153 = (

let uu____2160 = (

let uu____2165 = (

let uu____2166 = (

let uu____2171 = (e_term_aq aq)
in (FStar_TypeChecker_NBETerm.e_option uu____2171))
in (FStar_TypeChecker_NBETerm.embed uu____2166 cb tacopt))
in (FStar_TypeChecker_NBETerm.as_arg uu____2165))
in (uu____2160)::[])
in (uu____2147)::uu____2153))
in (uu____2131)::uu____2140))
in (mkConstruct FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.fv [] uu____2124))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(mkConstruct FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_term_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2212, ((b, uu____2214))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____2233 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2233 (fun b1 -> (FStar_All.pipe_left (fun _0_10 -> FStar_Pervasives_Native.Some (_0_10)) (FStar_Reflection_Data.Tv_Var (b1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2241, ((b, uu____2243))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2262 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2262 (fun b1 -> (FStar_All.pipe_left (fun _0_11 -> FStar_Pervasives_Native.Some (_0_11)) (FStar_Reflection_Data.Tv_BVar (b1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2270, ((f, uu____2272))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2291 = (FStar_TypeChecker_NBETerm.unembed e_fv cb f)
in (FStar_Util.bind_opt uu____2291 (fun f1 -> (FStar_All.pipe_left (fun _0_12 -> FStar_Pervasives_Native.Some (_0_12)) (FStar_Reflection_Data.Tv_FVar (f1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2299, ((r, uu____2301))::((l, uu____2303))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid) -> begin
(

let uu____2326 = (FStar_TypeChecker_NBETerm.unembed e_term cb l)
in (FStar_Util.bind_opt uu____2326 (fun l1 -> (

let uu____2332 = (FStar_TypeChecker_NBETerm.unembed e_argv cb r)
in (FStar_Util.bind_opt uu____2332 (fun r1 -> (FStar_All.pipe_left (fun _0_13 -> FStar_Pervasives_Native.Some (_0_13)) (FStar_Reflection_Data.Tv_App (((l1), (r1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2340, ((t1, uu____2342))::((b, uu____2344))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid) -> begin
(

let uu____2367 = (FStar_TypeChecker_NBETerm.unembed e_binder cb b)
in (FStar_Util.bind_opt uu____2367 (fun b1 -> (

let uu____2373 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2373 (fun t2 -> (FStar_All.pipe_left (fun _0_14 -> FStar_Pervasives_Native.Some (_0_14)) (FStar_Reflection_Data.Tv_Abs (((b1), (t2)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2381, ((t1, uu____2383))::((b, uu____2385))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid) -> begin
(

let uu____2408 = (FStar_TypeChecker_NBETerm.unembed e_binder cb b)
in (FStar_Util.bind_opt uu____2408 (fun b1 -> (

let uu____2414 = (FStar_TypeChecker_NBETerm.unembed e_comp cb t1)
in (FStar_Util.bind_opt uu____2414 (fun c -> (FStar_All.pipe_left (fun _0_15 -> FStar_Pervasives_Native.Some (_0_15)) (FStar_Reflection_Data.Tv_Arrow (((b1), (c)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2422, ((u, uu____2424))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid) -> begin
(

let uu____2443 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_unit cb u)
in (FStar_Util.bind_opt uu____2443 (fun u1 -> (FStar_All.pipe_left (fun _0_16 -> FStar_Pervasives_Native.Some (_0_16)) (FStar_Reflection_Data.Tv_Type (()))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2451, ((t1, uu____2453))::((b, uu____2455))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid) -> begin
(

let uu____2478 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2478 (fun b1 -> (

let uu____2484 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2484 (fun t2 -> (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_Reflection_Data.Tv_Refine (((b1), (t2)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2492, ((c, uu____2494))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid) -> begin
(

let uu____2513 = (FStar_TypeChecker_NBETerm.unembed e_const cb c)
in (FStar_Util.bind_opt uu____2513 (fun c1 -> (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) (FStar_Reflection_Data.Tv_Const (c1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2521, ((l, uu____2523))::((u, uu____2525))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid) -> begin
(

let uu____2548 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb u)
in (FStar_Util.bind_opt uu____2548 (fun u1 -> (

let ctx_u_s = (unlazy_as_t FStar_Syntax_Syntax.Lazy_uvar l)
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) (FStar_Reflection_Data.Tv_Uvar (((u1), (ctx_u_s)))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2558, ((t2, uu____2560))::((t1, uu____2562))::((b, uu____2564))::((r, uu____2566))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____2597 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_Util.bind_opt uu____2597 (fun r1 -> (

let uu____2603 = (FStar_TypeChecker_NBETerm.unembed e_bv cb b)
in (FStar_Util.bind_opt uu____2603 (fun b1 -> (

let uu____2609 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2609 (fun t11 -> (

let uu____2615 = (FStar_TypeChecker_NBETerm.unembed e_term cb t2)
in (FStar_Util.bind_opt uu____2615 (fun t21 -> (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) (FStar_Reflection_Data.Tv_Let (((r1), (b1), (t11), (t21)))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2623, ((brs, uu____2625))::((t1, uu____2627))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid) -> begin
(

let uu____2650 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2650 (fun t2 -> (

let uu____2656 = (

let uu____2661 = (FStar_TypeChecker_NBETerm.e_list e_branch)
in (FStar_TypeChecker_NBETerm.unembed uu____2661 cb brs))
in (FStar_Util.bind_opt uu____2656 (fun brs1 -> (FStar_All.pipe_left (fun _0_21 -> FStar_Pervasives_Native.Some (_0_21)) (FStar_Reflection_Data.Tv_Match (((t2), (brs1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2679, ((tacopt, uu____2681))::((t1, uu____2683))::((e, uu____2685))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid) -> begin
(

let uu____2712 = (FStar_TypeChecker_NBETerm.unembed e_term cb e)
in (FStar_Util.bind_opt uu____2712 (fun e1 -> (

let uu____2718 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____2718 (fun t2 -> (

let uu____2724 = (

let uu____2729 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____2729 cb tacopt))
in (FStar_Util.bind_opt uu____2724 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22)) (FStar_Reflection_Data.Tv_AscribedT (((e1), (t2), (tacopt1))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2747, ((tacopt, uu____2749))::((c, uu____2751))::((e, uu____2753))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid) -> begin
(

let uu____2780 = (FStar_TypeChecker_NBETerm.unembed e_term cb e)
in (FStar_Util.bind_opt uu____2780 (fun e1 -> (

let uu____2786 = (FStar_TypeChecker_NBETerm.unembed e_comp cb c)
in (FStar_Util.bind_opt uu____2786 (fun c1 -> (

let uu____2792 = (

let uu____2797 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____2797 cb tacopt))
in (FStar_Util.bind_opt uu____2792 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_23 -> FStar_Pervasives_Native.Some (_0_23)) (FStar_Reflection_Data.Tv_AscribedC (((e1), (c1), (tacopt1))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2815, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_24 -> FStar_Pervasives_Native.Some (_0_24)) FStar_Reflection_Data.Tv_Unknown)
end
| uu____2832 -> begin
((

let uu____2834 = (

let uu____2839 = (

let uu____2840 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded term_view: %s" uu____2840))
in ((FStar_Errors.Warning_NotEmbedded), (uu____2839)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____2834));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_term_view unembed_term_view FStar_Reflection_Data.fstar_refl_term_view_fv))))


let e_term_view : FStar_Reflection_Data.term_view FStar_TypeChecker_NBETerm.embedding = (e_term_view_aq [])


let e_bv_view : FStar_Reflection_Data.bv_view FStar_TypeChecker_NBETerm.embedding = (

let embed_bv_view = (fun cb bvv -> (

let uu____2862 = (

let uu____2869 = (

let uu____2874 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string cb bvv.FStar_Reflection_Data.bv_ppname)
in (FStar_TypeChecker_NBETerm.as_arg uu____2874))
in (

let uu____2875 = (

let uu____2882 = (

let uu____2887 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int cb bvv.FStar_Reflection_Data.bv_index)
in (FStar_TypeChecker_NBETerm.as_arg uu____2887))
in (

let uu____2888 = (

let uu____2895 = (

let uu____2900 = (FStar_TypeChecker_NBETerm.embed e_term cb bvv.FStar_Reflection_Data.bv_sort)
in (FStar_TypeChecker_NBETerm.as_arg uu____2900))
in (uu____2895)::[])
in (uu____2882)::uu____2888))
in (uu____2869)::uu____2875))
in (mkConstruct FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.fv [] uu____2862)))
in (

let unembed_bv_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____2933, ((s, uu____2935))::((idx, uu____2937))::((nm, uu____2939))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid) -> begin
(

let uu____2966 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_string cb nm)
in (FStar_Util.bind_opt uu____2966 (fun nm1 -> (

let uu____2972 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb idx)
in (FStar_Util.bind_opt uu____2972 (fun idx1 -> (

let uu____2978 = (FStar_TypeChecker_NBETerm.unembed e_term cb s)
in (FStar_Util.bind_opt uu____2978 (fun s1 -> (FStar_All.pipe_left (fun _0_25 -> FStar_Pervasives_Native.Some (_0_25)) {FStar_Reflection_Data.bv_ppname = nm1; FStar_Reflection_Data.bv_index = idx1; FStar_Reflection_Data.bv_sort = s1}))))))))))
end
| uu____2985 -> begin
((

let uu____2987 = (

let uu____2992 = (

let uu____2993 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded bv_view: %s" uu____2993))
in ((FStar_Errors.Warning_NotEmbedded), (uu____2992)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____2987));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_bv_view unembed_bv_view FStar_Reflection_Data.fstar_refl_bv_view_fv)))


let e_comp_view : FStar_Reflection_Data.comp_view FStar_TypeChecker_NBETerm.embedding = (

let embed_comp_view = (fun cb cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, md) -> begin
(

let uu____3013 = (

let uu____3020 = (

let uu____3025 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____3025))
in (

let uu____3026 = (

let uu____3033 = (

let uu____3038 = (

let uu____3039 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.embed uu____3039 cb md))
in (FStar_TypeChecker_NBETerm.as_arg uu____3038))
in (uu____3033)::[])
in (uu____3020)::uu____3026))
in (mkConstruct FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.fv [] uu____3013))
end
| FStar_Reflection_Data.C_Lemma (pre, post) -> begin
(

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let uu____3063 = (

let uu____3070 = (

let uu____3075 = (FStar_TypeChecker_NBETerm.embed e_term cb pre)
in (FStar_TypeChecker_NBETerm.as_arg uu____3075))
in (

let uu____3076 = (

let uu____3083 = (

let uu____3088 = (FStar_TypeChecker_NBETerm.embed e_term cb post1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3088))
in (uu____3083)::[])
in (uu____3070)::uu____3076))
in (mkConstruct FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.fv [] uu____3063)))
end
| FStar_Reflection_Data.C_Unknown -> begin
(mkConstruct FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_comp_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3121, ((md, uu____3123))::((t1, uu____3125))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid) -> begin
(

let uu____3148 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____3148 (fun t2 -> (

let uu____3154 = (

let uu____3159 = (FStar_TypeChecker_NBETerm.e_option e_term)
in (FStar_TypeChecker_NBETerm.unembed uu____3159 cb md))
in (FStar_Util.bind_opt uu____3154 (fun md1 -> (FStar_All.pipe_left (fun _0_26 -> FStar_Pervasives_Native.Some (_0_26)) (FStar_Reflection_Data.C_Total (((t2), (md1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3177, ((post, uu____3179))::((pre, uu____3181))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid) -> begin
(

let uu____3204 = (FStar_TypeChecker_NBETerm.unembed e_term cb pre)
in (FStar_Util.bind_opt uu____3204 (fun pre1 -> (

let uu____3210 = (FStar_TypeChecker_NBETerm.unembed e_term cb post)
in (FStar_Util.bind_opt uu____3210 (fun post1 -> (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) (FStar_Reflection_Data.C_Lemma (((pre1), (post1)))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3218, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_28 -> FStar_Pervasives_Native.Some (_0_28)) FStar_Reflection_Data.C_Unknown)
end
| uu____3235 -> begin
((

let uu____3237 = (

let uu____3242 = (

let uu____3243 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded comp_view: %s" uu____3243))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3242)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3237));
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
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3285, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Lt)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3301, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Eq)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3317, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Gt)
end
| uu____3332 -> begin
((

let uu____3334 = (

let uu____3339 = (

let uu____3340 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded order: %s" uu____3340))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3339)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3334));
FStar_Pervasives_Native.None;
)
end))
in (

let uu____3341 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.order_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (mk_emb' embed_order unembed_order uu____3341))))


let e_sigelt : FStar_Syntax_Syntax.sigelt FStar_TypeChecker_NBETerm.embedding = (

let embed_sigelt = (fun cb se -> (mk_lazy cb se FStar_Reflection_Data.fstar_refl_sigelt FStar_Syntax_Syntax.Lazy_sigelt))
in (

let unembed_sigelt = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Lazy (FStar_Util.Inl ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_sigelt; FStar_Syntax_Syntax.ltyp = uu____3371; FStar_Syntax_Syntax.rng = uu____3372}), uu____3373) -> begin
(

let uu____3392 = (FStar_Dyn.undyn b)
in FStar_Pervasives_Native.Some (uu____3392))
end
| uu____3393 -> begin
((

let uu____3395 = (

let uu____3400 = (

let uu____3401 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded sigelt: %s" uu____3401))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3400)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3395));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt_fv)))


let e_ident : FStar_Ident.ident FStar_TypeChecker_NBETerm.embedding = (

let repr = (FStar_TypeChecker_NBETerm.e_tuple2 FStar_TypeChecker_NBETerm.e_range FStar_TypeChecker_NBETerm.e_string)
in (

let embed_ident = (fun cb i -> (

let uu____3424 = (

let uu____3429 = (FStar_Ident.range_of_id i)
in (

let uu____3430 = (FStar_Ident.text_of_id i)
in ((uu____3429), (uu____3430))))
in (FStar_TypeChecker_NBETerm.embed repr cb uu____3424)))
in (

let unembed_ident = (fun cb t -> (

let uu____3450 = (FStar_TypeChecker_NBETerm.unembed repr cb t)
in (match (uu____3450) with
| FStar_Pervasives_Native.Some (rng, s) -> begin
(

let uu____3469 = (FStar_Ident.mk_ident ((s), (rng)))
in FStar_Pervasives_Native.Some (uu____3469))
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

let uu____3477 = (

let uu____3484 = (FStar_Ident.string_of_lid FStar_Parser_Const.lid_tuple2)
in (

let uu____3485 = (

let uu____3488 = (fv_as_emb_typ range_fv)
in (

let uu____3489 = (

let uu____3492 = (fv_as_emb_typ string_fv)
in (uu____3492)::[])
in (uu____3488)::uu____3489))
in ((uu____3484), (uu____3485))))
in FStar_Syntax_Syntax.ET_app (uu____3477))
in (

let uu____3495 = (

let uu____3496 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.lid_tuple2 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____3497 = (

let uu____3504 = (

let uu____3509 = (mkFV range_fv [] [])
in (FStar_TypeChecker_NBETerm.as_arg uu____3509))
in (

let uu____3514 = (

let uu____3521 = (

let uu____3526 = (mkFV string_fv [] [])
in (FStar_TypeChecker_NBETerm.as_arg uu____3526))
in (uu____3521)::[])
in (uu____3504)::uu____3514))
in (mkFV uu____3496 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[]) uu____3497)))
in (FStar_TypeChecker_NBETerm.mk_emb embed_ident unembed_ident uu____3495 et))))))))


let e_univ_name : FStar_Syntax_Syntax.univ_name FStar_TypeChecker_NBETerm.embedding = e_ident


let e_univ_names : FStar_Syntax_Syntax.univ_name Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_univ_name)


let e_string_list : Prims.string Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_string)


let e_sigelt_view : FStar_Reflection_Data.sigelt_view FStar_TypeChecker_NBETerm.embedding = (

let embed_sigelt_view = (fun cb sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Let (r, fv, univs1, ty, t) -> begin
(

let uu____3575 = (

let uu____3582 = (

let uu____3587 = (FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_TypeChecker_NBETerm.as_arg uu____3587))
in (

let uu____3588 = (

let uu____3595 = (

let uu____3600 = (FStar_TypeChecker_NBETerm.embed e_fv cb fv)
in (FStar_TypeChecker_NBETerm.as_arg uu____3600))
in (

let uu____3601 = (

let uu____3608 = (

let uu____3613 = (FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3613))
in (

let uu____3616 = (

let uu____3623 = (

let uu____3628 = (FStar_TypeChecker_NBETerm.embed e_term cb ty)
in (FStar_TypeChecker_NBETerm.as_arg uu____3628))
in (

let uu____3629 = (

let uu____3636 = (

let uu____3641 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____3641))
in (uu____3636)::[])
in (uu____3623)::uu____3629))
in (uu____3608)::uu____3616))
in (uu____3595)::uu____3601))
in (uu____3582)::uu____3588))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.fv [] uu____3575))
end
| FStar_Reflection_Data.Sg_Constructor (nm, ty) -> begin
(

let uu____3668 = (

let uu____3675 = (

let uu____3680 = (FStar_TypeChecker_NBETerm.embed e_string_list cb nm)
in (FStar_TypeChecker_NBETerm.as_arg uu____3680))
in (

let uu____3683 = (

let uu____3690 = (

let uu____3695 = (FStar_TypeChecker_NBETerm.embed e_term cb ty)
in (FStar_TypeChecker_NBETerm.as_arg uu____3695))
in (uu____3690)::[])
in (uu____3675)::uu____3683))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.fv [] uu____3668))
end
| FStar_Reflection_Data.Sg_Inductive (nm, univs1, bs, t, dcs) -> begin
(

let uu____3725 = (

let uu____3732 = (

let uu____3737 = (FStar_TypeChecker_NBETerm.embed e_string_list cb nm)
in (FStar_TypeChecker_NBETerm.as_arg uu____3737))
in (

let uu____3740 = (

let uu____3747 = (

let uu____3752 = (FStar_TypeChecker_NBETerm.embed e_univ_names cb univs1)
in (FStar_TypeChecker_NBETerm.as_arg uu____3752))
in (

let uu____3755 = (

let uu____3762 = (

let uu____3767 = (FStar_TypeChecker_NBETerm.embed e_binders cb bs)
in (FStar_TypeChecker_NBETerm.as_arg uu____3767))
in (

let uu____3768 = (

let uu____3775 = (

let uu____3780 = (FStar_TypeChecker_NBETerm.embed e_term cb t)
in (FStar_TypeChecker_NBETerm.as_arg uu____3780))
in (

let uu____3781 = (

let uu____3788 = (

let uu____3793 = (

let uu____3794 = (FStar_TypeChecker_NBETerm.e_list e_string_list)
in (FStar_TypeChecker_NBETerm.embed uu____3794 cb dcs))
in (FStar_TypeChecker_NBETerm.as_arg uu____3793))
in (uu____3788)::[])
in (uu____3775)::uu____3781))
in (uu____3762)::uu____3768))
in (uu____3747)::uu____3755))
in (uu____3732)::uu____3740))
in (mkConstruct FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.fv [] uu____3725))
end
| FStar_Reflection_Data.Unk -> begin
(mkConstruct FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.fv [] [])
end))
in (

let unembed_sigelt_view = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3851, ((dcs, uu____3853))::((t1, uu____3855))::((bs, uu____3857))::((us, uu____3859))::((nm, uu____3861))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid) -> begin
(

let uu____3896 = (FStar_TypeChecker_NBETerm.unembed e_string_list cb nm)
in (FStar_Util.bind_opt uu____3896 (fun nm1 -> (

let uu____3910 = (FStar_TypeChecker_NBETerm.unembed e_univ_names cb us)
in (FStar_Util.bind_opt uu____3910 (fun us1 -> (

let uu____3924 = (FStar_TypeChecker_NBETerm.unembed e_binders cb bs)
in (FStar_Util.bind_opt uu____3924 (fun bs1 -> (

let uu____3930 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____3930 (fun t2 -> (

let uu____3936 = (

let uu____3943 = (FStar_TypeChecker_NBETerm.e_list e_string_list)
in (FStar_TypeChecker_NBETerm.unembed uu____3943 cb dcs))
in (FStar_Util.bind_opt uu____3936 (fun dcs1 -> (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) (FStar_Reflection_Data.Sg_Inductive (((nm1), (us1), (bs1), (t2), (dcs1))))))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____3975, ((t1, uu____3977))::((ty, uu____3979))::((univs1, uu____3981))::((fvar1, uu____3983))::((r, uu____3985))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____4020 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_bool cb r)
in (FStar_Util.bind_opt uu____4020 (fun r1 -> (

let uu____4026 = (FStar_TypeChecker_NBETerm.unembed e_fv cb fvar1)
in (FStar_Util.bind_opt uu____4026 (fun fvar2 -> (

let uu____4032 = (FStar_TypeChecker_NBETerm.unembed e_univ_names cb univs1)
in (FStar_Util.bind_opt uu____4032 (fun univs2 -> (

let uu____4046 = (FStar_TypeChecker_NBETerm.unembed e_term cb ty)
in (FStar_Util.bind_opt uu____4046 (fun ty1 -> (

let uu____4052 = (FStar_TypeChecker_NBETerm.unembed e_term cb t1)
in (FStar_Util.bind_opt uu____4052 (fun t2 -> (FStar_All.pipe_left (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)) (FStar_Reflection_Data.Sg_Let (((r1), (fvar2), (univs2), (ty1), (t2))))))))))))))))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4062, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unk)
end
| uu____4077 -> begin
((

let uu____4079 = (

let uu____4084 = (

let uu____4085 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4085))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4084)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4079));
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

let uu____4104 = (

let uu____4111 = (FStar_TypeChecker_NBETerm.as_arg (FStar_TypeChecker_NBETerm.Constant (FStar_TypeChecker_NBETerm.Int (i))))
in (uu____4111)::[])
in (mkConstruct FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.fv [] uu____4104))
end
| FStar_Reflection_Data.Mult (e1, e2) -> begin
(

let uu____4126 = (

let uu____4133 = (

let uu____4138 = (embed_exp cb e1)
in (FStar_TypeChecker_NBETerm.as_arg uu____4138))
in (

let uu____4139 = (

let uu____4146 = (

let uu____4151 = (embed_exp cb e2)
in (FStar_TypeChecker_NBETerm.as_arg uu____4151))
in (uu____4146)::[])
in (uu____4133)::uu____4139))
in (mkConstruct FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.fv [] uu____4126))
end))
in (

let rec unembed_exp = (fun cb t -> (match (t) with
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4180, []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unit)
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4196, ((i, uu____4198))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____4217 = (FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_int cb i)
in (FStar_Util.bind_opt uu____4217 (fun i1 -> (FStar_All.pipe_left (fun _0_31 -> FStar_Pervasives_Native.Some (_0_31)) (FStar_Reflection_Data.Var (i1))))))
end
| FStar_TypeChecker_NBETerm.Construct (fv, uu____4225, ((e2, uu____4227))::((e1, uu____4229))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid) -> begin
(

let uu____4252 = (unembed_exp cb e1)
in (FStar_Util.bind_opt uu____4252 (fun e11 -> (

let uu____4258 = (unembed_exp cb e2)
in (FStar_Util.bind_opt uu____4258 (fun e21 -> (FStar_All.pipe_left (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32)) (FStar_Reflection_Data.Mult (((e11), (e21)))))))))))
end
| uu____4265 -> begin
((

let uu____4267 = (

let uu____4272 = (

let uu____4273 = (FStar_TypeChecker_NBETerm.t_to_string t)
in (FStar_Util.format1 "Not an embedded exp: %s" uu____4273))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4272)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4267));
FStar_Pervasives_Native.None;
)
end))
in (mk_emb' embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp_fv)))


let e_binder_view : FStar_Reflection_Data.binder_view FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_tuple2 e_bv e_aqualv)


let e_attribute : FStar_Syntax_Syntax.attribute FStar_TypeChecker_NBETerm.embedding = e_term


let e_attributes : FStar_Syntax_Syntax.attribute Prims.list FStar_TypeChecker_NBETerm.embedding = (FStar_TypeChecker_NBETerm.e_list e_attribute)





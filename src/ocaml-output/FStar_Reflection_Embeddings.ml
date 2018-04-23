
open Prims
open FStar_Pervasives

let e_bv : FStar_Syntax_Syntax.bv FStar_Syntax_Embeddings.embedding = (

let embed_bv = (fun rng bv -> (FStar_Syntax_Util.mk_lazy bv FStar_Reflection_Data.fstar_refl_bv FStar_Syntax_Syntax.Lazy_bv (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_bv = (fun w t -> (

let uu____29 = (

let uu____30 = (FStar_Syntax_Subst.compress t)
in uu____30.FStar_Syntax_Syntax.n)
in (match (uu____29) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_bv) -> begin
(

let uu____36 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____36))
end
| uu____37 -> begin
((match (w) with
| true -> begin
(

let uu____39 = (

let uu____44 = (

let uu____45 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded bv: %s" uu____45))
in ((FStar_Errors.Warning_NotEmbedded), (uu____44)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____39))
end
| uu____46 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_bv unembed_bv FStar_Reflection_Data.fstar_refl_bv)))


let e_binder : FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding = (

let embed_binder = (fun rng b -> (FStar_Syntax_Util.mk_lazy b FStar_Reflection_Data.fstar_refl_binder FStar_Syntax_Syntax.Lazy_binder (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_binder = (fun w t -> (

let uu____75 = (

let uu____76 = (FStar_Syntax_Subst.compress t)
in uu____76.FStar_Syntax_Syntax.n)
in (match (uu____75) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_binder) -> begin
(

let uu____82 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____82))
end
| uu____83 -> begin
((match (w) with
| true -> begin
(

let uu____85 = (

let uu____90 = (

let uu____91 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded binder: %s" uu____91))
in ((FStar_Errors.Warning_NotEmbedded), (uu____90)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____85))
end
| uu____92 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_binder unembed_binder FStar_Reflection_Data.fstar_refl_binder)))


let rec mapM_opt : 'a 'b . ('a  ->  'b FStar_Pervasives_Native.option)  ->  'a Prims.list  ->  'b Prims.list FStar_Pervasives_Native.option = (fun f l -> (match (l) with
| [] -> begin
FStar_Pervasives_Native.Some ([])
end
| (x)::xs -> begin
(

let uu____138 = (f x)
in (FStar_Util.bind_opt uu____138 (fun x1 -> (

let uu____146 = (mapM_opt f xs)
in (FStar_Util.bind_opt uu____146 (fun xs1 -> FStar_Pervasives_Native.Some ((x1)::xs1)))))))
end))


let e_term_aq : FStar_Syntax_Syntax.antiquotations  ->  FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding = (fun aq -> (

let embed_term = (fun rng t -> (

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = aq}
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_quoted (((t), (qi)))) FStar_Pervasives_Native.None rng)))
in (

let rec unembed_term = (fun w t -> (

let apply_antiquotes = (fun t1 aq1 -> (

let uu____212 = (mapM_opt (fun uu____229 -> (match (uu____229) with
| (bv, b, e) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.NT (((bv), (e))))
end
| uu____251 -> begin
(

let uu____252 = (unembed_term w e)
in (FStar_Util.bind_opt uu____252 (fun e1 -> FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.NT (((bv), (e1)))))))
end)
end)) aq1)
in (FStar_Util.bind_opt uu____212 (fun s -> (

let uu____266 = (FStar_Syntax_Subst.subst s t1)
in FStar_Pervasives_Native.Some (uu____266))))))
in (

let uu____267 = (

let uu____268 = (FStar_Syntax_Subst.compress t)
in uu____268.FStar_Syntax_Syntax.n)
in (match (uu____267) with
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(apply_antiquotes tm qi.FStar_Syntax_Syntax.antiquotes)
end
| uu____279 -> begin
((match (w) with
| true -> begin
(

let uu____281 = (

let uu____286 = (

let uu____287 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded term: %s" uu____287))
in ((FStar_Errors.Warning_NotEmbedded), (uu____286)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____281))
end
| uu____288 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_term unembed_term FStar_Syntax_Syntax.t_term))))


let e_term : FStar_Syntax_Syntax.term FStar_Syntax_Embeddings.embedding = (e_term_aq [])


let e_aqualv : FStar_Reflection_Data.aqualv FStar_Syntax_Embeddings.embedding = (

let embed_aqualv = (fun rng q -> (

let r = (match (q) with
| FStar_Reflection_Data.Q_Explicit -> begin
FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.t
end
| FStar_Reflection_Data.Q_Implicit -> begin
FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.t
end)
in (

let uu___55_317 = r
in {FStar_Syntax_Syntax.n = uu___55_317.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___55_317.FStar_Syntax_Syntax.vars})))
in (

let unembed_aqualv = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____336 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____336) with
| (hd1, args) -> begin
(

let uu____375 = (

let uu____388 = (

let uu____389 = (FStar_Syntax_Util.un_uinst hd1)
in uu____389.FStar_Syntax_Syntax.n)
in ((uu____388), (args)))
in (match (uu____375) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Explicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Explicit)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Implicit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Q_Implicit)
end
| uu____432 -> begin
((match (w) with
| true -> begin
(

let uu____446 = (

let uu____451 = (

let uu____452 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded aqualv: %s" uu____452))
in ((FStar_Errors.Warning_NotEmbedded), (uu____451)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____446))
end
| uu____453 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_aqualv unembed_aqualv FStar_Reflection_Data.fstar_refl_aqualv)))


let e_binders : FStar_Syntax_Syntax.binder Prims.list FStar_Syntax_Embeddings.embedding = (FStar_Syntax_Embeddings.e_list e_binder)


let e_fv : FStar_Syntax_Syntax.fv FStar_Syntax_Embeddings.embedding = (

let embed_fv = (fun rng fv -> (FStar_Syntax_Util.mk_lazy fv FStar_Reflection_Data.fstar_refl_fv FStar_Syntax_Syntax.Lazy_fvar (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_fv = (fun w t -> (

let uu____486 = (

let uu____487 = (FStar_Syntax_Subst.compress t)
in uu____487.FStar_Syntax_Syntax.n)
in (match (uu____486) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_fvar) -> begin
(

let uu____493 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____493))
end
| uu____494 -> begin
((match (w) with
| true -> begin
(

let uu____496 = (

let uu____501 = (

let uu____502 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded fvar: %s" uu____502))
in ((FStar_Errors.Warning_NotEmbedded), (uu____501)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____496))
end
| uu____503 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_fv unembed_fv FStar_Reflection_Data.fstar_refl_fv)))


let e_comp : FStar_Syntax_Syntax.comp FStar_Syntax_Embeddings.embedding = (

let embed_comp = (fun rng c -> (FStar_Syntax_Util.mk_lazy c FStar_Reflection_Data.fstar_refl_comp FStar_Syntax_Syntax.Lazy_comp (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_comp = (fun w t -> (

let uu____532 = (

let uu____533 = (FStar_Syntax_Subst.compress t)
in uu____533.FStar_Syntax_Syntax.n)
in (match (uu____532) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_comp) -> begin
(

let uu____539 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____539))
end
| uu____540 -> begin
((match (w) with
| true -> begin
(

let uu____542 = (

let uu____547 = (

let uu____548 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded comp: %s" uu____548))
in ((FStar_Errors.Warning_NotEmbedded), (uu____547)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____542))
end
| uu____549 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_comp unembed_comp FStar_Reflection_Data.fstar_refl_comp)))


let e_env : FStar_TypeChecker_Env.env FStar_Syntax_Embeddings.embedding = (

let embed_env = (fun rng e -> (FStar_Syntax_Util.mk_lazy e FStar_Reflection_Data.fstar_refl_env FStar_Syntax_Syntax.Lazy_env (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_env = (fun w t -> (

let uu____578 = (

let uu____579 = (FStar_Syntax_Subst.compress t)
in uu____579.FStar_Syntax_Syntax.n)
in (match (uu____578) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_env) -> begin
(

let uu____585 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____585))
end
| uu____586 -> begin
((match (w) with
| true -> begin
(

let uu____588 = (

let uu____593 = (

let uu____594 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded env: %s" uu____594))
in ((FStar_Errors.Warning_NotEmbedded), (uu____593)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____588))
end
| uu____595 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_env unembed_env FStar_Reflection_Data.fstar_refl_env)))


let e_const : FStar_Reflection_Data.vconst FStar_Syntax_Embeddings.embedding = (

let embed_const = (fun rng c -> (

let r = (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.t
end
| FStar_Reflection_Data.C_True -> begin
FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.t
end
| FStar_Reflection_Data.C_False -> begin
FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.t
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____615 = (

let uu____620 = (

let uu____621 = (

let uu____628 = (

let uu____629 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Util.exp_int uu____629))
in (FStar_Syntax_Syntax.as_arg uu____628))
in (uu____621)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.t uu____620))
in (uu____615 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.C_String (s) -> begin
(

let uu____645 = (

let uu____650 = (

let uu____651 = (

let uu____658 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng s)
in (FStar_Syntax_Syntax.as_arg uu____658))
in (uu____651)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.t uu____650))
in (uu____645 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end)
in (

let uu___56_673 = r
in {FStar_Syntax_Syntax.n = uu___56_673.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___56_673.FStar_Syntax_Syntax.vars})))
in (

let unembed_const = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____692 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____692) with
| (hd1, args) -> begin
(

let uu____731 = (

let uu____742 = (

let uu____743 = (FStar_Syntax_Util.un_uinst hd1)
in uu____743.FStar_Syntax_Syntax.n)
in ((uu____742), (args)))
in (match (uu____731) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_Unit)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_True.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_True)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_False.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.C_False)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((i, uu____789))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int.FStar_Reflection_Data.lid) -> begin
(

let uu____804 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int i)
in (FStar_Util.bind_opt uu____804 (fun i1 -> (FStar_All.pipe_left (fun _0_17 -> FStar_Pervasives_Native.Some (_0_17)) (FStar_Reflection_Data.C_Int (i1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((s, uu____813))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_String.FStar_Reflection_Data.lid) -> begin
(

let uu____828 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_string s)
in (FStar_Util.bind_opt uu____828 (fun s1 -> (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) (FStar_Reflection_Data.C_String (s1))))))
end
| uu____835 -> begin
((match (w) with
| true -> begin
(

let uu____847 = (

let uu____852 = (

let uu____853 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded vconst: %s" uu____853))
in ((FStar_Errors.Warning_NotEmbedded), (uu____852)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____847))
end
| uu____854 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_const unembed_const FStar_Reflection_Data.fstar_refl_vconst)))


let rec e_pattern' : unit  ->  FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding = (fun uu____861 -> (

let rec embed_pattern = (fun rng p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____874 = (

let uu____879 = (

let uu____880 = (

let uu____887 = (FStar_Syntax_Embeddings.embed e_const rng c)
in (FStar_Syntax_Syntax.as_arg uu____887))
in (uu____880)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.t uu____879))
in (uu____874 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____908 = (

let uu____913 = (

let uu____914 = (

let uu____921 = (FStar_Syntax_Embeddings.embed e_fv rng fv)
in (FStar_Syntax_Syntax.as_arg uu____921))
in (

let uu____922 = (

let uu____931 = (

let uu____938 = (

let uu____939 = (

let uu____944 = (e_pattern' ())
in (FStar_Syntax_Embeddings.e_list uu____944))
in (FStar_Syntax_Embeddings.embed uu____939 rng ps))
in (FStar_Syntax_Syntax.as_arg uu____938))
in (uu____931)::[])
in (uu____914)::uu____922))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.t uu____913))
in (uu____908 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____970 = (

let uu____975 = (

let uu____976 = (

let uu____983 = (FStar_Syntax_Embeddings.embed e_bv rng bv)
in (FStar_Syntax_Syntax.as_arg uu____983))
in (uu____976)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.t uu____975))
in (uu____970 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____999 = (

let uu____1004 = (

let uu____1005 = (

let uu____1012 = (FStar_Syntax_Embeddings.embed e_bv rng bv)
in (FStar_Syntax_Syntax.as_arg uu____1012))
in (uu____1005)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.t uu____1004))
in (uu____999 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Pat_Dot_Term (bv, t) -> begin
(

let uu____1029 = (

let uu____1034 = (

let uu____1035 = (

let uu____1042 = (FStar_Syntax_Embeddings.embed e_bv rng bv)
in (FStar_Syntax_Syntax.as_arg uu____1042))
in (

let uu____1043 = (

let uu____1052 = (

let uu____1059 = (FStar_Syntax_Embeddings.embed e_term rng t)
in (FStar_Syntax_Syntax.as_arg uu____1059))
in (uu____1052)::[])
in (uu____1035)::uu____1043))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.t uu____1034))
in (uu____1029 FStar_Pervasives_Native.None rng))
end))
in (

let rec unembed_pattern = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____1096 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____1096) with
| (hd1, args) -> begin
(

let uu____1135 = (

let uu____1146 = (

let uu____1147 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1147.FStar_Syntax_Syntax.n)
in ((uu____1146), (args)))
in (match (uu____1135) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1160))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant.FStar_Reflection_Data.lid) -> begin
(

let uu____1175 = (FStar_Syntax_Embeddings.unembed e_const c)
in (FStar_Util.bind_opt uu____1175 (fun c1 -> (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) (FStar_Reflection_Data.Pat_Constant (c1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((f, uu____1184))::((ps, uu____1186))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons.FStar_Reflection_Data.lid) -> begin
(

let uu____1205 = (FStar_Syntax_Embeddings.unembed e_fv f)
in (FStar_Util.bind_opt uu____1205 (fun f1 -> (

let uu____1211 = (

let uu____1216 = (

let uu____1221 = (e_pattern' ())
in (FStar_Syntax_Embeddings.e_list uu____1221))
in (FStar_Syntax_Embeddings.unembed uu____1216 ps))
in (FStar_Util.bind_opt uu____1211 (fun ps1 -> (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) (FStar_Reflection_Data.Pat_Cons (((f1), (ps1)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((bv, uu____1238))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____1253 = (FStar_Syntax_Embeddings.unembed e_bv bv)
in (FStar_Util.bind_opt uu____1253 (fun bv1 -> (FStar_All.pipe_left (fun _0_21 -> FStar_Pervasives_Native.Some (_0_21)) (FStar_Reflection_Data.Pat_Var (bv1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((bv, uu____1262))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild.FStar_Reflection_Data.lid) -> begin
(

let uu____1277 = (FStar_Syntax_Embeddings.unembed e_bv bv)
in (FStar_Util.bind_opt uu____1277 (fun bv1 -> (FStar_All.pipe_left (fun _0_22 -> FStar_Pervasives_Native.Some (_0_22)) (FStar_Reflection_Data.Pat_Wild (bv1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((bv, uu____1286))::((t2, uu____1288))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Dot_Term.FStar_Reflection_Data.lid) -> begin
(

let uu____1307 = (FStar_Syntax_Embeddings.unembed e_bv bv)
in (FStar_Util.bind_opt uu____1307 (fun bv1 -> (

let uu____1313 = (FStar_Syntax_Embeddings.unembed e_term t2)
in (FStar_Util.bind_opt uu____1313 (fun t3 -> (FStar_All.pipe_left (fun _0_23 -> FStar_Pervasives_Native.Some (_0_23)) (FStar_Reflection_Data.Pat_Dot_Term (((bv1), (t3)))))))))))
end
| uu____1320 -> begin
((match (w) with
| true -> begin
(

let uu____1332 = (

let uu____1337 = (

let uu____1338 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded pattern: %s" uu____1338))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1337)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____1332))
end
| uu____1339 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_pattern unembed_pattern FStar_Reflection_Data.fstar_refl_pattern))))


let e_pattern : FStar_Reflection_Data.pattern FStar_Syntax_Embeddings.embedding = (e_pattern' ())


let e_branch : (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) FStar_Syntax_Embeddings.embedding = (FStar_Syntax_Embeddings.e_tuple2 e_pattern e_term)


let e_argv : (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv) FStar_Syntax_Embeddings.embedding = (FStar_Syntax_Embeddings.e_tuple2 e_term e_aqualv)


let e_branch_aq : FStar_Syntax_Syntax.antiquotations  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) FStar_Syntax_Embeddings.embedding = (fun aq -> (

let uu____1365 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.e_tuple2 e_pattern uu____1365)))


let e_argv_aq : FStar_Syntax_Syntax.antiquotations  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv) FStar_Syntax_Embeddings.embedding = (fun aq -> (

let uu____1379 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.e_tuple2 uu____1379 e_aqualv)))


let e_term_view_aq : FStar_Syntax_Syntax.antiquotations  ->  FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding = (fun aq -> (

let embed_term_view = (fun rng t -> (match (t) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____1401 = (

let uu____1406 = (

let uu____1407 = (

let uu____1414 = (FStar_Syntax_Embeddings.embed e_fv rng fv)
in (FStar_Syntax_Syntax.as_arg uu____1414))
in (uu____1407)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.t uu____1406))
in (uu____1401 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_BVar (fv) -> begin
(

let uu____1430 = (

let uu____1435 = (

let uu____1436 = (

let uu____1443 = (FStar_Syntax_Embeddings.embed e_bv rng fv)
in (FStar_Syntax_Syntax.as_arg uu____1443))
in (uu____1436)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.t uu____1435))
in (uu____1430 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____1459 = (

let uu____1464 = (

let uu____1465 = (

let uu____1472 = (FStar_Syntax_Embeddings.embed e_bv rng bv)
in (FStar_Syntax_Syntax.as_arg uu____1472))
in (uu____1465)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.t uu____1464))
in (uu____1459 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____1489 = (

let uu____1494 = (

let uu____1495 = (

let uu____1502 = (

let uu____1503 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1503 rng hd1))
in (FStar_Syntax_Syntax.as_arg uu____1502))
in (

let uu____1506 = (

let uu____1515 = (

let uu____1522 = (

let uu____1523 = (e_argv_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1523 rng a))
in (FStar_Syntax_Syntax.as_arg uu____1522))
in (uu____1515)::[])
in (uu____1495)::uu____1506))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.t uu____1494))
in (uu____1489 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Abs (b, t1) -> begin
(

let uu____1556 = (

let uu____1561 = (

let uu____1562 = (

let uu____1569 = (FStar_Syntax_Embeddings.embed e_binder rng b)
in (FStar_Syntax_Syntax.as_arg uu____1569))
in (

let uu____1570 = (

let uu____1579 = (

let uu____1586 = (

let uu____1587 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1587 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____1586))
in (uu____1579)::[])
in (uu____1562)::uu____1570))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.t uu____1561))
in (uu____1556 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Arrow (b, c) -> begin
(

let uu____1612 = (

let uu____1617 = (

let uu____1618 = (

let uu____1625 = (FStar_Syntax_Embeddings.embed e_binder rng b)
in (FStar_Syntax_Syntax.as_arg uu____1625))
in (

let uu____1626 = (

let uu____1635 = (

let uu____1642 = (FStar_Syntax_Embeddings.embed e_comp rng c)
in (FStar_Syntax_Syntax.as_arg uu____1642))
in (uu____1635)::[])
in (uu____1618)::uu____1626))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.t uu____1617))
in (uu____1612 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____1664 = (

let uu____1669 = (

let uu____1670 = (

let uu____1677 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_unit rng ())
in (FStar_Syntax_Syntax.as_arg uu____1677))
in (uu____1670)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.t uu____1669))
in (uu____1664 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Refine (bv, t1) -> begin
(

let uu____1694 = (

let uu____1699 = (

let uu____1700 = (

let uu____1707 = (FStar_Syntax_Embeddings.embed e_bv rng bv)
in (FStar_Syntax_Syntax.as_arg uu____1707))
in (

let uu____1708 = (

let uu____1717 = (

let uu____1724 = (

let uu____1725 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1725 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____1724))
in (uu____1717)::[])
in (uu____1700)::uu____1708))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.t uu____1699))
in (uu____1694 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1749 = (

let uu____1754 = (

let uu____1755 = (

let uu____1762 = (FStar_Syntax_Embeddings.embed e_const rng c)
in (FStar_Syntax_Syntax.as_arg uu____1762))
in (uu____1755)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.t uu____1754))
in (uu____1749 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Uvar (u, g, bs, t1) -> begin
((failwith "FIXME! Embed gamma!");
(

let uu____1782 = (

let uu____1787 = (

let uu____1788 = (

let uu____1795 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng u)
in (FStar_Syntax_Syntax.as_arg uu____1795))
in (

let uu____1796 = (

let uu____1805 = (

let uu____1812 = (

let uu____1813 = (FStar_Syntax_Embeddings.e_list e_binder)
in (FStar_Syntax_Embeddings.embed uu____1813 rng []))
in (FStar_Syntax_Syntax.as_arg uu____1812))
in (

let uu____1820 = (

let uu____1829 = (

let uu____1836 = (

let uu____1837 = (FStar_Syntax_Embeddings.e_list e_binder)
in (FStar_Syntax_Embeddings.embed uu____1837 rng bs))
in (FStar_Syntax_Syntax.as_arg uu____1836))
in (

let uu____1844 = (

let uu____1853 = (

let uu____1860 = (

let uu____1861 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1861 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____1860))
in (uu____1853)::[])
in (uu____1829)::uu____1844))
in (uu____1805)::uu____1820))
in (uu____1788)::uu____1796))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.t uu____1787))
in (uu____1782 FStar_Pervasives_Native.None rng));
)
end
| FStar_Reflection_Data.Tv_Let (r, b, t1, t2) -> begin
(

let uu____1900 = (

let uu____1905 = (

let uu____1906 = (

let uu____1913 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool rng r)
in (FStar_Syntax_Syntax.as_arg uu____1913))
in (

let uu____1914 = (

let uu____1923 = (

let uu____1930 = (FStar_Syntax_Embeddings.embed e_bv rng b)
in (FStar_Syntax_Syntax.as_arg uu____1930))
in (

let uu____1931 = (

let uu____1940 = (

let uu____1947 = (

let uu____1948 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1948 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____1947))
in (

let uu____1951 = (

let uu____1960 = (

let uu____1967 = (

let uu____1968 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____1968 rng t2))
in (FStar_Syntax_Syntax.as_arg uu____1967))
in (uu____1960)::[])
in (uu____1940)::uu____1951))
in (uu____1923)::uu____1931))
in (uu____1906)::uu____1914))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.t uu____1905))
in (uu____1900 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Match (t1, brs) -> begin
(

let uu____2009 = (

let uu____2014 = (

let uu____2015 = (

let uu____2022 = (

let uu____2023 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____2023 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____2022))
in (

let uu____2026 = (

let uu____2035 = (

let uu____2042 = (

let uu____2043 = (

let uu____2052 = (e_branch_aq aq)
in (FStar_Syntax_Embeddings.e_list uu____2052))
in (FStar_Syntax_Embeddings.embed uu____2043 rng brs))
in (FStar_Syntax_Syntax.as_arg uu____2042))
in (uu____2035)::[])
in (uu____2015)::uu____2026))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.t uu____2014))
in (uu____2009 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_AscribedT (e, t1, tacopt) -> begin
(

let uu____2096 = (

let uu____2101 = (

let uu____2102 = (

let uu____2109 = (

let uu____2110 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____2110 rng e))
in (FStar_Syntax_Syntax.as_arg uu____2109))
in (

let uu____2113 = (

let uu____2122 = (

let uu____2129 = (

let uu____2130 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____2130 rng t1))
in (FStar_Syntax_Syntax.as_arg uu____2129))
in (

let uu____2133 = (

let uu____2142 = (

let uu____2149 = (

let uu____2150 = (

let uu____2155 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.e_option uu____2155))
in (FStar_Syntax_Embeddings.embed uu____2150 rng tacopt))
in (FStar_Syntax_Syntax.as_arg uu____2149))
in (uu____2142)::[])
in (uu____2122)::uu____2133))
in (uu____2102)::uu____2113))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.t uu____2101))
in (uu____2096 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) -> begin
(

let uu____2193 = (

let uu____2198 = (

let uu____2199 = (

let uu____2206 = (

let uu____2207 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.embed uu____2207 rng e))
in (FStar_Syntax_Syntax.as_arg uu____2206))
in (

let uu____2210 = (

let uu____2219 = (

let uu____2226 = (FStar_Syntax_Embeddings.embed e_comp rng c)
in (FStar_Syntax_Syntax.as_arg uu____2226))
in (

let uu____2227 = (

let uu____2236 = (

let uu____2243 = (

let uu____2244 = (

let uu____2249 = (e_term_aq aq)
in (FStar_Syntax_Embeddings.e_option uu____2249))
in (FStar_Syntax_Embeddings.embed uu____2244 rng tacopt))
in (FStar_Syntax_Syntax.as_arg uu____2243))
in (uu____2236)::[])
in (uu____2219)::uu____2227))
in (uu____2199)::uu____2210))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.t uu____2198))
in (uu____2193 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
(

let uu___57_2280 = FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.t
in {FStar_Syntax_Syntax.n = uu___57_2280.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___57_2280.FStar_Syntax_Syntax.vars})
end))
in (

let unembed_term_view = (fun w t -> (

let uu____2296 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____2296) with
| (hd1, args) -> begin
(

let uu____2335 = (

let uu____2346 = (

let uu____2347 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2347.FStar_Syntax_Syntax.n)
in ((uu____2346), (args)))
in (match (uu____2335) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____2360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____2375 = (FStar_Syntax_Embeddings.unembed e_bv b)
in (FStar_Util.bind_opt uu____2375 (fun b1 -> (FStar_All.pipe_left (fun _0_24 -> FStar_Pervasives_Native.Some (_0_24)) (FStar_Reflection_Data.Tv_Var (b1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____2384))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_BVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2399 = (FStar_Syntax_Embeddings.unembed e_bv b)
in (FStar_Util.bind_opt uu____2399 (fun b1 -> (FStar_All.pipe_left (fun _0_25 -> FStar_Pervasives_Native.Some (_0_25)) (FStar_Reflection_Data.Tv_BVar (b1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((f, uu____2408))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar.FStar_Reflection_Data.lid) -> begin
(

let uu____2423 = (FStar_Syntax_Embeddings.unembed e_fv f)
in (FStar_Util.bind_opt uu____2423 (fun f1 -> (FStar_All.pipe_left (fun _0_26 -> FStar_Pervasives_Native.Some (_0_26)) (FStar_Reflection_Data.Tv_FVar (f1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____2432))::((r, uu____2434))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App.FStar_Reflection_Data.lid) -> begin
(

let uu____2453 = (FStar_Syntax_Embeddings.unembed e_term l)
in (FStar_Util.bind_opt uu____2453 (fun l1 -> (

let uu____2459 = (FStar_Syntax_Embeddings.unembed e_argv r)
in (FStar_Util.bind_opt uu____2459 (fun r1 -> (FStar_All.pipe_left (fun _0_27 -> FStar_Pervasives_Native.Some (_0_27)) (FStar_Reflection_Data.Tv_App (((l1), (r1)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____2484))::((t1, uu____2486))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs.FStar_Reflection_Data.lid) -> begin
(

let uu____2505 = (FStar_Syntax_Embeddings.unembed e_binder b)
in (FStar_Util.bind_opt uu____2505 (fun b1 -> (

let uu____2511 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2511 (fun t2 -> (FStar_All.pipe_left (fun _0_28 -> FStar_Pervasives_Native.Some (_0_28)) (FStar_Reflection_Data.Tv_Abs (((b1), (t2)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____2520))::((t1, uu____2522))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow.FStar_Reflection_Data.lid) -> begin
(

let uu____2541 = (FStar_Syntax_Embeddings.unembed e_binder b)
in (FStar_Util.bind_opt uu____2541 (fun b1 -> (

let uu____2547 = (FStar_Syntax_Embeddings.unembed e_comp t1)
in (FStar_Util.bind_opt uu____2547 (fun c -> (FStar_All.pipe_left (fun _0_29 -> FStar_Pervasives_Native.Some (_0_29)) (FStar_Reflection_Data.Tv_Arrow (((b1), (c)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____2556))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type.FStar_Reflection_Data.lid) -> begin
(

let uu____2571 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_unit u)
in (FStar_Util.bind_opt uu____2571 (fun u1 -> (FStar_All.pipe_left (fun _0_30 -> FStar_Pervasives_Native.Some (_0_30)) (FStar_Reflection_Data.Tv_Type (()))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____2580))::((t1, uu____2582))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine.FStar_Reflection_Data.lid) -> begin
(

let uu____2601 = (FStar_Syntax_Embeddings.unembed e_bv b)
in (FStar_Util.bind_opt uu____2601 (fun b1 -> (

let uu____2607 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2607 (fun t2 -> (FStar_All.pipe_left (fun _0_31 -> FStar_Pervasives_Native.Some (_0_31)) (FStar_Reflection_Data.Tv_Refine (((b1), (t2)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____2616))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const.FStar_Reflection_Data.lid) -> begin
(

let uu____2631 = (FStar_Syntax_Embeddings.unembed e_const c)
in (FStar_Util.bind_opt uu____2631 (fun c1 -> (FStar_All.pipe_left (fun _0_32 -> FStar_Pervasives_Native.Some (_0_32)) (FStar_Reflection_Data.Tv_Const (c1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____2640))::((g, uu____2642))::((bs, uu____2644))::((t1, uu____2646))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar.FStar_Reflection_Data.lid) -> begin
(

let uu____2673 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int u)
in (FStar_Util.bind_opt uu____2673 (fun u1 -> (

let uu____2679 = (

let uu____2684 = (FStar_Syntax_Embeddings.e_list e_binder)
in (FStar_Syntax_Embeddings.unembed uu____2684 bs))
in (FStar_Util.bind_opt uu____2679 (fun bs1 -> (

let uu____2698 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2698 (fun t2 -> ((failwith "FIXME! UNEMBED GAMMA!");
(FStar_All.pipe_left (fun _0_33 -> FStar_Pervasives_Native.Some (_0_33)) (FStar_Reflection_Data.Tv_Uvar (((u1), ([]), (bs1), (t2)))));
))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____2709))::((b, uu____2711))::((t1, uu____2713))::((t2, uu____2715))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____2742 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool r)
in (FStar_Util.bind_opt uu____2742 (fun r1 -> (

let uu____2748 = (FStar_Syntax_Embeddings.unembed e_bv b)
in (FStar_Util.bind_opt uu____2748 (fun b1 -> (

let uu____2754 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2754 (fun t11 -> (

let uu____2760 = (FStar_Syntax_Embeddings.unembed e_term t2)
in (FStar_Util.bind_opt uu____2760 (fun t21 -> (FStar_All.pipe_left (fun _0_34 -> FStar_Pervasives_Native.Some (_0_34)) (FStar_Reflection_Data.Tv_Let (((r1), (b1), (t11), (t21)))))))))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t1, uu____2769))::((brs, uu____2771))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match.FStar_Reflection_Data.lid) -> begin
(

let uu____2790 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2790 (fun t2 -> (

let uu____2796 = (

let uu____2805 = (FStar_Syntax_Embeddings.e_list e_branch)
in (FStar_Syntax_Embeddings.unembed uu____2805 brs))
in (FStar_Util.bind_opt uu____2796 (fun brs1 -> (FStar_All.pipe_left (fun _0_35 -> FStar_Pervasives_Native.Some (_0_35)) (FStar_Reflection_Data.Tv_Match (((t2), (brs1)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____2844))::((t1, uu____2846))::((tacopt, uu____2848))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscT.FStar_Reflection_Data.lid) -> begin
(

let uu____2871 = (FStar_Syntax_Embeddings.unembed e_term e)
in (FStar_Util.bind_opt uu____2871 (fun e1 -> (

let uu____2877 = (FStar_Syntax_Embeddings.unembed e_term t1)
in (FStar_Util.bind_opt uu____2877 (fun t2 -> (

let uu____2883 = (

let uu____2888 = (FStar_Syntax_Embeddings.e_option e_term)
in (FStar_Syntax_Embeddings.unembed uu____2888 tacopt))
in (FStar_Util.bind_opt uu____2883 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_36 -> FStar_Pervasives_Native.Some (_0_36)) (FStar_Reflection_Data.Tv_AscribedT (((e1), (t2), (tacopt1))))))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____2907))::((c, uu____2909))::((tacopt, uu____2911))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_AscC.FStar_Reflection_Data.lid) -> begin
(

let uu____2934 = (FStar_Syntax_Embeddings.unembed e_term e)
in (FStar_Util.bind_opt uu____2934 (fun e1 -> (

let uu____2940 = (FStar_Syntax_Embeddings.unembed e_comp c)
in (FStar_Util.bind_opt uu____2940 (fun c1 -> (

let uu____2946 = (

let uu____2951 = (FStar_Syntax_Embeddings.e_option e_term)
in (FStar_Syntax_Embeddings.unembed uu____2951 tacopt))
in (FStar_Util.bind_opt uu____2946 (fun tacopt1 -> (FStar_All.pipe_left (fun _0_37 -> FStar_Pervasives_Native.Some (_0_37)) (FStar_Reflection_Data.Tv_AscribedC (((e1), (c1), (tacopt1))))))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_38 -> FStar_Pervasives_Native.Some (_0_38)) FStar_Reflection_Data.Tv_Unknown)
end
| uu____2981 -> begin
((match (w) with
| true -> begin
(

let uu____2993 = (

let uu____2998 = (

let uu____2999 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded term_view: %s" uu____2999))
in ((FStar_Errors.Warning_NotEmbedded), (uu____2998)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2993))
end
| uu____3000 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_term_view unembed_term_view FStar_Reflection_Data.fstar_refl_term_view))))


let e_term_view : FStar_Reflection_Data.term_view FStar_Syntax_Embeddings.embedding = (e_term_view_aq [])


let e_bv_view : FStar_Reflection_Data.bv_view FStar_Syntax_Embeddings.embedding = (

let embed_bv_view = (fun rng bvv -> (

let uu____3024 = (

let uu____3029 = (

let uu____3030 = (

let uu____3037 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string rng bvv.FStar_Reflection_Data.bv_ppname)
in (FStar_Syntax_Syntax.as_arg uu____3037))
in (

let uu____3038 = (

let uu____3047 = (

let uu____3054 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_int rng bvv.FStar_Reflection_Data.bv_index)
in (FStar_Syntax_Syntax.as_arg uu____3054))
in (

let uu____3055 = (

let uu____3064 = (

let uu____3071 = (FStar_Syntax_Embeddings.embed e_term rng bvv.FStar_Reflection_Data.bv_sort)
in (FStar_Syntax_Syntax.as_arg uu____3071))
in (uu____3064)::[])
in (uu____3047)::uu____3055))
in (uu____3030)::uu____3038))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.t uu____3029))
in (uu____3024 FStar_Pervasives_Native.None rng)))
in (

let unembed_bv_view = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____3114 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____3114) with
| (hd1, args) -> begin
(

let uu____3153 = (

let uu____3164 = (

let uu____3165 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3165.FStar_Syntax_Syntax.n)
in ((uu____3164), (args)))
in (match (uu____3153) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____3178))::((idx, uu____3180))::((s, uu____3182))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Mk_bv.FStar_Reflection_Data.lid) -> begin
(

let uu____3205 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_string nm)
in (FStar_Util.bind_opt uu____3205 (fun nm1 -> (

let uu____3211 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int idx)
in (FStar_Util.bind_opt uu____3211 (fun idx1 -> (

let uu____3217 = (FStar_Syntax_Embeddings.unembed e_term s)
in (FStar_Util.bind_opt uu____3217 (fun s1 -> (FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) {FStar_Reflection_Data.bv_ppname = nm1; FStar_Reflection_Data.bv_index = idx1; FStar_Reflection_Data.bv_sort = s1}))))))))))
end
| uu____3224 -> begin
((match (w) with
| true -> begin
(

let uu____3236 = (

let uu____3241 = (

let uu____3242 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded bv_view: %s" uu____3242))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3241)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3236))
end
| uu____3243 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_bv_view unembed_bv_view FStar_Reflection_Data.fstar_refl_bv_view)))


let e_comp_view : FStar_Reflection_Data.comp_view FStar_Syntax_Embeddings.embedding = (

let embed_comp_view = (fun rng cv -> (match (cv) with
| FStar_Reflection_Data.C_Total (t, md) -> begin
(

let uu____3263 = (

let uu____3268 = (

let uu____3269 = (

let uu____3276 = (FStar_Syntax_Embeddings.embed e_term rng t)
in (FStar_Syntax_Syntax.as_arg uu____3276))
in (

let uu____3277 = (

let uu____3286 = (

let uu____3293 = (

let uu____3294 = (FStar_Syntax_Embeddings.e_option e_term)
in (FStar_Syntax_Embeddings.embed uu____3294 rng md))
in (FStar_Syntax_Syntax.as_arg uu____3293))
in (uu____3286)::[])
in (uu____3269)::uu____3277))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.t uu____3268))
in (uu____3263 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.C_Lemma (pre, post) -> begin
(

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let uu____3326 = (

let uu____3331 = (

let uu____3332 = (

let uu____3339 = (FStar_Syntax_Embeddings.embed e_term rng pre)
in (FStar_Syntax_Syntax.as_arg uu____3339))
in (

let uu____3340 = (

let uu____3349 = (

let uu____3356 = (FStar_Syntax_Embeddings.embed e_term rng post1)
in (FStar_Syntax_Syntax.as_arg uu____3356))
in (uu____3349)::[])
in (uu____3332)::uu____3340))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.t uu____3331))
in (uu____3326 FStar_Pervasives_Native.None rng)))
end
| FStar_Reflection_Data.C_Unknown -> begin
(

let uu___58_3377 = FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.t
in {FStar_Syntax_Syntax.n = uu___58_3377.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___58_3377.FStar_Syntax_Syntax.vars})
end))
in (

let unembed_comp_view = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____3394 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____3394) with
| (hd1, args) -> begin
(

let uu____3433 = (

let uu____3444 = (

let uu____3445 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3445.FStar_Syntax_Syntax.n)
in ((uu____3444), (args)))
in (match (uu____3433) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t2, uu____3458))::((md, uu____3460))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Total.FStar_Reflection_Data.lid) -> begin
(

let uu____3479 = (FStar_Syntax_Embeddings.unembed e_term t2)
in (FStar_Util.bind_opt uu____3479 (fun t3 -> (

let uu____3485 = (

let uu____3490 = (FStar_Syntax_Embeddings.e_option e_term)
in (FStar_Syntax_Embeddings.unembed uu____3490 md))
in (FStar_Util.bind_opt uu____3485 (fun md1 -> (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) (FStar_Reflection_Data.C_Total (((t3), (md1)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((pre, uu____3509))::((post, uu____3511))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Lemma.FStar_Reflection_Data.lid) -> begin
(

let uu____3530 = (FStar_Syntax_Embeddings.unembed e_term pre)
in (FStar_Util.bind_opt uu____3530 (fun pre1 -> (

let uu____3536 = (FStar_Syntax_Embeddings.unembed e_term post)
in (FStar_Util.bind_opt uu____3536 (fun post1 -> (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) (FStar_Reflection_Data.C_Lemma (((pre1), (post1)))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unknown.FStar_Reflection_Data.lid) -> begin
(FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) FStar_Reflection_Data.C_Unknown)
end
| uu____3556 -> begin
((match (w) with
| true -> begin
(

let uu____3568 = (

let uu____3573 = (

let uu____3574 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded comp_view: %s" uu____3574))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3573)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3568))
end
| uu____3575 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_comp_view unembed_comp_view FStar_Reflection_Data.fstar_refl_comp_view)))


let e_order : FStar_Order.order FStar_Syntax_Embeddings.embedding = (

let embed_order = (fun rng o -> (

let r = (match (o) with
| FStar_Order.Lt -> begin
FStar_Reflection_Data.ord_Lt
end
| FStar_Order.Eq -> begin
FStar_Reflection_Data.ord_Eq
end
| FStar_Order.Gt -> begin
FStar_Reflection_Data.ord_Gt
end)
in (

let uu___59_3594 = r
in {FStar_Syntax_Syntax.n = uu___59_3594.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___59_3594.FStar_Syntax_Syntax.vars})))
in (

let unembed_order = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____3613 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____3613) with
| (hd1, args) -> begin
(

let uu____3652 = (

let uu____3665 = (

let uu____3666 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3666.FStar_Syntax_Syntax.n)
in ((uu____3665), (args)))
in (match (uu____3652) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Lt)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Eq)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Order.Gt)
end
| uu____3724 -> begin
((match (w) with
| true -> begin
(

let uu____3738 = (

let uu____3743 = (

let uu____3744 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded order: %s" uu____3744))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3743)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____3738))
end
| uu____3745 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_order unembed_order FStar_Syntax_Syntax.t_order)))


let e_sigelt : FStar_Syntax_Syntax.sigelt FStar_Syntax_Embeddings.embedding = (

let embed_sigelt = (fun rng se -> (FStar_Syntax_Util.mk_lazy se FStar_Reflection_Data.fstar_refl_sigelt FStar_Syntax_Syntax.Lazy_sigelt (FStar_Pervasives_Native.Some (rng))))
in (

let unembed_sigelt = (fun w t -> (

let uu____3774 = (

let uu____3775 = (FStar_Syntax_Subst.compress t)
in uu____3775.FStar_Syntax_Syntax.n)
in (match (uu____3774) with
| FStar_Syntax_Syntax.Tm_lazy (i) when (Prims.op_Equality i.FStar_Syntax_Syntax.lkind FStar_Syntax_Syntax.Lazy_sigelt) -> begin
(

let uu____3781 = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in FStar_Pervasives_Native.Some (uu____3781))
end
| uu____3782 -> begin
((match (w) with
| true -> begin
(

let uu____3784 = (

let uu____3789 = (

let uu____3790 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded sigelt: %s" uu____3790))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3789)))
in (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____3784))
end
| uu____3791 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (FStar_Syntax_Embeddings.mk_emb embed_sigelt unembed_sigelt FStar_Reflection_Data.fstar_refl_sigelt)))


let e_sigelt_view : FStar_Reflection_Data.sigelt_view FStar_Syntax_Embeddings.embedding = (

let embed_sigelt_view = (fun rng sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Let (r, fv, ty, t) -> begin
(

let uu____3809 = (

let uu____3814 = (

let uu____3815 = (

let uu____3822 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_bool rng r)
in (FStar_Syntax_Syntax.as_arg uu____3822))
in (

let uu____3823 = (

let uu____3832 = (

let uu____3839 = (FStar_Syntax_Embeddings.embed e_fv rng fv)
in (FStar_Syntax_Syntax.as_arg uu____3839))
in (

let uu____3840 = (

let uu____3849 = (

let uu____3856 = (FStar_Syntax_Embeddings.embed e_term rng ty)
in (FStar_Syntax_Syntax.as_arg uu____3856))
in (

let uu____3857 = (

let uu____3866 = (

let uu____3873 = (FStar_Syntax_Embeddings.embed e_term rng t)
in (FStar_Syntax_Syntax.as_arg uu____3873))
in (uu____3866)::[])
in (uu____3849)::uu____3857))
in (uu____3832)::uu____3840))
in (uu____3815)::uu____3823))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.t uu____3814))
in (uu____3809 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Sg_Constructor (nm, ty) -> begin
(

let uu____3908 = (

let uu____3913 = (

let uu____3914 = (

let uu____3921 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string_list rng nm)
in (FStar_Syntax_Syntax.as_arg uu____3921))
in (

let uu____3924 = (

let uu____3933 = (

let uu____3940 = (FStar_Syntax_Embeddings.embed e_term rng ty)
in (FStar_Syntax_Syntax.as_arg uu____3940))
in (uu____3933)::[])
in (uu____3914)::uu____3924))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Constructor.FStar_Reflection_Data.t uu____3913))
in (uu____3908 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Sg_Inductive (nm, bs, t, dcs) -> begin
(

let uu____3973 = (

let uu____3978 = (

let uu____3979 = (

let uu____3986 = (FStar_Syntax_Embeddings.embed FStar_Syntax_Embeddings.e_string_list rng nm)
in (FStar_Syntax_Syntax.as_arg uu____3986))
in (

let uu____3989 = (

let uu____3998 = (

let uu____4005 = (FStar_Syntax_Embeddings.embed e_binders rng bs)
in (FStar_Syntax_Syntax.as_arg uu____4005))
in (

let uu____4008 = (

let uu____4017 = (

let uu____4024 = (FStar_Syntax_Embeddings.embed e_term rng t)
in (FStar_Syntax_Syntax.as_arg uu____4024))
in (

let uu____4025 = (

let uu____4034 = (

let uu____4041 = (

let uu____4042 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string_list)
in (FStar_Syntax_Embeddings.embed uu____4042 rng dcs))
in (FStar_Syntax_Syntax.as_arg uu____4041))
in (uu____4034)::[])
in (uu____4017)::uu____4025))
in (uu____3998)::uu____4008))
in (uu____3979)::uu____3989))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.t uu____3978))
in (uu____3973 FStar_Pervasives_Native.None rng))
end
| FStar_Reflection_Data.Unk -> begin
(

let uu___60_4087 = FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.t
in {FStar_Syntax_Syntax.n = uu___60_4087.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___60_4087.FStar_Syntax_Syntax.vars})
end))
in (

let unembed_sigelt_view = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____4104 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4104) with
| (hd1, args) -> begin
(

let uu____4143 = (

let uu____4154 = (

let uu____4155 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4155.FStar_Syntax_Syntax.n)
in ((uu____4154), (args)))
in (match (uu____4143) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____4168))::((bs, uu____4170))::((t2, uu____4172))::((dcs, uu____4174))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive.FStar_Reflection_Data.lid) -> begin
(

let uu____4201 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_string_list nm)
in (FStar_Util.bind_opt uu____4201 (fun nm1 -> (

let uu____4215 = (FStar_Syntax_Embeddings.unembed e_binders bs)
in (FStar_Util.bind_opt uu____4215 (fun bs1 -> (

let uu____4229 = (FStar_Syntax_Embeddings.unembed e_term t2)
in (FStar_Util.bind_opt uu____4229 (fun t3 -> (

let uu____4235 = (

let uu____4242 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string_list)
in (FStar_Syntax_Embeddings.unembed uu____4242 dcs))
in (FStar_Util.bind_opt uu____4235 (fun dcs1 -> (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) (FStar_Reflection_Data.Sg_Inductive (((nm1), (bs1), (t3), (dcs1)))))))))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____4273))::((fvar1, uu____4275))::((ty, uu____4277))::((t2, uu____4279))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Let.FStar_Reflection_Data.lid) -> begin
(

let uu____4306 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_bool r)
in (FStar_Util.bind_opt uu____4306 (fun r1 -> (

let uu____4312 = (FStar_Syntax_Embeddings.unembed e_fv fvar1)
in (FStar_Util.bind_opt uu____4312 (fun fvar2 -> (

let uu____4318 = (FStar_Syntax_Embeddings.unembed e_term ty)
in (FStar_Util.bind_opt uu____4318 (fun ty1 -> (

let uu____4324 = (FStar_Syntax_Embeddings.unembed e_term t2)
in (FStar_Util.bind_opt uu____4324 (fun t3 -> (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) (FStar_Reflection_Data.Sg_Let (((r1), (fvar2), (ty1), (t3)))))))))))))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unk)
end
| uu____4342 -> begin
((match (w) with
| true -> begin
(

let uu____4354 = (

let uu____4359 = (

let uu____4360 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded sigelt_view: %s" uu____4360))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4359)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4354))
end
| uu____4361 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_sigelt_view unembed_sigelt_view FStar_Reflection_Data.fstar_refl_sigelt_view)))


let e_exp : FStar_Reflection_Data.exp FStar_Syntax_Embeddings.embedding = (

let rec embed_exp = (fun rng e -> (

let r = (match (e) with
| FStar_Reflection_Data.Unit -> begin
FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.t
end
| FStar_Reflection_Data.Var (i) -> begin
(

let uu____4381 = (

let uu____4386 = (

let uu____4387 = (

let uu____4394 = (

let uu____4395 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Util.exp_int uu____4395))
in (FStar_Syntax_Syntax.as_arg uu____4394))
in (uu____4387)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.t uu____4386))
in (uu____4381 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Mult (e1, e2) -> begin
(

let uu____4412 = (

let uu____4417 = (

let uu____4418 = (

let uu____4425 = (embed_exp rng e1)
in (FStar_Syntax_Syntax.as_arg uu____4425))
in (

let uu____4426 = (

let uu____4435 = (

let uu____4442 = (embed_exp rng e2)
in (FStar_Syntax_Syntax.as_arg uu____4442))
in (uu____4435)::[])
in (uu____4418)::uu____4426))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.t uu____4417))
in (uu____4412 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end)
in (

let uu___61_4463 = r
in {FStar_Syntax_Syntax.n = uu___61_4463.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___61_4463.FStar_Syntax_Syntax.vars})))
in (

let rec unembed_exp = (fun w t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____4482 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____4482) with
| (hd1, args) -> begin
(

let uu____4521 = (

let uu____4532 = (

let uu____4533 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4533.FStar_Syntax_Syntax.n)
in ((uu____4532), (args)))
in (match (uu____4521) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Unit.FStar_Reflection_Data.lid) -> begin
FStar_Pervasives_Native.Some (FStar_Reflection_Data.Unit)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((i, uu____4557))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Var.FStar_Reflection_Data.lid) -> begin
(

let uu____4572 = (FStar_Syntax_Embeddings.unembed FStar_Syntax_Embeddings.e_int i)
in (FStar_Util.bind_opt uu____4572 (fun i1 -> (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) (FStar_Reflection_Data.Var (i1))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e1, uu____4581))::((e2, uu____4583))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_E_Mult.FStar_Reflection_Data.lid) -> begin
(

let uu____4602 = (unembed_exp w e1)
in (FStar_Util.bind_opt uu____4602 (fun e11 -> (

let uu____4608 = (unembed_exp w e2)
in (FStar_Util.bind_opt uu____4608 (fun e21 -> (FStar_All.pipe_left (fun _0_46 -> FStar_Pervasives_Native.Some (_0_46)) (FStar_Reflection_Data.Mult (((e11), (e21)))))))))))
end
| uu____4615 -> begin
((match (w) with
| true -> begin
(

let uu____4627 = (

let uu____4632 = (

let uu____4633 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format1 "Not an embedded exp: %s" uu____4633))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4632)))
in (FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu____4627))
end
| uu____4634 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))
in (FStar_Syntax_Embeddings.mk_emb embed_exp unembed_exp FStar_Reflection_Data.fstar_refl_exp)))


let e_binder_view : (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv) FStar_Syntax_Embeddings.embedding = (FStar_Syntax_Embeddings.e_tuple2 e_bv e_aqualv)


let unfold_lazy_bv : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let bv = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in (

let uu____4647 = (

let uu____4652 = (

let uu____4653 = (

let uu____4660 = (

let uu____4661 = (FStar_Reflection_Basic.inspect_bv bv)
in (FStar_Syntax_Embeddings.embed e_bv_view i.FStar_Syntax_Syntax.rng uu____4661))
in (FStar_Syntax_Syntax.as_arg uu____4660))
in (uu____4653)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_bv.FStar_Reflection_Data.t uu____4652))
in (uu____4647 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng))))


let unfold_lazy_binder : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let binder = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in (

let uu____4682 = (FStar_Reflection_Basic.inspect_binder binder)
in (match (uu____4682) with
| (bv, aq) -> begin
(

let uu____4689 = (

let uu____4694 = (

let uu____4695 = (

let uu____4702 = (FStar_Syntax_Embeddings.embed e_bv i.FStar_Syntax_Syntax.rng bv)
in (FStar_Syntax_Syntax.as_arg uu____4702))
in (

let uu____4703 = (

let uu____4712 = (

let uu____4719 = (FStar_Syntax_Embeddings.embed e_aqualv i.FStar_Syntax_Syntax.rng aq)
in (FStar_Syntax_Syntax.as_arg uu____4719))
in (uu____4712)::[])
in (uu____4695)::uu____4703))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_binder.FStar_Reflection_Data.t uu____4694))
in (uu____4689 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng))
end))))


let unfold_lazy_fvar : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let fv = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in (

let uu____4746 = (

let uu____4751 = (

let uu____4752 = (

let uu____4759 = (

let uu____4760 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_string)
in (

let uu____4765 = (FStar_Reflection_Basic.inspect_fv fv)
in (FStar_Syntax_Embeddings.embed uu____4760 i.FStar_Syntax_Syntax.rng uu____4765)))
in (FStar_Syntax_Syntax.as_arg uu____4759))
in (uu____4752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_fv.FStar_Reflection_Data.t uu____4751))
in (uu____4746 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng))))


let unfold_lazy_comp : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let comp = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in (

let uu____4790 = (

let uu____4795 = (

let uu____4796 = (

let uu____4803 = (

let uu____4804 = (FStar_Reflection_Basic.inspect_comp comp)
in (FStar_Syntax_Embeddings.embed e_comp_view i.FStar_Syntax_Syntax.rng uu____4804))
in (FStar_Syntax_Syntax.as_arg uu____4803))
in (uu____4796)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_comp.FStar_Reflection_Data.t uu____4795))
in (uu____4790 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng))))


let unfold_lazy_env : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> FStar_Syntax_Util.exp_unit)


let unfold_lazy_sigelt : FStar_Syntax_Syntax.lazyinfo  ->  FStar_Syntax_Syntax.term = (fun i -> (

let sigelt = (FStar_Dyn.undyn i.FStar_Syntax_Syntax.blob)
in (

let uu____4830 = (

let uu____4835 = (

let uu____4836 = (

let uu____4843 = (

let uu____4844 = (FStar_Reflection_Basic.inspect_sigelt sigelt)
in (FStar_Syntax_Embeddings.embed e_sigelt_view i.FStar_Syntax_Syntax.rng uu____4844))
in (FStar_Syntax_Syntax.as_arg uu____4843))
in (uu____4836)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.fstar_refl_pack_sigelt.FStar_Reflection_Data.t uu____4835))
in (uu____4830 FStar_Pervasives_Native.None i.FStar_Syntax_Syntax.rng))))





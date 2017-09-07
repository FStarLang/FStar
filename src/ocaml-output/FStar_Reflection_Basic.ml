
open Prims
open FStar_Pervasives

let lid_as_tm : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (

let uu____5 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____5 FStar_Syntax_Syntax.fv_to_tm)))


let fstar_refl_embed : FStar_Syntax_Syntax.term = (lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid)


let protect_embedded_term : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t x -> (

let uu____16 = (

let uu____17 = (

let uu____18 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____19 = (

let uu____22 = (FStar_Syntax_Syntax.as_arg x)
in (uu____22)::[])
in (uu____18)::uu____19))
in (FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17))
in (uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos)))


let un_protect_embedded_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____29 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____29) with
| (head1, args) -> begin
(

let uu____66 = (

let uu____79 = (

let uu____80 = (FStar_Syntax_Util.un_uinst head1)
in uu____80.FStar_Syntax_Syntax.n)
in ((uu____79), (args)))
in (match (uu____66) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____92)::((x, uu____94))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) -> begin
x
end
| uu____131 -> begin
(

let uu____144 = (

let uu____145 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not a protected embedded term: %s" uu____145))
in (failwith uu____144))
end))
end)))


let embed_binder : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term = (fun b -> (FStar_Syntax_Util.mk_alien b "reflection.embed_binder" FStar_Pervasives_Native.None))


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder = (fun t -> (

let uu____154 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____154 FStar_Dyn.undyn)))


let embed_binders : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term = (fun l -> (FStar_Syntax_Embeddings.embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l))


let unembed_binders : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder Prims.list = (fun t -> (FStar_Syntax_Embeddings.unembed_list unembed_binder t))


let embed_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (protect_embedded_term FStar_Syntax_Syntax.tun t))


let unembed_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (un_protect_embedded_term t))


let embed_fvar : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun fv -> (FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar" FStar_Pervasives_Native.None))


let unembed_fvar : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv = (fun t -> (

let uu____185 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____185 FStar_Dyn.undyn)))


let embed_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term = (fun env -> (FStar_Syntax_Util.mk_alien env "tactics_embed_env" FStar_Pervasives_Native.None))


let unembed_env : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env = (fun t -> (

let uu____194 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____194 FStar_Dyn.undyn)))


let embed_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.term = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Reflection_Data.ref_C_Unit
end
| FStar_Reflection_Data.C_True -> begin
FStar_Reflection_Data.ref_C_True
end
| FStar_Reflection_Data.C_False -> begin
FStar_Reflection_Data.ref_C_False
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____200 = (

let uu____201 = (

let uu____202 = (

let uu____203 = (

let uu____204 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Util.exp_int uu____204))
in (FStar_Syntax_Syntax.as_arg uu____203))
in (uu____202)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int uu____201))
in (uu____200 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.C_String (s) -> begin
(

let uu____208 = (

let uu____209 = (

let uu____210 = (

let uu____211 = (FStar_Syntax_Embeddings.embed_string s)
in (FStar_Syntax_Syntax.as_arg uu____211))
in (uu____210)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String uu____209))
in (uu____208 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_const : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.vconst = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____219 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____219) with
| (hd1, args) -> begin
(

let uu____256 = (

let uu____269 = (

let uu____270 = (FStar_Syntax_Util.un_uinst hd1)
in uu____270.FStar_Syntax_Syntax.n)
in ((uu____269), (args)))
in (match (uu____256) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unit_lid) -> begin
FStar_Reflection_Data.C_Unit
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_True_lid) -> begin
FStar_Reflection_Data.C_True
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_False_lid) -> begin
FStar_Reflection_Data.C_False
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((i, uu____328))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int_lid) -> begin
(

let uu____353 = (FStar_Syntax_Embeddings.unembed_int i)
in FStar_Reflection_Data.C_Int (uu____353))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((s, uu____356))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_String_lid) -> begin
(

let uu____381 = (FStar_Syntax_Embeddings.unembed_string s)
in FStar_Reflection_Data.C_String (uu____381))
end
| uu____382 -> begin
(failwith "not an embedded vconst")
end))
end))))


let rec embed_pattern : FStar_Reflection_Data.pattern  ->  FStar_Syntax_Syntax.term = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____400 = (

let uu____401 = (

let uu____402 = (

let uu____403 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____403))
in (uu____402)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Constant uu____401))
in (uu____400 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____412 = (

let uu____413 = (

let uu____414 = (

let uu____415 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____415))
in (

let uu____416 = (

let uu____419 = (

let uu____420 = (FStar_Syntax_Embeddings.embed_list embed_pattern FStar_Reflection_Data.fstar_refl_pattern ps)
in (FStar_Syntax_Syntax.as_arg uu____420))
in (uu____419)::[])
in (uu____414)::uu____416))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons uu____413))
in (uu____412 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____424 = (

let uu____425 = (

let uu____426 = (

let uu____427 = (

let uu____428 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____428))
in (FStar_Syntax_Syntax.as_arg uu____427))
in (uu____426)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var uu____425))
in (uu____424 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____432 = (

let uu____433 = (

let uu____434 = (

let uu____435 = (

let uu____436 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____436))
in (FStar_Syntax_Syntax.as_arg uu____435))
in (uu____434)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild uu____433))
in (uu____432 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec unembed_pattern : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.pattern = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____444 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____444) with
| (hd1, args) -> begin
(

let uu____481 = (

let uu____494 = (

let uu____495 = (FStar_Syntax_Util.un_uinst hd1)
in uu____495.FStar_Syntax_Syntax.n)
in ((uu____494), (args)))
in (match (uu____481) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____508))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant_lid) -> begin
(

let uu____533 = (unembed_const c)
in FStar_Reflection_Data.Pat_Constant (uu____533))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((f, uu____536))::((ps, uu____538))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons_lid) -> begin
(

let uu____573 = (

let uu____580 = (unembed_fvar f)
in (

let uu____581 = (FStar_Syntax_Embeddings.unembed_list unembed_pattern ps)
in ((uu____580), (uu____581))))
in FStar_Reflection_Data.Pat_Cons (uu____573))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____588))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var_lid) -> begin
(

let uu____613 = (

let uu____614 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____614))
in FStar_Reflection_Data.Pat_Var (uu____613))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____621))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild_lid) -> begin
(

let uu____646 = (

let uu____647 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____647))
in FStar_Reflection_Data.Pat_Wild (uu____646))
end
| uu____652 -> begin
(failwith "not an embedded pattern")
end))
end))))


let embed_branch : (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term = (FStar_Syntax_Embeddings.embed_pair embed_pattern FStar_Reflection_Data.fstar_refl_pattern embed_term FStar_Reflection_Data.fstar_refl_term)


let unembed_branch : FStar_Syntax_Syntax.term  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) = (FStar_Syntax_Embeddings.unembed_pair unembed_pattern unembed_term)


let embed_aqualv : FStar_Reflection_Data.aqualv  ->  FStar_Syntax_Syntax.term = (fun q -> (match (q) with
| FStar_Reflection_Data.Q_Explicit -> begin
FStar_Reflection_Data.ref_Q_Explicit
end
| FStar_Reflection_Data.Q_Implicit -> begin
FStar_Reflection_Data.ref_Q_Implicit
end))


let unembed_aqualv : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.aqualv = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____688 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____688) with
| (hd1, args) -> begin
(

let uu____725 = (

let uu____738 = (

let uu____739 = (FStar_Syntax_Util.un_uinst hd1)
in uu____739.FStar_Syntax_Syntax.n)
in ((uu____738), (args)))
in (match (uu____725) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Explicit_lid) -> begin
FStar_Reflection_Data.Q_Explicit
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Q_Implicit_lid) -> begin
FStar_Reflection_Data.Q_Implicit
end
| uu____780 -> begin
(failwith "not an embedded aqualv")
end))
end))))


let embed_argv : (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv)  ->  FStar_Syntax_Syntax.term = (FStar_Syntax_Embeddings.embed_pair embed_term FStar_Reflection_Data.fstar_refl_term embed_aqualv FStar_Reflection_Data.fstar_refl_aqualv)


let unembed_argv : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Reflection_Data.aqualv) = (FStar_Syntax_Embeddings.unembed_pair unembed_term unembed_aqualv)


let embed_term_view : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun t -> (match (t) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____812 = (

let uu____813 = (

let uu____814 = (

let uu____815 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____815))
in (uu____814)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar uu____813))
in (uu____812 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____819 = (

let uu____820 = (

let uu____821 = (

let uu____822 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____822))
in (uu____821)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var uu____820))
in (uu____819 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____827 = (

let uu____828 = (

let uu____829 = (

let uu____830 = (embed_term hd1)
in (FStar_Syntax_Syntax.as_arg uu____830))
in (

let uu____831 = (

let uu____834 = (

let uu____835 = (embed_argv a)
in (FStar_Syntax_Syntax.as_arg uu____835))
in (uu____834)::[])
in (uu____829)::uu____831))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App uu____828))
in (uu____827 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Abs (b, t1) -> begin
(

let uu____840 = (

let uu____841 = (

let uu____842 = (

let uu____843 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____843))
in (

let uu____844 = (

let uu____847 = (

let uu____848 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____848))
in (uu____847)::[])
in (uu____842)::uu____844))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs uu____841))
in (uu____840 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Arrow (b, t1) -> begin
(

let uu____853 = (

let uu____854 = (

let uu____855 = (

let uu____856 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____856))
in (

let uu____857 = (

let uu____860 = (

let uu____861 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____861))
in (uu____860)::[])
in (uu____855)::uu____857))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow uu____854))
in (uu____853 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____865 = (

let uu____866 = (

let uu____867 = (

let uu____868 = (FStar_Syntax_Embeddings.embed_unit ())
in (FStar_Syntax_Syntax.as_arg uu____868))
in (uu____867)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type uu____866))
in (uu____865 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Refine (bv, t1) -> begin
(

let uu____873 = (

let uu____874 = (

let uu____875 = (

let uu____876 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____876))
in (

let uu____877 = (

let uu____880 = (

let uu____881 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____881))
in (uu____880)::[])
in (uu____875)::uu____877))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine uu____874))
in (uu____873 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____885 = (

let uu____886 = (

let uu____887 = (

let uu____888 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____888))
in (uu____887)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const uu____886))
in (uu____885 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, t1) -> begin
(

let uu____893 = (

let uu____894 = (

let uu____895 = (

let uu____896 = (FStar_Syntax_Embeddings.embed_int u)
in (FStar_Syntax_Syntax.as_arg uu____896))
in (

let uu____897 = (

let uu____900 = (

let uu____901 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____901))
in (uu____900)::[])
in (uu____895)::uu____897))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar uu____894))
in (uu____893 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Match (t1, brs) -> begin
(

let uu____910 = (

let uu____911 = (

let uu____912 = (

let uu____913 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____913))
in (

let uu____914 = (

let uu____917 = (

let uu____918 = (FStar_Syntax_Embeddings.embed_list embed_branch FStar_Reflection_Data.fstar_refl_branch brs)
in (FStar_Syntax_Syntax.as_arg uu____918))
in (uu____917)::[])
in (uu____912)::uu____914))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match uu____911))
in (uu____910 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
FStar_Reflection_Data.ref_Tv_Unknown
end))


let unembed_term_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____930 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____930) with
| (hd1, args) -> begin
(

let uu____967 = (

let uu____980 = (

let uu____981 = (FStar_Syntax_Util.un_uinst hd1)
in uu____981.FStar_Syntax_Syntax.n)
in ((uu____980), (args)))
in (match (uu____967) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____994))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var_lid) -> begin
(

let uu____1019 = (unembed_binder b)
in FStar_Reflection_Data.Tv_Var (uu____1019))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1022))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar_lid) -> begin
(

let uu____1047 = (unembed_fvar b)
in FStar_Reflection_Data.Tv_FVar (uu____1047))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____1050))::((r, uu____1052))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App_lid) -> begin
(

let uu____1087 = (

let uu____1092 = (unembed_term l)
in (

let uu____1093 = (unembed_argv r)
in ((uu____1092), (uu____1093))))
in FStar_Reflection_Data.Tv_App (uu____1087))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1104))::((t2, uu____1106))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs_lid) -> begin
(

let uu____1141 = (

let uu____1146 = (unembed_binder b)
in (

let uu____1147 = (unembed_term t2)
in ((uu____1146), (uu____1147))))
in FStar_Reflection_Data.Tv_Abs (uu____1141))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1150))::((t2, uu____1152))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow_lid) -> begin
(

let uu____1187 = (

let uu____1192 = (unembed_binder b)
in (

let uu____1193 = (unembed_term t2)
in ((uu____1192), (uu____1193))))
in FStar_Reflection_Data.Tv_Arrow (uu____1187))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1196))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type_lid) -> begin
((FStar_Syntax_Embeddings.unembed_unit u);
FStar_Reflection_Data.Tv_Type (());
)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1224))::((t2, uu____1226))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine_lid) -> begin
(

let uu____1261 = (

let uu____1266 = (unembed_binder b)
in (

let uu____1267 = (unembed_term t2)
in ((uu____1266), (uu____1267))))
in FStar_Reflection_Data.Tv_Refine (uu____1261))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1270))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const_lid) -> begin
(

let uu____1295 = (unembed_const c)
in FStar_Reflection_Data.Tv_Const (uu____1295))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1298))::((t2, uu____1300))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar_lid) -> begin
(

let uu____1335 = (

let uu____1340 = (FStar_Syntax_Embeddings.unembed_int u)
in (

let uu____1341 = (unembed_term t2)
in ((uu____1340), (uu____1341))))
in FStar_Reflection_Data.Tv_Uvar (uu____1335))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t2, uu____1344))::((brs, uu____1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match_lid) -> begin
(

let uu____1381 = (

let uu____1388 = (unembed_term t2)
in (

let uu____1389 = (FStar_Syntax_Embeddings.unembed_list unembed_branch brs)
in ((uu____1388), (uu____1389))))
in FStar_Reflection_Data.Tv_Match (uu____1381))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown_lid) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____1421 -> begin
(failwith "not an embedded term_view")
end))
end))))


let rec last : 'a . 'a Prims.list  ->  'a = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____1448)::xs -> begin
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

let uu____1474 = (init xs)
in (x)::uu____1474)
end))


let inspect_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (

let uu____1485 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____1485)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let uu____1494 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____1494 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)))


let inspect_bv : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____1504) -> begin
(

let uu____1517 = (FStar_Util.int_of_string s)
in FStar_Reflection_Data.C_Int (uu____1517))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| FStar_Const.Const_string (s, uu____1519) -> begin
FStar_Reflection_Data.C_String (s)
end
| uu____1520 -> begin
(

let uu____1521 = (

let uu____1522 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____1522))
in (failwith uu____1521))
end))


let rec inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.un_uinst t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (t2, uu____1529) -> begin
(inspect t2)
end
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1535 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Reflection_Data.Tv_Var (uu____1535))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Reflection_Data.Tv_FVar (fv)
end
| FStar_Syntax_Syntax.Tm_app (hd1, []) -> begin
(failwith "inspect: empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____1578 = (last args)
in (match (uu____1578) with
| (a, q) -> begin
(

let q' = (match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____1598)) -> begin
FStar_Reflection_Data.Q_Implicit
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Reflection_Data.Q_Explicit
end
| FStar_Pervasives_Native.None -> begin
FStar_Reflection_Data.Q_Explicit
end)
in (

let uu____1599 = (

let uu____1604 = (

let uu____1607 = (

let uu____1608 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1608))
in (uu____1607 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in ((uu____1604), (((a), (q')))))
in FStar_Reflection_Data.Tv_App (uu____1599)))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____1627, uu____1628) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____1670 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____1670) with
| (bs1, t3) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1697 = (

let uu____1702 = (FStar_Syntax_Util.abs bs2 t3 k)
in ((b), (uu____1702)))
in FStar_Reflection_Data.Tv_Abs (uu____1697))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____1707) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(

let uu____1741 = (FStar_Syntax_Subst.open_comp bs k)
in (match (uu____1741) with
| (bs1, k1) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1768 = (

let uu____1773 = (FStar_Syntax_Util.arrow bs2 k1)
in ((b), (uu____1773)))
in FStar_Reflection_Data.Tv_Arrow (uu____1768))
end)
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t2) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____1789 = (FStar_Syntax_Subst.open_term ((b)::[]) t2)
in (match (uu____1789) with
| (b', t3) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____1818 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.Tv_Refine (((b1), (t3))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1828 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____1828))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t2) -> begin
(

let uu____1855 = (

let uu____1860 = (FStar_Syntax_Unionfind.uvar_id u)
in ((uu____1860), (t2)))
in FStar_Reflection_Data.Tv_Uvar (uu____1855))
end
| FStar_Syntax_Syntax.Tm_match (t2, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____1910 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____1910))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____1929 = (

let uu____1936 = (FStar_List.map (fun uu____1948 -> (match (uu____1948) with
| (p1, uu____1956) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____1936)))
in FStar_Reflection_Data.Pat_Cons (uu____1929))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____1965) -> begin
(failwith "NYI: Pat_dot_term")
end))
in (

let brs1 = (FStar_List.map FStar_Syntax_Subst.open_branch brs)
in (

let brs2 = (FStar_List.map (fun uu___80_2009 -> (match (uu___80_2009) with
| (pat, uu____2031, t3) -> begin
(

let uu____2049 = (inspect_pat pat)
in ((uu____2049), (t3)))
end)) brs1)
in FStar_Reflection_Data.Tv_Match (((t2), (brs2))))))
end
| uu____2062 -> begin
((

let uu____2064 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____2065 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n" uu____2064 uu____2065)));
FStar_Reflection_Data.Tv_Unknown;
)
end)))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____2071 = (

let uu____2082 = (FStar_Util.string_of_int i)
in ((uu____2082), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____2071))
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


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv, uu____2099) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(FStar_Syntax_Syntax.fv_to_tm fv)
end
| FStar_Reflection_Data.Tv_App (l, (r, q)) -> begin
(match (q) with
| FStar_Reflection_Data.Q_Explicit -> begin
(

let uu____2108 = (

let uu____2117 = (FStar_Syntax_Syntax.as_arg r)
in (uu____2117)::[])
in (FStar_Syntax_Util.mk_app l uu____2108))
end
| FStar_Reflection_Data.Q_Implicit -> begin
(

let uu____2118 = (

let uu____2127 = (FStar_Syntax_Syntax.iarg r)
in (uu____2127)::[])
in (FStar_Syntax_Util.mk_app l uu____2118))
end)
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
end
| FStar_Reflection_Data.Tv_Arrow (b, t) -> begin
(

let uu____2132 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow ((b)::[]) uu____2132))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
FStar_Syntax_Util.ktype
end
| FStar_Reflection_Data.Tv_Refine ((bv, uu____2136), t) -> begin
(FStar_Syntax_Util.refine bv t)
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____2143 = (

let uu____2146 = (

let uu____2147 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____2147))
in (FStar_Syntax_Syntax.mk uu____2146))
in (uu____2143 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, t) -> begin
(FStar_Syntax_Util.uvar_from_id u t)
end
| FStar_Reflection_Data.Tv_Match (t, brs) -> begin
(

let wrap = (fun v1 -> {FStar_Syntax_Syntax.v = v1; FStar_Syntax_Syntax.p = FStar_Range.dummyRange})
in (

let rec pack_pat = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____2170 = (

let uu____2171 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____2171))
in (FStar_All.pipe_left wrap uu____2170))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____2180 = (

let uu____2181 = (

let uu____2194 = (FStar_List.map (fun p1 -> (

let uu____2208 = (pack_pat p1)
in ((uu____2208), (false)))) ps)
in ((fv), (uu____2194)))
in FStar_Syntax_Syntax.Pat_cons (uu____2181))
in (FStar_All.pipe_left wrap uu____2180))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var (bv)))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild (bv)))
end))
in (

let brs1 = (FStar_List.map (fun uu___81_2254 -> (match (uu___81_2254) with
| (pat, t1) -> begin
(

let uu____2271 = (pack_pat pat)
in ((uu____2271), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))))
end
| uu____2283 -> begin
(failwith "pack: unexpected term view")
end))


let embed_order : FStar_Order.order  ->  FStar_Syntax_Syntax.term = (fun o -> (match (o) with
| FStar_Order.Lt -> begin
FStar_Reflection_Data.ord_Lt
end
| FStar_Order.Eq -> begin
FStar_Reflection_Data.ord_Eq
end
| FStar_Order.Gt -> begin
FStar_Reflection_Data.ord_Gt
end))


let unembed_order : FStar_Syntax_Syntax.term  ->  FStar_Order.order = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2293 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2293) with
| (hd1, args) -> begin
(

let uu____2330 = (

let uu____2343 = (

let uu____2344 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2344.FStar_Syntax_Syntax.n)
in ((uu____2343), (args)))
in (match (uu____2330) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Order.Lt
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Order.Eq
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Order.Gt
end
| uu____2400 -> begin
(failwith "not an embedded order")
end))
end))))


let compare_binder : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder  ->  FStar_Order.order = (fun x y -> (

let n1 = (FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y))
in (match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Lt
end
| uu____2422 -> begin
(match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
FStar_Order.Eq
end
| uu____2423 -> begin
FStar_Order.Gt
end)
end)))


let is_free : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun x t -> (FStar_Syntax_Util.is_free_in (FStar_Pervasives_Native.fst x) t))


let embed_norm_step : FStar_Reflection_Data.norm_step  ->  FStar_Syntax_Syntax.term = (fun n1 -> (match (n1) with
| FStar_Reflection_Data.Simpl -> begin
FStar_Reflection_Data.ref_Simpl
end
| FStar_Reflection_Data.WHNF -> begin
FStar_Reflection_Data.ref_WHNF
end
| FStar_Reflection_Data.Primops -> begin
FStar_Reflection_Data.ref_Primops
end
| FStar_Reflection_Data.Delta -> begin
FStar_Reflection_Data.ref_Delta
end
| FStar_Reflection_Data.UnfoldOnly (l) -> begin
(

let uu____2439 = (

let uu____2440 = (

let uu____2441 = (

let uu____2442 = (FStar_Syntax_Embeddings.embed_list embed_fvar FStar_Reflection_Data.fstar_refl_fvar l)
in (FStar_Syntax_Syntax.as_arg uu____2442))
in (uu____2441)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_UnfoldOnly uu____2440))
in (uu____2439 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_norm_step : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.norm_step = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2450 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2450) with
| (hd1, args) -> begin
(

let uu____2487 = (

let uu____2500 = (

let uu____2501 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2501.FStar_Syntax_Syntax.n)
in ((uu____2500), (args)))
in (match (uu____2487) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Simpl_lid) -> begin
FStar_Reflection_Data.Simpl
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_WHNF_lid) -> begin
FStar_Reflection_Data.WHNF
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Primops_lid) -> begin
FStar_Reflection_Data.Primops
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Delta_lid) -> begin
FStar_Reflection_Data.Delta
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____2574))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_UnfoldOnly_lid) -> begin
(

let uu____2599 = (FStar_Syntax_Embeddings.unembed_list unembed_fvar l)
in FStar_Reflection_Data.UnfoldOnly (uu____2599))
end
| uu____2602 -> begin
(failwith "not an embedded norm_step")
end))
end))))


let lookup_typ : FStar_TypeChecker_Env.env  ->  Prims.string Prims.list  ->  FStar_Reflection_Data.sigelt_view = (fun env ns -> (

let lid = (FStar_Parser_Const.p2l ns)
in (

let res = (FStar_TypeChecker_Env.lookup_qname env lid)
in (match (res) with
| FStar_Pervasives_Native.None -> begin
FStar_Reflection_Data.Unk
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____2667), rng) -> begin
FStar_Reflection_Data.Unk
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid1, us1, bs, t, uu____2768, dc_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid1)
in (

let ctor1 = (fun dc_lid -> (

let uu____2785 = (FStar_TypeChecker_Env.lookup_qname env dc_lid)
in (match (uu____2785) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se1, us2), rng1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid2, us3, t1, uu____2858, n1, uu____2860) -> begin
(

let uu____2865 = (

let uu____2870 = (FStar_Ident.path_of_lid lid2)
in ((uu____2870), (t1)))
in FStar_Reflection_Data.Ctor (uu____2865))
end
| uu____2875 -> begin
(failwith "wat 1")
end)
end
| uu____2876 -> begin
(failwith "wat 2")
end)))
in (

let ctors = (FStar_List.map ctor1 dc_lids)
in FStar_Reflection_Data.Sg_Inductive (((nm), (bs), (t), (ctors))))))
end
| uu____2904 -> begin
FStar_Reflection_Data.Unk
end)
end))))


let embed_ctor : FStar_Reflection_Data.ctor  ->  FStar_Syntax_Syntax.term = (fun c -> (match (c) with
| FStar_Reflection_Data.Ctor (nm, t) -> begin
(

let uu____2911 = (

let uu____2912 = (

let uu____2913 = (

let uu____2914 = (FStar_Syntax_Embeddings.embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____2914))
in (

let uu____2915 = (

let uu____2918 = (

let uu____2919 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____2919))
in (uu____2918)::[])
in (uu____2913)::uu____2915))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor uu____2912))
in (uu____2911 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_ctor : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.ctor = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2927 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2927) with
| (hd1, args) -> begin
(

let uu____2964 = (

let uu____2977 = (

let uu____2978 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2978.FStar_Syntax_Syntax.n)
in ((uu____2977), (args)))
in (match (uu____2964) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____2991))::((t2, uu____2993))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Ctor_lid) -> begin
(

let uu____3028 = (

let uu____3033 = (FStar_Syntax_Embeddings.unembed_string_list nm)
in (

let uu____3036 = (unembed_term t2)
in ((uu____3033), (uu____3036))))
in FStar_Reflection_Data.Ctor (uu____3028))
end
| uu____3039 -> begin
(failwith "not an embedded ctor")
end))
end))))


let embed_sigelt_view : FStar_Reflection_Data.sigelt_view  ->  FStar_Syntax_Syntax.term = (fun sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Inductive (nm, bs, t, dcs) -> begin
(

let uu____3068 = (

let uu____3069 = (

let uu____3070 = (

let uu____3071 = (FStar_Syntax_Embeddings.embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____3071))
in (

let uu____3072 = (

let uu____3075 = (

let uu____3076 = (embed_binders bs)
in (FStar_Syntax_Syntax.as_arg uu____3076))
in (

let uu____3077 = (

let uu____3080 = (

let uu____3081 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____3081))
in (

let uu____3082 = (

let uu____3085 = (

let uu____3086 = (FStar_Syntax_Embeddings.embed_list embed_ctor FStar_Reflection_Data.fstar_refl_ctor dcs)
in (FStar_Syntax_Syntax.as_arg uu____3086))
in (uu____3085)::[])
in (uu____3080)::uu____3082))
in (uu____3075)::uu____3077))
in (uu____3070)::uu____3072))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Inductive uu____3069))
in (uu____3068 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Unk -> begin
FStar_Reflection_Data.ref_Unk
end))


let unembed_sigelt_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.sigelt_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____3094 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____3094) with
| (hd1, args) -> begin
(

let uu____3131 = (

let uu____3144 = (

let uu____3145 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3145.FStar_Syntax_Syntax.n)
in ((uu____3144), (args)))
in (match (uu____3131) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____3158))::((bs, uu____3160))::((t2, uu____3162))::((dcs, uu____3164))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive_lid) -> begin
(

let uu____3219 = (

let uu____3232 = (FStar_Syntax_Embeddings.unembed_string_list nm)
in (

let uu____3235 = (unembed_binders bs)
in (

let uu____3238 = (unembed_term t2)
in (

let uu____3239 = (FStar_Syntax_Embeddings.unembed_list unembed_ctor dcs)
in ((uu____3232), (uu____3235), (uu____3238), (uu____3239))))))
in FStar_Reflection_Data.Sg_Inductive (uu____3219))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk_lid) -> begin
FStar_Reflection_Data.Unk
end
| uu____3263 -> begin
(failwith "not an embedded sigelt_view")
end))
end))))


let binders_of_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders = (fun e -> (FStar_TypeChecker_Env.all_binders e))


let type_of_binder : 'Auu____3284 . (FStar_Syntax_Syntax.bv * 'Auu____3284)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun b -> (match (b) with
| (b1, uu____3300) -> begin
b1.FStar_Syntax_Syntax.sort
end))


let term_eq : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = FStar_Syntax_Util.term_eq


let fresh_binder : 'Auu____3315 . FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.bv * 'Auu____3315 FStar_Pervasives_Native.option) = (fun t -> (

let uu____3326 = (FStar_Syntax_Syntax.gen_bv "__refl" FStar_Pervasives_Native.None t)
in ((uu____3326), (FStar_Pervasives_Native.None))))


let term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = FStar_Syntax_Print.term_to_string





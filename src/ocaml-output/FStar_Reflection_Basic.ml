
open Prims
open FStar_Pervasives

let lid_as_tm : FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun l -> (

let uu____5 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____5 FStar_Syntax_Syntax.fv_to_tm)))


let fstar_refl_embed : FStar_Syntax_Syntax.term = (lid_as_tm FStar_Parser_Const.fstar_refl_embed_lid)


let protect_embedded_term : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t x -> (

let uu____16 = (

let uu____17 = (

let uu____18 = (FStar_Syntax_Syntax.iarg t)
in (

let uu____19 = (

let uu____21 = (FStar_Syntax_Syntax.as_arg x)
in (uu____21)::[])
in (uu____18)::uu____19))
in (FStar_Syntax_Syntax.mk_Tm_app fstar_refl_embed uu____17))
in (uu____16 FStar_Pervasives_Native.None x.FStar_Syntax_Syntax.pos)))


let un_protect_embedded_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____30 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____30) with
| (head1, args) -> begin
(

let uu____56 = (

let uu____64 = (

let uu____65 = (FStar_Syntax_Util.un_uinst head1)
in uu____65.FStar_Syntax_Syntax.n)
in ((uu____64), (args)))
in (match (uu____56) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____74)::((x, uu____76))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fstar_refl_embed_lid) -> begin
x
end
| uu____102 -> begin
(

let uu____110 = (

let uu____111 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not a protected embedded term: %s" uu____111))
in (failwith uu____110))
end))
end)))


let embed_unit : Prims.unit  ->  FStar_Syntax_Syntax.term = (fun u -> FStar_Syntax_Util.exp_unit)


let unembed_unit : FStar_Syntax_Syntax.term  ->  Prims.unit = (fun uu____119 -> ())


let embed_bool : Prims.bool  ->  FStar_Syntax_Syntax.term = (fun b -> (match (b) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____124 -> begin
FStar_Syntax_Util.exp_false_bool
end))


let unembed_bool : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let uu____129 = (

let uu____130 = (FStar_Syntax_Subst.compress t)
in uu____130.FStar_Syntax_Syntax.n)
in (match (uu____129) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
b
end
| uu____134 -> begin
(failwith "Not an embedded bool")
end)))


let embed_int : Prims.int  ->  FStar_Syntax_Syntax.term = (fun i -> (

let uu____139 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Util.exp_int uu____139)))


let unembed_int : FStar_Syntax_Syntax.term  ->  Prims.int = (fun t -> (

let uu____144 = (

let uu____145 = (FStar_Syntax_Subst.compress t)
in uu____145.FStar_Syntax_Syntax.n)
in (match (uu____144) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____149)) -> begin
(FStar_Util.int_of_string s)
end
| uu____156 -> begin
(failwith "Not an embedded int")
end)))


let embed_string : Prims.string  ->  FStar_Syntax_Syntax.term = (fun s -> (

let bytes = (FStar_Util.unicode_of_string s)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((bytes), (FStar_Range.dummyRange))))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let unembed_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____174)) -> begin
(FStar_Util.string_of_unicode bytes)
end
| uu____177 -> begin
(

let uu____178 = (

let uu____179 = (

let uu____180 = (FStar_Syntax_Print.term_to_string t1)
in (Prims.strcat uu____180 ")"))
in (Prims.strcat "Not an embedded string (" uu____179))
in (failwith uu____178))
end)))


let lid_Mktuple2 : FStar_Ident.lident = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") FStar_Range.dummyRange)


let lid_tuple2 : FStar_Ident.lident = (FStar_Parser_Const.mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange)


let embed_binder : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.term = (fun b -> (FStar_Syntax_Util.mk_alien b "reflection.embed_binder" FStar_Pervasives_Native.None))


let unembed_binder : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder = (fun t -> (

let uu____189 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____189 FStar_Dyn.undyn)))


let rec embed_list = (fun embed_a typ l -> (match (l) with
| [] -> begin
(

let uu____218 = (

let uu____219 = (

let uu____220 = (FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____220 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____221 = (

let uu____222 = (FStar_Syntax_Syntax.iarg typ)
in (uu____222)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____219 uu____221)))
in (uu____218 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| (hd1)::tl1 -> begin
(

let uu____230 = (

let uu____231 = (

let uu____232 = (FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____232 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____233 = (

let uu____234 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____235 = (

let uu____237 = (

let uu____238 = (embed_a hd1)
in (FStar_Syntax_Syntax.as_arg uu____238))
in (

let uu____239 = (

let uu____241 = (

let uu____242 = (embed_list embed_a typ tl1)
in (FStar_Syntax_Syntax.as_arg uu____242))
in (uu____241)::[])
in (uu____237)::uu____239))
in (uu____234)::uu____235))
in (FStar_Syntax_Syntax.mk_Tm_app uu____231 uu____233)))
in (uu____230 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec unembed_list = (fun unembed_a l -> (

let l1 = (FStar_Syntax_Util.unascribe l)
in (

let uu____269 = (FStar_Syntax_Util.head_and_args l1)
in (match (uu____269) with
| (hd1, args) -> begin
(

let uu____296 = (

let uu____304 = (

let uu____305 = (FStar_Syntax_Util.un_uinst hd1)
in uu____305.FStar_Syntax_Syntax.n)
in ((uu____304), (args)))
in (match (uu____296) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____315) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_t)::((hd2, uu____329))::((tl1, uu____331))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____365 = (unembed_a hd2)
in (

let uu____366 = (unembed_list unembed_a tl1)
in (uu____365)::uu____366))
end
| uu____368 -> begin
(

let uu____376 = (

let uu____377 = (FStar_Syntax_Print.term_to_string l1)
in (FStar_Util.format1 "Not an embedded list: %s" uu____377))
in (failwith uu____376))
end))
end))))


let embed_binders : FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term = (fun l -> (embed_list embed_binder FStar_Reflection_Data.fstar_refl_binder l))


let unembed_binders : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.binder Prims.list = (fun t -> (unembed_list unembed_binder t))


let embed_string_list : Prims.string Prims.list  ->  FStar_Syntax_Syntax.term = (fun ss -> (embed_list embed_string FStar_TypeChecker_Common.t_string ss))


let unembed_string_list : FStar_Syntax_Syntax.term  ->  Prims.string Prims.list = (fun t -> (unembed_list unembed_string t))


let embed_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (protect_embedded_term FStar_Reflection_Data.fstar_refl_term t))


let unembed_term : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (un_protect_embedded_term t))


let embed_pair = (fun embed_a t_a embed_b t_b x -> (

let uu____459 = (

let uu____460 = (

let uu____461 = (FStar_Reflection_Data.lid_as_data_tm lid_Mktuple2)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____461 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____462 = (

let uu____463 = (FStar_Syntax_Syntax.iarg t_a)
in (

let uu____464 = (

let uu____466 = (FStar_Syntax_Syntax.iarg t_b)
in (

let uu____467 = (

let uu____469 = (

let uu____470 = (embed_a (FStar_Pervasives_Native.fst x))
in (FStar_Syntax_Syntax.as_arg uu____470))
in (

let uu____471 = (

let uu____473 = (

let uu____474 = (embed_b (FStar_Pervasives_Native.snd x))
in (FStar_Syntax_Syntax.as_arg uu____474))
in (uu____473)::[])
in (uu____469)::uu____471))
in (uu____466)::uu____467))
in (uu____463)::uu____464))
in (FStar_Syntax_Syntax.mk_Tm_app uu____460 uu____462)))
in (uu____459 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let unembed_pair = (fun unembed_a unembed_b pair -> (

let pairs = (FStar_Syntax_Util.unascribe pair)
in (

let uu____516 = (FStar_Syntax_Util.head_and_args pair)
in (match (uu____516) with
| (hd1, args) -> begin
(

let uu____544 = (

let uu____552 = (

let uu____553 = (FStar_Syntax_Util.un_uinst hd1)
in uu____553.FStar_Syntax_Syntax.n)
in ((uu____552), (args)))
in (match (uu____544) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____564)::(uu____565)::((a, uu____567))::((b, uu____569))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv lid_Mktuple2) -> begin
(

let uu____611 = (unembed_a a)
in (

let uu____612 = (unembed_b b)
in ((uu____611), (uu____612))))
end
| uu____613 -> begin
(failwith "Not an embedded pair")
end))
end))))


let embed_option = (fun embed_a typ o -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____651 = (

let uu____652 = (

let uu____653 = (FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.none_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____653 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____654 = (

let uu____655 = (FStar_Syntax_Syntax.iarg typ)
in (uu____655)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____652 uu____654)))
in (uu____651 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____661 = (

let uu____662 = (

let uu____663 = (FStar_Reflection_Data.lid_as_data_tm FStar_Parser_Const.some_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____663 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____664 = (

let uu____665 = (FStar_Syntax_Syntax.iarg typ)
in (

let uu____666 = (

let uu____668 = (

let uu____669 = (embed_a a)
in (FStar_Syntax_Syntax.as_arg uu____669))
in (uu____668)::[])
in (uu____665)::uu____666))
in (FStar_Syntax_Syntax.mk_Tm_app uu____662 uu____664)))
in (uu____661 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_option = (fun unembed_a o -> (

let uu____695 = (FStar_Syntax_Util.head_and_args o)
in (match (uu____695) with
| (hd1, args) -> begin
(

let uu____722 = (

let uu____730 = (

let uu____731 = (FStar_Syntax_Util.un_uinst hd1)
in uu____731.FStar_Syntax_Syntax.n)
in ((uu____730), (args)))
in (match (uu____722) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____741) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.None
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____753)::((a, uu____755))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid) -> begin
(

let uu____781 = (unembed_a a)
in FStar_Pervasives_Native.Some (uu____781))
end
| uu____782 -> begin
(failwith "Not an embedded option")
end))
end)))


let embed_fvar : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term = (fun fv -> (FStar_Syntax_Util.mk_alien fv "reflection.embed_fvar" FStar_Pervasives_Native.None))


let unembed_fvar : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv = (fun t -> (

let uu____799 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____799 FStar_Dyn.undyn)))


let embed_env : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term = (fun env -> (FStar_Syntax_Util.mk_alien env "tactics_embed_env" FStar_Pervasives_Native.None))


let unembed_env : FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.env = (fun t -> (

let uu____808 = (FStar_Syntax_Util.un_alien t)
in (FStar_All.pipe_right uu____808 FStar_Dyn.undyn)))


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

let uu____814 = (

let uu____815 = (

let uu____816 = (

let uu____817 = (

let uu____818 = (FStar_Util.string_of_int i)
in (FStar_Syntax_Util.exp_int uu____818))
in (FStar_Syntax_Syntax.as_arg uu____817))
in (uu____816)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_Int uu____815))
in (uu____814 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.C_String (s) -> begin
(

let uu____824 = (

let uu____825 = (

let uu____826 = (

let uu____827 = (embed_string s)
in (FStar_Syntax_Syntax.as_arg uu____827))
in (uu____826)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_C_String uu____825))
in (uu____824 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_const : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.vconst = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____837 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____837) with
| (hd1, args) -> begin
(

let uu____863 = (

let uu____871 = (

let uu____872 = (FStar_Syntax_Util.un_uinst hd1)
in uu____872.FStar_Syntax_Syntax.n)
in ((uu____871), (args)))
in (match (uu____863) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unit_lid) -> begin
FStar_Reflection_Data.C_Unit
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_True_lid) -> begin
FStar_Reflection_Data.C_True
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_False_lid) -> begin
FStar_Reflection_Data.C_False
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((i, uu____912))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int_lid) -> begin
(

let uu____930 = (unembed_int i)
in FStar_Reflection_Data.C_Int (uu____930))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((s, uu____933))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_String_lid) -> begin
(

let uu____951 = (unembed_string s)
in FStar_Reflection_Data.C_String (uu____951))
end
| uu____952 -> begin
(failwith "not an embedded vconst")
end))
end))))


let rec embed_pattern : FStar_Reflection_Data.pattern  ->  FStar_Syntax_Syntax.term = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____965 = (

let uu____966 = (

let uu____967 = (

let uu____968 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____968))
in (uu____967)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Constant uu____966))
in (uu____965 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____977 = (

let uu____978 = (

let uu____979 = (

let uu____980 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____980))
in (

let uu____981 = (

let uu____983 = (

let uu____984 = (embed_list embed_pattern FStar_Reflection_Data.fstar_refl_pattern ps)
in (FStar_Syntax_Syntax.as_arg uu____984))
in (uu____983)::[])
in (uu____979)::uu____981))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons uu____978))
in (uu____977 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____990 = (

let uu____991 = (

let uu____992 = (

let uu____993 = (

let uu____994 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____994))
in (FStar_Syntax_Syntax.as_arg uu____993))
in (uu____992)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var uu____991))
in (uu____990 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____1000 = (

let uu____1001 = (

let uu____1002 = (

let uu____1003 = (

let uu____1004 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____1004))
in (FStar_Syntax_Syntax.as_arg uu____1003))
in (uu____1002)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild uu____1001))
in (uu____1000 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec unembed_pattern : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.pattern = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____1014 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____1014) with
| (hd1, args) -> begin
(

let uu____1040 = (

let uu____1048 = (

let uu____1049 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1049.FStar_Syntax_Syntax.n)
in ((uu____1048), (args)))
in (match (uu____1040) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1059))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant_lid) -> begin
(

let uu____1077 = (unembed_const c)
in FStar_Reflection_Data.Pat_Constant (uu____1077))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((f, uu____1080))::((ps, uu____1082))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons_lid) -> begin
(

let uu____1108 = (

let uu____1112 = (unembed_fvar f)
in (

let uu____1113 = (unembed_list unembed_pattern ps)
in ((uu____1112), (uu____1113))))
in FStar_Reflection_Data.Pat_Cons (uu____1108))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1118))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var_lid) -> begin
(

let uu____1136 = (

let uu____1137 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____1137))
in FStar_Reflection_Data.Pat_Var (uu____1136))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1142))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild_lid) -> begin
(

let uu____1160 = (

let uu____1161 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____1161))
in FStar_Reflection_Data.Pat_Wild (uu____1160))
end
| uu____1164 -> begin
(failwith "not an embedded pattern")
end))
end))))


let embed_branch : (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term = (embed_pair embed_pattern FStar_Reflection_Data.fstar_refl_pattern embed_term FStar_Reflection_Data.fstar_refl_term)


let unembed_branch : FStar_Syntax_Syntax.term  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) = (unembed_pair unembed_pattern unembed_term)


let embed_term_view : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun t -> (match (t) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____1187 = (

let uu____1188 = (

let uu____1189 = (

let uu____1190 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____1190))
in (uu____1189)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar uu____1188))
in (uu____1187 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____1196 = (

let uu____1197 = (

let uu____1198 = (

let uu____1199 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____1199))
in (uu____1198)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var uu____1197))
in (uu____1196 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____1206 = (

let uu____1207 = (

let uu____1208 = (

let uu____1209 = (embed_term hd1)
in (FStar_Syntax_Syntax.as_arg uu____1209))
in (

let uu____1210 = (

let uu____1212 = (

let uu____1213 = (embed_term a)
in (FStar_Syntax_Syntax.as_arg uu____1213))
in (uu____1212)::[])
in (uu____1208)::uu____1210))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App uu____1207))
in (uu____1206 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Abs (b, t1) -> begin
(

let uu____1220 = (

let uu____1221 = (

let uu____1222 = (

let uu____1223 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____1223))
in (

let uu____1224 = (

let uu____1226 = (

let uu____1227 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1227))
in (uu____1226)::[])
in (uu____1222)::uu____1224))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs uu____1221))
in (uu____1220 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Arrow (b, t1) -> begin
(

let uu____1234 = (

let uu____1235 = (

let uu____1236 = (

let uu____1237 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____1237))
in (

let uu____1238 = (

let uu____1240 = (

let uu____1241 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1241))
in (uu____1240)::[])
in (uu____1236)::uu____1238))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow uu____1235))
in (uu____1234 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____1247 = (

let uu____1248 = (

let uu____1249 = (

let uu____1250 = (embed_unit ())
in (FStar_Syntax_Syntax.as_arg uu____1250))
in (uu____1249)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type uu____1248))
in (uu____1247 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Refine (bv, t1) -> begin
(

let uu____1257 = (

let uu____1258 = (

let uu____1259 = (

let uu____1260 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____1260))
in (

let uu____1261 = (

let uu____1263 = (

let uu____1264 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1264))
in (uu____1263)::[])
in (uu____1259)::uu____1261))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine uu____1258))
in (uu____1257 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1270 = (

let uu____1271 = (

let uu____1272 = (

let uu____1273 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____1273))
in (uu____1272)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const uu____1271))
in (uu____1270 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, t1) -> begin
(

let uu____1280 = (

let uu____1281 = (

let uu____1282 = (

let uu____1283 = (embed_int u)
in (FStar_Syntax_Syntax.as_arg uu____1283))
in (

let uu____1284 = (

let uu____1286 = (

let uu____1287 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1287))
in (uu____1286)::[])
in (uu____1282)::uu____1284))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar uu____1281))
in (uu____1280 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Match (t1, brs) -> begin
(

let uu____1296 = (

let uu____1297 = (

let uu____1298 = (

let uu____1299 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1299))
in (

let uu____1300 = (

let uu____1302 = (

let uu____1303 = (embed_list embed_branch FStar_Reflection_Data.fstar_refl_branch brs)
in (FStar_Syntax_Syntax.as_arg uu____1303))
in (uu____1302)::[])
in (uu____1298)::uu____1300))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match uu____1297))
in (uu____1296 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
FStar_Reflection_Data.ref_Tv_Unknown
end))


let unembed_term_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____1315 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____1315) with
| (hd1, args) -> begin
(

let uu____1341 = (

let uu____1349 = (

let uu____1350 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1350.FStar_Syntax_Syntax.n)
in ((uu____1349), (args)))
in (match (uu____1341) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var_lid) -> begin
(

let uu____1378 = (unembed_binder b)
in FStar_Reflection_Data.Tv_Var (uu____1378))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1381))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar_lid) -> begin
(

let uu____1399 = (unembed_fvar b)
in FStar_Reflection_Data.Tv_FVar (uu____1399))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____1402))::((r, uu____1404))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App_lid) -> begin
(

let uu____1430 = (

let uu____1433 = (unembed_term l)
in (

let uu____1434 = (unembed_term r)
in ((uu____1433), (uu____1434))))
in FStar_Reflection_Data.Tv_App (uu____1430))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1437))::((t2, uu____1439))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs_lid) -> begin
(

let uu____1465 = (

let uu____1468 = (unembed_binder b)
in (

let uu____1469 = (unembed_term t2)
in ((uu____1468), (uu____1469))))
in FStar_Reflection_Data.Tv_Abs (uu____1465))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1472))::((t2, uu____1474))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow_lid) -> begin
(

let uu____1500 = (

let uu____1503 = (unembed_binder b)
in (

let uu____1504 = (unembed_term t2)
in ((uu____1503), (uu____1504))))
in FStar_Reflection_Data.Tv_Arrow (uu____1500))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1507))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type_lid) -> begin
((unembed_unit u);
FStar_Reflection_Data.Tv_Type (());
)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1528))::((t2, uu____1530))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine_lid) -> begin
(

let uu____1556 = (

let uu____1559 = (unembed_binder b)
in (

let uu____1560 = (unembed_term t2)
in ((uu____1559), (uu____1560))))
in FStar_Reflection_Data.Tv_Refine (uu____1556))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1563))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const_lid) -> begin
(

let uu____1581 = (unembed_const c)
in FStar_Reflection_Data.Tv_Const (uu____1581))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1584))::((t2, uu____1586))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar_lid) -> begin
(

let uu____1612 = (

let uu____1615 = (unembed_int u)
in (

let uu____1616 = (unembed_term t2)
in ((uu____1615), (uu____1616))))
in FStar_Reflection_Data.Tv_Uvar (uu____1612))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t2, uu____1619))::((brs, uu____1621))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match_lid) -> begin
(

let uu____1647 = (

let uu____1651 = (unembed_term t2)
in (

let uu____1652 = (unembed_list unembed_branch brs)
in ((uu____1651), (uu____1652))))
in FStar_Reflection_Data.Tv_Match (uu____1647))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown_lid) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____1671 -> begin
(failwith "not an embedded term_view")
end))
end))))


let rec last = (fun l -> (match (l) with
| [] -> begin
(failwith "last: empty list")
end
| (x)::[] -> begin
x
end
| (uu____1691)::xs -> begin
(last xs)
end))


let rec init = (fun l -> (match (l) with
| [] -> begin
(failwith "init: empty list")
end
| (x)::[] -> begin
[]
end
| (x)::xs -> begin
(

let uu____1711 = (init xs)
in (x)::uu____1711)
end))


let inspect_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (

let uu____1719 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____1719)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let uu____1726 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____1726 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)))


let inspect_bv : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____1736) -> begin
(

let uu____1743 = (FStar_Util.int_of_string s)
in FStar_Reflection_Data.C_Int (uu____1743))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| FStar_Const.Const_string (bs, uu____1745) -> begin
FStar_Reflection_Data.C_String ((FStar_Util.string_of_bytes bs))
end
| uu____1748 -> begin
(

let uu____1749 = (

let uu____1750 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____1750))
in (failwith uu____1749))
end))


let inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.un_uinst t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1757 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Reflection_Data.Tv_Var (uu____1757))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Reflection_Data.Tv_FVar (fv)
end
| FStar_Syntax_Syntax.Tm_app (hd1, []) -> begin
(failwith "inspect: empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____1789 = (last args)
in (match (uu____1789) with
| (a, uu____1799) -> begin
(

let uu____1804 = (

let uu____1807 = (

let uu____1810 = (

let uu____1811 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1811))
in (uu____1810 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in ((uu____1807), (a)))
in FStar_Reflection_Data.Tv_App (uu____1804))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____1824, uu____1825) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____1852 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____1852) with
| (bs1, t3) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1868 = (

let uu____1871 = (FStar_Syntax_Util.abs bs2 t3 k)
in ((b), (uu____1871)))
in FStar_Reflection_Data.Tv_Abs (uu____1868))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____1874) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(

let uu____1897 = (FStar_Syntax_Subst.open_comp bs k)
in (match (uu____1897) with
| (bs1, k1) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1913 = (

let uu____1916 = (FStar_Syntax_Util.arrow bs2 k1)
in ((b), (uu____1916)))
in FStar_Reflection_Data.Tv_Arrow (uu____1913))
end)
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t2) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____1930 = (FStar_Syntax_Subst.open_term ((b)::[]) t2)
in (match (uu____1930) with
| (b', t3) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____1947 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.Tv_Refine (((b1), (t3))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1953 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____1953))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t2) -> begin
(

let uu____1972 = (

let uu____1975 = (FStar_Syntax_Unionfind.uvar_id u)
in ((uu____1975), (t2)))
in FStar_Reflection_Data.Tv_Uvar (uu____1972))
end
| FStar_Syntax_Syntax.Tm_match (t2, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____2011 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____2011))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____2022 = (

let uu____2026 = (FStar_List.map (fun uu____2034 -> (match (uu____2034) with
| (p1, uu____2039) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____2026)))
in FStar_Reflection_Data.Pat_Cons (uu____2022))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____2045) -> begin
(failwith "NYI: Pat_dot_term")
end))
in (

let brs1 = (FStar_List.map FStar_Syntax_Subst.open_branch brs)
in (

let brs2 = (FStar_List.map (fun uu___76_2076 -> (match (uu___76_2076) with
| (pat, uu____2091, t3) -> begin
(

let uu____2105 = (inspect_pat pat)
in ((uu____2105), (t3)))
end)) brs1)
in FStar_Reflection_Data.Tv_Match (((t2), (brs2))))))
end
| uu____2115 -> begin
((

let uu____2117 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____2118 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n" uu____2117 uu____2118)));
FStar_Reflection_Data.Tv_Unknown;
)
end)))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____2124 = (

let uu____2130 = (FStar_Util.string_of_int i)
in ((uu____2130), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____2124))
end
| FStar_Reflection_Data.C_True -> begin
FStar_Const.Const_bool (true)
end
| FStar_Reflection_Data.C_False -> begin
FStar_Const.Const_bool (false)
end
| FStar_Reflection_Data.C_String (s) -> begin
FStar_Const.Const_string ((((FStar_Util.bytes_of_string s)), (FStar_Range.dummyRange)))
end))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv, uu____2143) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(FStar_Syntax_Syntax.fv_to_tm fv)
end
| FStar_Reflection_Data.Tv_App (l, r) -> begin
(

let uu____2147 = (

let uu____2153 = (FStar_Syntax_Syntax.as_arg r)
in (uu____2153)::[])
in (FStar_Syntax_Util.mk_app l uu____2147))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
end
| FStar_Reflection_Data.Tv_Arrow (b, t) -> begin
(

let uu____2158 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow ((b)::[]) uu____2158))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
FStar_Syntax_Util.ktype
end
| FStar_Reflection_Data.Tv_Refine ((bv, uu____2162), t) -> begin
(FStar_Syntax_Util.refine bv t)
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____2167 = (

let uu____2170 = (

let uu____2171 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____2171))
in (FStar_Syntax_Syntax.mk uu____2170))
in (uu____2167 FStar_Pervasives_Native.None FStar_Range.dummyRange))
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

let uu____2196 = (

let uu____2197 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____2197))
in (FStar_All.pipe_left wrap uu____2196))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____2203 = (

let uu____2204 = (

let uu____2211 = (FStar_List.map (fun p1 -> (

let uu____2220 = (pack_pat p1)
in ((uu____2220), (false)))) ps)
in ((fv), (uu____2211)))
in FStar_Syntax_Syntax.Pat_cons (uu____2204))
in (FStar_All.pipe_left wrap uu____2203))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var (bv)))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild (bv)))
end))
in (

let brs1 = (FStar_List.map (fun uu___77_2249 -> (match (uu___77_2249) with
| (pat, t1) -> begin
(

let uu____2260 = (pack_pat pat)
in ((uu____2260), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (

let brs2 = (FStar_List.map FStar_Syntax_Subst.close_branch brs1)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs2)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))))
end
| uu____2273 -> begin
(failwith "pack: unexpected term view")
end))


let embed_order : FStar_Reflection_Data.order  ->  FStar_Syntax_Syntax.term = (fun o -> (match (o) with
| FStar_Reflection_Data.Lt -> begin
FStar_Reflection_Data.ord_Lt
end
| FStar_Reflection_Data.Eq -> begin
FStar_Reflection_Data.ord_Eq
end
| FStar_Reflection_Data.Gt -> begin
FStar_Reflection_Data.ord_Gt
end))


let unembed_order : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.order = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2283 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2283) with
| (hd1, args) -> begin
(

let uu____2309 = (

let uu____2317 = (

let uu____2318 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2318.FStar_Syntax_Syntax.n)
in ((uu____2317), (args)))
in (match (uu____2309) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Reflection_Data.Lt
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Reflection_Data.Eq
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Reflection_Data.Gt
end
| uu____2356 -> begin
(failwith "not an embedded order")
end))
end))))


let order_binder : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder  ->  FStar_Reflection_Data.order = (fun x y -> (

let n1 = (FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y))
in (match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
FStar_Reflection_Data.Lt
end
| uu____2373 -> begin
(match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
FStar_Reflection_Data.Eq
end
| uu____2374 -> begin
FStar_Reflection_Data.Gt
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
end))


let unembed_norm_step : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.norm_step = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2392 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2392) with
| (hd1, args) -> begin
(

let uu____2418 = (

let uu____2426 = (

let uu____2427 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2427.FStar_Syntax_Syntax.n)
in ((uu____2426), (args)))
in (match (uu____2418) with
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
| uu____2475 -> begin
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
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____2514), rng) -> begin
FStar_Reflection_Data.Unk
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid1, us1, bs, t, uu____2569, dc_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid1)
in (

let ctor1 = (fun dc_lid -> (

let uu____2581 = (FStar_TypeChecker_Env.lookup_qname env dc_lid)
in (match (uu____2581) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se1, us2), rng1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid2, us3, t1, uu____2621, n1, uu____2623) -> begin
(

let uu____2626 = (

let uu____2629 = (FStar_Ident.path_of_lid lid2)
in ((uu____2629), (t1)))
in FStar_Reflection_Data.Ctor (uu____2626))
end
| uu____2632 -> begin
(failwith "wat 1")
end)
end
| uu____2633 -> begin
(failwith "wat 2")
end)))
in (

let ctors = (FStar_List.map ctor1 dc_lids)
in FStar_Reflection_Data.Sg_Inductive (((nm), (bs), (t), (ctors))))))
end
| uu____2648 -> begin
FStar_Reflection_Data.Unk
end)
end))))


let embed_ctor : FStar_Reflection_Data.ctor  ->  FStar_Syntax_Syntax.term = (fun c -> (match (c) with
| FStar_Reflection_Data.Ctor (nm, t) -> begin
(

let uu____2655 = (

let uu____2656 = (

let uu____2657 = (

let uu____2658 = (embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____2658))
in (

let uu____2659 = (

let uu____2661 = (

let uu____2662 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____2662))
in (uu____2661)::[])
in (uu____2657)::uu____2659))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor uu____2656))
in (uu____2655 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_ctor : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.ctor = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2672 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2672) with
| (hd1, args) -> begin
(

let uu____2698 = (

let uu____2706 = (

let uu____2707 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2707.FStar_Syntax_Syntax.n)
in ((uu____2706), (args)))
in (match (uu____2698) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____2717))::((t2, uu____2719))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Ctor_lid) -> begin
(

let uu____2745 = (

let uu____2748 = (unembed_string_list nm)
in (

let uu____2750 = (unembed_term t2)
in ((uu____2748), (uu____2750))))
in FStar_Reflection_Data.Ctor (uu____2745))
end
| uu____2752 -> begin
(failwith "not an embedded ctor")
end))
end))))


let embed_sigelt_view : FStar_Reflection_Data.sigelt_view  ->  FStar_Syntax_Syntax.term = (fun sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Inductive (nm, bs, t, dcs) -> begin
(

let uu____2772 = (

let uu____2773 = (

let uu____2774 = (

let uu____2775 = (embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____2775))
in (

let uu____2776 = (

let uu____2778 = (

let uu____2779 = (embed_binders bs)
in (FStar_Syntax_Syntax.as_arg uu____2779))
in (

let uu____2780 = (

let uu____2782 = (

let uu____2783 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____2783))
in (

let uu____2784 = (

let uu____2786 = (

let uu____2787 = (embed_list embed_ctor FStar_Reflection_Data.fstar_refl_ctor dcs)
in (FStar_Syntax_Syntax.as_arg uu____2787))
in (uu____2786)::[])
in (uu____2782)::uu____2784))
in (uu____2778)::uu____2780))
in (uu____2774)::uu____2776))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Inductive uu____2773))
in (uu____2772 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Unk -> begin
FStar_Reflection_Data.ref_Unk
end))


let unembed_sigelt_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.sigelt_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2797 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2797) with
| (hd1, args) -> begin
(

let uu____2823 = (

let uu____2831 = (

let uu____2832 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2832.FStar_Syntax_Syntax.n)
in ((uu____2831), (args)))
in (match (uu____2823) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____2842))::((bs, uu____2844))::((t2, uu____2846))::((dcs, uu____2848))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive_lid) -> begin
(

let uu____2890 = (

let uu____2897 = (unembed_string_list nm)
in (

let uu____2899 = (unembed_binders bs)
in (

let uu____2901 = (unembed_term t2)
in (

let uu____2902 = (unembed_list unembed_ctor dcs)
in ((uu____2897), (uu____2899), (uu____2901), (uu____2902))))))
in FStar_Reflection_Data.Sg_Inductive (uu____2890))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk_lid) -> begin
FStar_Reflection_Data.Unk
end
| uu____2917 -> begin
(failwith "not an embedded sigelt_view")
end))
end))))





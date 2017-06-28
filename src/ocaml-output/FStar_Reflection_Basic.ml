
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
end))


let unembed_const : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.vconst = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____828 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____828) with
| (hd1, args) -> begin
(

let uu____854 = (

let uu____862 = (

let uu____863 = (FStar_Syntax_Util.un_uinst hd1)
in uu____863.FStar_Syntax_Syntax.n)
in ((uu____862), (args)))
in (match (uu____854) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Unit_lid) -> begin
FStar_Reflection_Data.C_Unit
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_True_lid) -> begin
FStar_Reflection_Data.C_True
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_False_lid) -> begin
FStar_Reflection_Data.C_False
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((i, uu____903))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_C_Int_lid) -> begin
(

let uu____921 = (

let uu____922 = (FStar_Syntax_Subst.compress i)
in uu____922.FStar_Syntax_Syntax.n)
in (match (uu____921) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____926)) -> begin
(

let uu____933 = (FStar_Util.int_of_string s)
in FStar_Reflection_Data.C_Int (uu____933))
end
| uu____934 -> begin
(failwith "unembed_const: unexpected arg for C_Int")
end))
end
| uu____935 -> begin
(failwith "not an embedded vconst")
end))
end))))


let rec embed_pattern : FStar_Reflection_Data.pattern  ->  FStar_Syntax_Syntax.term = (fun p -> (match (p) with
| FStar_Reflection_Data.Pat_Constant (c) -> begin
(

let uu____948 = (

let uu____949 = (

let uu____950 = (

let uu____951 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____951))
in (uu____950)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Constant uu____949))
in (uu____948 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____960 = (

let uu____961 = (

let uu____962 = (

let uu____963 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____963))
in (

let uu____964 = (

let uu____966 = (

let uu____967 = (embed_list embed_pattern FStar_Reflection_Data.fstar_refl_pattern ps)
in (FStar_Syntax_Syntax.as_arg uu____967))
in (uu____966)::[])
in (uu____962)::uu____964))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Cons uu____961))
in (uu____960 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(

let uu____973 = (

let uu____974 = (

let uu____975 = (

let uu____976 = (

let uu____977 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____977))
in (FStar_Syntax_Syntax.as_arg uu____976))
in (uu____975)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Var uu____974))
in (uu____973 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(

let uu____983 = (

let uu____984 = (

let uu____985 = (

let uu____986 = (

let uu____987 = (FStar_Syntax_Syntax.mk_binder bv)
in (embed_binder uu____987))
in (FStar_Syntax_Syntax.as_arg uu____986))
in (uu____985)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Pat_Wild uu____984))
in (uu____983 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let rec unembed_pattern : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.pattern = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____997 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____997) with
| (hd1, args) -> begin
(

let uu____1023 = (

let uu____1031 = (

let uu____1032 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1032.FStar_Syntax_Syntax.n)
in ((uu____1031), (args)))
in (match (uu____1023) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1042))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Constant_lid) -> begin
(

let uu____1060 = (unembed_const c)
in FStar_Reflection_Data.Pat_Constant (uu____1060))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((f, uu____1063))::((ps, uu____1065))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Cons_lid) -> begin
(

let uu____1091 = (

let uu____1095 = (unembed_fvar f)
in (

let uu____1096 = (unembed_list unembed_pattern ps)
in ((uu____1095), (uu____1096))))
in FStar_Reflection_Data.Pat_Cons (uu____1091))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1101))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Var_lid) -> begin
(

let uu____1119 = (

let uu____1120 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____1120))
in FStar_Reflection_Data.Pat_Var (uu____1119))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1125))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Pat_Wild_lid) -> begin
(

let uu____1143 = (

let uu____1144 = (unembed_binder b)
in (FStar_Pervasives_Native.fst uu____1144))
in FStar_Reflection_Data.Pat_Wild (uu____1143))
end
| uu____1147 -> begin
(failwith "not an embedded pattern")
end))
end))))


let embed_branch : (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term = (embed_pair embed_pattern FStar_Reflection_Data.fstar_refl_pattern embed_term FStar_Reflection_Data.fstar_refl_term)


let unembed_branch : FStar_Syntax_Syntax.term  ->  (FStar_Reflection_Data.pattern * FStar_Syntax_Syntax.term) = (unembed_pair unembed_pattern unembed_term)


let embed_term_view : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun t -> (match (t) with
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(

let uu____1170 = (

let uu____1171 = (

let uu____1172 = (

let uu____1173 = (embed_fvar fv)
in (FStar_Syntax_Syntax.as_arg uu____1173))
in (uu____1172)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_FVar uu____1171))
in (uu____1170 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Var (bv) -> begin
(

let uu____1179 = (

let uu____1180 = (

let uu____1181 = (

let uu____1182 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____1182))
in (uu____1181)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Var uu____1180))
in (uu____1179 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_App (hd1, a) -> begin
(

let uu____1189 = (

let uu____1190 = (

let uu____1191 = (

let uu____1192 = (embed_term hd1)
in (FStar_Syntax_Syntax.as_arg uu____1192))
in (

let uu____1193 = (

let uu____1195 = (

let uu____1196 = (embed_term a)
in (FStar_Syntax_Syntax.as_arg uu____1196))
in (uu____1195)::[])
in (uu____1191)::uu____1193))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_App uu____1190))
in (uu____1189 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Abs (b, t1) -> begin
(

let uu____1203 = (

let uu____1204 = (

let uu____1205 = (

let uu____1206 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____1206))
in (

let uu____1207 = (

let uu____1209 = (

let uu____1210 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1210))
in (uu____1209)::[])
in (uu____1205)::uu____1207))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Abs uu____1204))
in (uu____1203 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Arrow (b, t1) -> begin
(

let uu____1217 = (

let uu____1218 = (

let uu____1219 = (

let uu____1220 = (embed_binder b)
in (FStar_Syntax_Syntax.as_arg uu____1220))
in (

let uu____1221 = (

let uu____1223 = (

let uu____1224 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1224))
in (uu____1223)::[])
in (uu____1219)::uu____1221))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Arrow uu____1218))
in (uu____1217 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Type (u) -> begin
(

let uu____1230 = (

let uu____1231 = (

let uu____1232 = (

let uu____1233 = (embed_unit ())
in (FStar_Syntax_Syntax.as_arg uu____1233))
in (uu____1232)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Type uu____1231))
in (uu____1230 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Refine (bv, t1) -> begin
(

let uu____1240 = (

let uu____1241 = (

let uu____1242 = (

let uu____1243 = (embed_binder bv)
in (FStar_Syntax_Syntax.as_arg uu____1243))
in (

let uu____1244 = (

let uu____1246 = (

let uu____1247 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1247))
in (uu____1246)::[])
in (uu____1242)::uu____1244))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Refine uu____1241))
in (uu____1240 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____1253 = (

let uu____1254 = (

let uu____1255 = (

let uu____1256 = (embed_const c)
in (FStar_Syntax_Syntax.as_arg uu____1256))
in (uu____1255)::[])
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Const uu____1254))
in (uu____1253 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Uvar (u, t1) -> begin
(

let uu____1263 = (

let uu____1264 = (

let uu____1265 = (

let uu____1266 = (embed_int u)
in (FStar_Syntax_Syntax.as_arg uu____1266))
in (

let uu____1267 = (

let uu____1269 = (

let uu____1270 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1270))
in (uu____1269)::[])
in (uu____1265)::uu____1267))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Uvar uu____1264))
in (uu____1263 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Match (t1, brs) -> begin
(

let uu____1279 = (

let uu____1280 = (

let uu____1281 = (

let uu____1282 = (embed_term t1)
in (FStar_Syntax_Syntax.as_arg uu____1282))
in (

let uu____1283 = (

let uu____1285 = (

let uu____1286 = (embed_list embed_branch FStar_Reflection_Data.fstar_refl_branch brs)
in (FStar_Syntax_Syntax.as_arg uu____1286))
in (uu____1285)::[])
in (uu____1281)::uu____1283))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Tv_Match uu____1280))
in (uu____1279 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Tv_Unknown -> begin
FStar_Reflection_Data.ref_Tv_Unknown
end))


let unembed_term_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____1298 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____1298) with
| (hd1, args) -> begin
(

let uu____1324 = (

let uu____1332 = (

let uu____1333 = (FStar_Syntax_Util.un_uinst hd1)
in uu____1333.FStar_Syntax_Syntax.n)
in ((uu____1332), (args)))
in (match (uu____1324) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1343))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Var_lid) -> begin
(

let uu____1361 = (unembed_binder b)
in FStar_Reflection_Data.Tv_Var (uu____1361))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_FVar_lid) -> begin
(

let uu____1382 = (unembed_fvar b)
in FStar_Reflection_Data.Tv_FVar (uu____1382))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____1385))::((r, uu____1387))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_App_lid) -> begin
(

let uu____1413 = (

let uu____1416 = (unembed_term l)
in (

let uu____1417 = (unembed_term r)
in ((uu____1416), (uu____1417))))
in FStar_Reflection_Data.Tv_App (uu____1413))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1420))::((t2, uu____1422))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Abs_lid) -> begin
(

let uu____1448 = (

let uu____1451 = (unembed_binder b)
in (

let uu____1452 = (unembed_term t2)
in ((uu____1451), (uu____1452))))
in FStar_Reflection_Data.Tv_Abs (uu____1448))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1455))::((t2, uu____1457))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Arrow_lid) -> begin
(

let uu____1483 = (

let uu____1486 = (unembed_binder b)
in (

let uu____1487 = (unembed_term t2)
in ((uu____1486), (uu____1487))))
in FStar_Reflection_Data.Tv_Arrow (uu____1483))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1490))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Type_lid) -> begin
((unembed_unit u);
FStar_Reflection_Data.Tv_Type (());
)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((b, uu____1511))::((t2, uu____1513))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Refine_lid) -> begin
(

let uu____1539 = (

let uu____1542 = (unembed_binder b)
in (

let uu____1543 = (unembed_term t2)
in ((uu____1542), (uu____1543))))
in FStar_Reflection_Data.Tv_Refine (uu____1539))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((c, uu____1546))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Const_lid) -> begin
(

let uu____1564 = (unembed_const c)
in FStar_Reflection_Data.Tv_Const (uu____1564))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((u, uu____1567))::((t2, uu____1569))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Uvar_lid) -> begin
(

let uu____1595 = (

let uu____1598 = (unembed_int u)
in (

let uu____1599 = (unembed_term t2)
in ((uu____1598), (uu____1599))))
in FStar_Reflection_Data.Tv_Uvar (uu____1595))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t2, uu____1602))::((brs, uu____1604))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Match_lid) -> begin
(

let uu____1630 = (

let uu____1634 = (unembed_term t2)
in (

let uu____1635 = (unembed_list unembed_branch brs)
in ((uu____1634), (uu____1635))))
in FStar_Reflection_Data.Tv_Match (uu____1630))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Tv_Unknown_lid) -> begin
FStar_Reflection_Data.Tv_Unknown
end
| uu____1654 -> begin
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
| (uu____1674)::xs -> begin
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

let uu____1694 = (init xs)
in (x)::uu____1694)
end))


let inspect_fv : FStar_Syntax_Syntax.fv  ->  Prims.string Prims.list = (fun fv -> (

let uu____1702 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.path_of_lid uu____1702)))


let pack_fv : Prims.string Prims.list  ->  FStar_Syntax_Syntax.fv = (fun ns -> (

let uu____1709 = (FStar_Parser_Const.p2l ns)
in (FStar_Syntax_Syntax.lid_as_fv uu____1709 FStar_Syntax_Syntax.Delta_equational FStar_Pervasives_Native.None)))


let inspect_bv : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (FStar_Syntax_Print.bv_to_string (FStar_Pervasives_Native.fst b)))


let inspect_const : FStar_Syntax_Syntax.sconst  ->  FStar_Reflection_Data.vconst = (fun c -> (match (c) with
| FStar_Const.Const_unit -> begin
FStar_Reflection_Data.C_Unit
end
| FStar_Const.Const_int (s, uu____1719) -> begin
(

let uu____1726 = (FStar_Util.int_of_string s)
in FStar_Reflection_Data.C_Int (uu____1726))
end
| FStar_Const.Const_bool (true) -> begin
FStar_Reflection_Data.C_True
end
| FStar_Const.Const_bool (false) -> begin
FStar_Reflection_Data.C_False
end
| uu____1727 -> begin
(

let uu____1728 = (

let uu____1729 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "unknown constant: %s" uu____1729))
in (failwith uu____1728))
end))


let inspect : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.term_view = (fun t -> (

let t1 = (FStar_Syntax_Util.un_uinst t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (bv) -> begin
(

let uu____1736 = (FStar_Syntax_Syntax.mk_binder bv)
in FStar_Reflection_Data.Tv_Var (uu____1736))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
FStar_Reflection_Data.Tv_FVar (fv)
end
| FStar_Syntax_Syntax.Tm_app (hd1, []) -> begin
(failwith "inspect: empty arguments on Tm_app")
end
| FStar_Syntax_Syntax.Tm_app (hd1, args) -> begin
(

let uu____1768 = (last args)
in (match (uu____1768) with
| (a, uu____1778) -> begin
(

let uu____1783 = (

let uu____1786 = (

let uu____1789 = (

let uu____1790 = (init args)
in (FStar_Syntax_Syntax.mk_Tm_app hd1 uu____1790))
in (uu____1789 FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos))
in ((uu____1786), (a)))
in FStar_Reflection_Data.Tv_App (uu____1783))
end))
end
| FStar_Syntax_Syntax.Tm_abs ([], uu____1803, uu____1804) -> begin
(failwith "inspect: empty arguments on Tm_abs")
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, k) -> begin
(

let uu____1831 = (FStar_Syntax_Subst.open_term bs t2)
in (match (uu____1831) with
| (bs1, t3) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1847 = (

let uu____1850 = (FStar_Syntax_Util.abs bs2 t3 k)
in ((b), (uu____1850)))
in FStar_Reflection_Data.Tv_Abs (uu____1847))
end)
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____1853) -> begin
FStar_Reflection_Data.Tv_Type (())
end
| FStar_Syntax_Syntax.Tm_arrow ([], k) -> begin
(failwith "inspect: empty binders on arrow")
end
| FStar_Syntax_Syntax.Tm_arrow (bs, k) -> begin
(

let uu____1876 = (FStar_Syntax_Subst.open_comp bs k)
in (match (uu____1876) with
| (bs1, k1) -> begin
(match (bs1) with
| [] -> begin
(failwith "impossible")
end
| (b)::bs2 -> begin
(

let uu____1892 = (

let uu____1895 = (FStar_Syntax_Util.arrow bs2 k1)
in ((b), (uu____1895)))
in FStar_Reflection_Data.Tv_Arrow (uu____1892))
end)
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, t2) -> begin
(

let b = (FStar_Syntax_Syntax.mk_binder bv)
in (

let uu____1909 = (FStar_Syntax_Subst.open_term ((b)::[]) t2)
in (match (uu____1909) with
| (b', t3) -> begin
(

let b1 = (match (b') with
| (b'1)::[] -> begin
b'1
end
| uu____1926 -> begin
(failwith "impossible")
end)
in FStar_Reflection_Data.Tv_Refine (((b1), (t3))))
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1932 = (inspect_const c)
in FStar_Reflection_Data.Tv_Const (uu____1932))
end
| FStar_Syntax_Syntax.Tm_uvar (u, t2) -> begin
(

let uu____1951 = (

let uu____1954 = (FStar_Syntax_Unionfind.uvar_id u)
in ((uu____1954), (t2)))
in FStar_Reflection_Data.Tv_Uvar (uu____1951))
end
| FStar_Syntax_Syntax.Tm_match (t2, brs) -> begin
(

let rec inspect_pat = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____1990 = (inspect_const c)
in FStar_Reflection_Data.Pat_Constant (uu____1990))
end
| FStar_Syntax_Syntax.Pat_cons (fv, ps) -> begin
(

let uu____2001 = (

let uu____2005 = (FStar_List.map (fun uu____2013 -> (match (uu____2013) with
| (p1, uu____2018) -> begin
(inspect_pat p1)
end)) ps)
in ((fv), (uu____2005)))
in FStar_Reflection_Data.Pat_Cons (uu____2001))
end
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
FStar_Reflection_Data.Pat_Var (bv)
end
| FStar_Syntax_Syntax.Pat_wild (bv) -> begin
FStar_Reflection_Data.Pat_Wild (bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____2024) -> begin
(failwith "NYI: Pat_dot_term")
end))
in (

let brs1 = (FStar_List.map (fun uu___76_2053 -> (match (uu___76_2053) with
| (pat, uu____2068, t3) -> begin
(

let uu____2082 = (inspect_pat pat)
in ((uu____2082), (t3)))
end)) brs)
in FStar_Reflection_Data.Tv_Match (((t2), (brs1)))))
end
| uu____2092 -> begin
((

let uu____2094 = (FStar_Syntax_Print.tag_of_term t1)
in (

let uu____2095 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "inspect: outside of expected syntax (%s, %s)\n" uu____2094 uu____2095)));
FStar_Reflection_Data.Tv_Unknown;
)
end)))


let pack_const : FStar_Reflection_Data.vconst  ->  FStar_Syntax_Syntax.sconst = (fun c -> (match (c) with
| FStar_Reflection_Data.C_Unit -> begin
FStar_Const.Const_unit
end
| FStar_Reflection_Data.C_Int (i) -> begin
(

let uu____2101 = (

let uu____2107 = (FStar_Util.string_of_int i)
in ((uu____2107), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____2101))
end
| FStar_Reflection_Data.C_True -> begin
FStar_Const.Const_bool (true)
end
| FStar_Reflection_Data.C_False -> begin
FStar_Const.Const_bool (false)
end))


let pack : FStar_Reflection_Data.term_view  ->  FStar_Syntax_Syntax.term = (fun tv -> (match (tv) with
| FStar_Reflection_Data.Tv_Var (bv, uu____2118) -> begin
(FStar_Syntax_Syntax.bv_to_name bv)
end
| FStar_Reflection_Data.Tv_FVar (fv) -> begin
(FStar_Syntax_Syntax.fv_to_tm fv)
end
| FStar_Reflection_Data.Tv_App (l, r) -> begin
(

let uu____2122 = (

let uu____2128 = (FStar_Syntax_Syntax.as_arg r)
in (uu____2128)::[])
in (FStar_Syntax_Util.mk_app l uu____2122))
end
| FStar_Reflection_Data.Tv_Abs (b, t) -> begin
(FStar_Syntax_Util.abs ((b)::[]) t FStar_Pervasives_Native.None)
end
| FStar_Reflection_Data.Tv_Arrow (b, t) -> begin
(

let uu____2133 = (FStar_Syntax_Syntax.mk_Total t)
in (FStar_Syntax_Util.arrow ((b)::[]) uu____2133))
end
| FStar_Reflection_Data.Tv_Type (()) -> begin
FStar_Syntax_Util.ktype
end
| FStar_Reflection_Data.Tv_Refine ((bv, uu____2137), t) -> begin
(FStar_Syntax_Util.refine bv t)
end
| FStar_Reflection_Data.Tv_Const (c) -> begin
(

let uu____2142 = (

let uu____2145 = (

let uu____2146 = (pack_const c)
in FStar_Syntax_Syntax.Tm_constant (uu____2146))
in (FStar_Syntax_Syntax.mk uu____2145))
in (uu____2142 FStar_Pervasives_Native.None FStar_Range.dummyRange))
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

let uu____2171 = (

let uu____2172 = (pack_const c)
in FStar_Syntax_Syntax.Pat_constant (uu____2172))
in (FStar_All.pipe_left wrap uu____2171))
end
| FStar_Reflection_Data.Pat_Cons (fv, ps) -> begin
(

let uu____2178 = (

let uu____2179 = (

let uu____2186 = (FStar_List.map (fun p1 -> (

let uu____2195 = (pack_pat p1)
in ((uu____2195), (false)))) ps)
in ((fv), (uu____2186)))
in FStar_Syntax_Syntax.Pat_cons (uu____2179))
in (FStar_All.pipe_left wrap uu____2178))
end
| FStar_Reflection_Data.Pat_Var (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var (bv)))
end
| FStar_Reflection_Data.Pat_Wild (bv) -> begin
(FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild (bv)))
end))
in (

let brs1 = (FStar_List.map (fun uu___77_2224 -> (match (uu___77_2224) with
| (pat, t1) -> begin
(

let uu____2235 = (pack_pat pat)
in ((uu____2235), (FStar_Pervasives_Native.None), (t1)))
end)) brs)
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((t), (brs1)))) FStar_Pervasives_Native.None FStar_Range.dummyRange))))
end
| uu____2252 -> begin
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

let uu____2262 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2262) with
| (hd1, args) -> begin
(

let uu____2288 = (

let uu____2296 = (

let uu____2297 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2297.FStar_Syntax_Syntax.n)
in ((uu____2296), (args)))
in (match (uu____2288) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Lt_lid) -> begin
FStar_Reflection_Data.Lt
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Eq_lid) -> begin
FStar_Reflection_Data.Eq
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ord_Gt_lid) -> begin
FStar_Reflection_Data.Gt
end
| uu____2335 -> begin
(failwith "not an embedded order")
end))
end))))


let order_binder : FStar_Syntax_Syntax.binder  ->  FStar_Syntax_Syntax.binder  ->  FStar_Reflection_Data.order = (fun x y -> (

let n1 = (FStar_Syntax_Syntax.order_bv (FStar_Pervasives_Native.fst x) (FStar_Pervasives_Native.fst y))
in (match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
FStar_Reflection_Data.Lt
end
| uu____2352 -> begin
(match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
FStar_Reflection_Data.Eq
end
| uu____2353 -> begin
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

let uu____2371 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2371) with
| (hd1, args) -> begin
(

let uu____2397 = (

let uu____2405 = (

let uu____2406 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2406.FStar_Syntax_Syntax.n)
in ((uu____2405), (args)))
in (match (uu____2397) with
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
| uu____2454 -> begin
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
| FStar_Pervasives_Native.Some (FStar_Util.Inl (uu____2493), rng) -> begin
FStar_Reflection_Data.Unk
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, us), rng) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid1, us1, bs, t, uu____2548, dc_lids) -> begin
(

let nm = (FStar_Ident.path_of_lid lid1)
in (

let ctor1 = (fun dc_lid -> (

let uu____2560 = (FStar_TypeChecker_Env.lookup_qname env dc_lid)
in (match (uu____2560) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se1, us2), rng1) -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid2, us3, t1, uu____2600, n1, uu____2602) -> begin
(

let uu____2605 = (

let uu____2608 = (FStar_Ident.path_of_lid lid2)
in ((uu____2608), (t1)))
in FStar_Reflection_Data.Ctor (uu____2605))
end
| uu____2611 -> begin
(failwith "wat 1")
end)
end
| uu____2612 -> begin
(failwith "wat 2")
end)))
in (

let ctors = (FStar_List.map ctor1 dc_lids)
in FStar_Reflection_Data.Sg_Inductive (((nm), (bs), (t), (ctors))))))
end
| uu____2627 -> begin
FStar_Reflection_Data.Unk
end)
end))))


let embed_ctor : FStar_Reflection_Data.ctor  ->  FStar_Syntax_Syntax.term = (fun c -> (match (c) with
| FStar_Reflection_Data.Ctor (nm, t) -> begin
(

let uu____2634 = (

let uu____2635 = (

let uu____2636 = (

let uu____2637 = (embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____2637))
in (

let uu____2638 = (

let uu____2640 = (

let uu____2641 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____2641))
in (uu____2640)::[])
in (uu____2636)::uu____2638))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Ctor uu____2635))
in (uu____2634 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end))


let unembed_ctor : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.ctor = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2651 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2651) with
| (hd1, args) -> begin
(

let uu____2677 = (

let uu____2685 = (

let uu____2686 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2686.FStar_Syntax_Syntax.n)
in ((uu____2685), (args)))
in (match (uu____2677) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____2696))::((t2, uu____2698))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Ctor_lid) -> begin
(

let uu____2724 = (

let uu____2727 = (unembed_string_list nm)
in (

let uu____2729 = (unembed_term t2)
in ((uu____2727), (uu____2729))))
in FStar_Reflection_Data.Ctor (uu____2724))
end
| uu____2731 -> begin
(failwith "not an embedded ctor")
end))
end))))


let embed_sigelt_view : FStar_Reflection_Data.sigelt_view  ->  FStar_Syntax_Syntax.term = (fun sev -> (match (sev) with
| FStar_Reflection_Data.Sg_Inductive (nm, bs, t, dcs) -> begin
(

let uu____2751 = (

let uu____2752 = (

let uu____2753 = (

let uu____2754 = (embed_string_list nm)
in (FStar_Syntax_Syntax.as_arg uu____2754))
in (

let uu____2755 = (

let uu____2757 = (

let uu____2758 = (embed_binders bs)
in (FStar_Syntax_Syntax.as_arg uu____2758))
in (

let uu____2759 = (

let uu____2761 = (

let uu____2762 = (embed_term t)
in (FStar_Syntax_Syntax.as_arg uu____2762))
in (

let uu____2763 = (

let uu____2765 = (

let uu____2766 = (embed_list embed_ctor FStar_Reflection_Data.fstar_refl_ctor dcs)
in (FStar_Syntax_Syntax.as_arg uu____2766))
in (uu____2765)::[])
in (uu____2761)::uu____2763))
in (uu____2757)::uu____2759))
in (uu____2753)::uu____2755))
in (FStar_Syntax_Syntax.mk_Tm_app FStar_Reflection_Data.ref_Sg_Inductive uu____2752))
in (uu____2751 FStar_Pervasives_Native.None FStar_Range.dummyRange))
end
| FStar_Reflection_Data.Unk -> begin
FStar_Reflection_Data.ref_Unk
end))


let unembed_sigelt_view : FStar_Syntax_Syntax.term  ->  FStar_Reflection_Data.sigelt_view = (fun t -> (

let t1 = (FStar_Syntax_Util.unascribe t)
in (

let uu____2776 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____2776) with
| (hd1, args) -> begin
(

let uu____2802 = (

let uu____2810 = (

let uu____2811 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2811.FStar_Syntax_Syntax.n)
in ((uu____2810), (args)))
in (match (uu____2802) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((nm, uu____2821))::((bs, uu____2823))::((t2, uu____2825))::((dcs, uu____2827))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Sg_Inductive_lid) -> begin
(

let uu____2869 = (

let uu____2876 = (unembed_string_list nm)
in (

let uu____2878 = (unembed_binders bs)
in (

let uu____2880 = (unembed_term t2)
in (

let uu____2881 = (unembed_list unembed_ctor dcs)
in ((uu____2876), (uu____2878), (uu____2880), (uu____2881))))))
in FStar_Reflection_Data.Sg_Inductive (uu____2869))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Reflection_Data.ref_Unk_lid) -> begin
FStar_Reflection_Data.Unk
end
| uu____2896 -> begin
(failwith "not an embedded sigelt_view")
end))
end))))





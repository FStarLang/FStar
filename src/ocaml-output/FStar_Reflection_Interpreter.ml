
open Prims
open FStar_Pervasives

let unembed : 'Auu____9 . 'Auu____9 FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Embeddings.norm_cb  ->  'Auu____9 FStar_Pervasives_Native.option = (fun ea a norm_cb -> (

let uu____35 = (FStar_Syntax_Embeddings.unembed ea a)
in (uu____35 true norm_cb)))


let try_unembed : 'Auu____56 . 'Auu____56 FStar_Syntax_Embeddings.embedding  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Embeddings.norm_cb  ->  'Auu____56 FStar_Pervasives_Native.option = (fun ea a norm_cb -> (

let uu____82 = (FStar_Syntax_Embeddings.unembed ea a)
in (uu____82 false norm_cb)))


let embed : 'Auu____105 . 'Auu____105 FStar_Syntax_Embeddings.embedding  ->  FStar_Range.range  ->  'Auu____105  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.term = (fun ea r x norm_cb -> (

let uu____134 = (FStar_Syntax_Embeddings.embed ea x)
in (uu____134 r FStar_Pervasives_Native.None norm_cb)))


let int1 : 'a 'r . FStar_Ident.lid  ->  ('a  ->  'r)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_TypeChecker_Cfg.psc  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun m f ea er psc n1 args -> (match (args) with
| ((a, uu____243))::[] -> begin
(

let uu____268 = (try_unembed ea a n1)
in (FStar_Util.bind_opt uu____268 (fun a1 -> (

let uu____276 = (

let uu____277 = (FStar_TypeChecker_Cfg.psc_range psc)
in (

let uu____278 = (f a1)
in (embed er uu____277 uu____278 n1)))
in FStar_Pervasives_Native.Some (uu____276)))))
end
| uu____281 -> begin
FStar_Pervasives_Native.None
end))


let int2 : 'a 'b 'r . FStar_Ident.lid  ->  ('a  ->  'b  ->  'r)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  FStar_TypeChecker_Cfg.psc  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun m f ea eb er psc n1 args -> (match (args) with
| ((a, uu____376))::((b, uu____378))::[] -> begin
(

let uu____419 = (try_unembed ea a n1)
in (FStar_Util.bind_opt uu____419 (fun a1 -> (

let uu____427 = (try_unembed eb b n1)
in (FStar_Util.bind_opt uu____427 (fun b1 -> (

let uu____435 = (

let uu____436 = (FStar_TypeChecker_Cfg.psc_range psc)
in (

let uu____437 = (f a1 b1)
in (embed er uu____436 uu____437 n1)))
in FStar_Pervasives_Native.Some (uu____435))))))))
end
| uu____440 -> begin
FStar_Pervasives_Native.None
end))


let nbe_int1 : 'a 'r . FStar_Ident.lid  ->  ('a  ->  'r)  ->  'a FStar_TypeChecker_NBETerm.embedding  ->  'r FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option = (fun m f ea er cb args -> (match (args) with
| ((a, uu____505))::[] -> begin
(

let uu____514 = (FStar_TypeChecker_NBETerm.unembed ea cb a)
in (FStar_Util.bind_opt uu____514 (fun a1 -> (

let uu____520 = (

let uu____521 = (f a1)
in (FStar_TypeChecker_NBETerm.embed er cb uu____521))
in FStar_Pervasives_Native.Some (uu____520)))))
end
| uu____522 -> begin
FStar_Pervasives_Native.None
end))


let nbe_int2 : 'a 'b 'r . FStar_Ident.lid  ->  ('a  ->  'b  ->  'r)  ->  'a FStar_TypeChecker_NBETerm.embedding  ->  'b FStar_TypeChecker_NBETerm.embedding  ->  'r FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option = (fun m f ea eb er cb args -> (match (args) with
| ((a, uu____606))::((b, uu____608))::[] -> begin
(

let uu____621 = (FStar_TypeChecker_NBETerm.unembed ea cb a)
in (FStar_Util.bind_opt uu____621 (fun a1 -> (

let uu____627 = (FStar_TypeChecker_NBETerm.unembed eb cb b)
in (FStar_Util.bind_opt uu____627 (fun b1 -> (

let uu____633 = (

let uu____634 = (f a1 b1)
in (FStar_TypeChecker_NBETerm.embed er cb uu____634))
in FStar_Pervasives_Native.Some (uu____633))))))))
end
| uu____635 -> begin
FStar_Pervasives_Native.None
end))


let mklid : Prims.string  ->  FStar_Ident.lid = (fun nm -> (FStar_Reflection_Data.fstar_refl_basic_lid nm))


let mk : FStar_Ident.lid  ->  Prims.int  ->  (FStar_TypeChecker_Cfg.psc  ->  FStar_Syntax_Embeddings.norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)  ->  (FStar_TypeChecker_NBETerm.nbe_cbs  ->  FStar_TypeChecker_NBETerm.args  ->  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)  ->  FStar_TypeChecker_Cfg.primitive_step = (fun l arity fn nbe_fn -> {FStar_TypeChecker_Cfg.name = l; FStar_TypeChecker_Cfg.arity = arity; FStar_TypeChecker_Cfg.univ_arity = (Prims.parse_int "0"); FStar_TypeChecker_Cfg.auto_reflect = FStar_Pervasives_Native.None; FStar_TypeChecker_Cfg.strong_reduction_ok = true; FStar_TypeChecker_Cfg.requires_binder_substitution = false; FStar_TypeChecker_Cfg.interpretation = fn; FStar_TypeChecker_Cfg.interpretation_nbe = nbe_fn})


let mk1 : 'a 'na 'nr 'r . Prims.string  ->  ('a  ->  'r)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  ('na  ->  'nr)  ->  'na FStar_TypeChecker_NBETerm.embedding  ->  'nr FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_Cfg.primitive_step = (fun nm f ea er nf ena enr -> (

let l = (mklid nm)
in (mk l (Prims.parse_int "1") (int1 l f ea er) (nbe_int1 l nf ena enr))))


let mk2 : 'a 'b 'na 'nb 'nr 'r . Prims.string  ->  ('a  ->  'b  ->  'r)  ->  'a FStar_Syntax_Embeddings.embedding  ->  'b FStar_Syntax_Embeddings.embedding  ->  'r FStar_Syntax_Embeddings.embedding  ->  ('na  ->  'nb  ->  'nr)  ->  'na FStar_TypeChecker_NBETerm.embedding  ->  'nb FStar_TypeChecker_NBETerm.embedding  ->  'nr FStar_TypeChecker_NBETerm.embedding  ->  FStar_TypeChecker_Cfg.primitive_step = (fun nm f ea eb er nf ena enb enr -> (

let l = (mklid nm)
in (mk l (Prims.parse_int "2") (int2 l f ea eb er) (nbe_int2 l nf ena enb enr))))


let reflection_primops : FStar_TypeChecker_Cfg.primitive_step Prims.list = (

let uu____914 = (mk1 "inspect_ln" FStar_Reflection_Basic.inspect_ln FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term_view FStar_Reflection_Basic.inspect_ln FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term_view)
in (

let uu____915 = (

let uu____918 = (mk1 "pack_ln" FStar_Reflection_Basic.pack_ln FStar_Reflection_Embeddings.e_term_view FStar_Reflection_Embeddings.e_term FStar_Reflection_Basic.pack_ln FStar_Reflection_NBEEmbeddings.e_term_view FStar_Reflection_NBEEmbeddings.e_term)
in (

let uu____919 = (

let uu____922 = (mk1 "inspect_fv" FStar_Reflection_Basic.inspect_fv FStar_Reflection_Embeddings.e_fv FStar_Syntax_Embeddings.e_string_list FStar_Reflection_Basic.inspect_fv FStar_Reflection_NBEEmbeddings.e_fv FStar_TypeChecker_NBETerm.e_string_list)
in (

let uu____927 = (

let uu____930 = (mk1 "pack_fv" FStar_Reflection_Basic.pack_fv FStar_Syntax_Embeddings.e_string_list FStar_Reflection_Embeddings.e_fv FStar_Reflection_Basic.pack_fv FStar_TypeChecker_NBETerm.e_string_list FStar_Reflection_NBEEmbeddings.e_fv)
in (

let uu____935 = (

let uu____938 = (mk1 "inspect_comp" FStar_Reflection_Basic.inspect_comp FStar_Reflection_Embeddings.e_comp FStar_Reflection_Embeddings.e_comp_view FStar_Reflection_Basic.inspect_comp FStar_Reflection_NBEEmbeddings.e_comp FStar_Reflection_NBEEmbeddings.e_comp_view)
in (

let uu____939 = (

let uu____942 = (mk1 "pack_comp" FStar_Reflection_Basic.pack_comp FStar_Reflection_Embeddings.e_comp_view FStar_Reflection_Embeddings.e_comp FStar_Reflection_Basic.pack_comp FStar_Reflection_NBEEmbeddings.e_comp_view FStar_Reflection_NBEEmbeddings.e_comp)
in (

let uu____943 = (

let uu____946 = (mk1 "inspect_sigelt" FStar_Reflection_Basic.inspect_sigelt FStar_Reflection_Embeddings.e_sigelt FStar_Reflection_Embeddings.e_sigelt_view FStar_Reflection_Basic.inspect_sigelt FStar_Reflection_NBEEmbeddings.e_sigelt FStar_Reflection_NBEEmbeddings.e_sigelt_view)
in (

let uu____947 = (

let uu____950 = (mk1 "pack_sigelt" FStar_Reflection_Basic.pack_sigelt FStar_Reflection_Embeddings.e_sigelt_view FStar_Reflection_Embeddings.e_sigelt FStar_Reflection_Basic.pack_sigelt FStar_Reflection_NBEEmbeddings.e_sigelt_view FStar_Reflection_NBEEmbeddings.e_sigelt)
in (

let uu____951 = (

let uu____954 = (mk1 "inspect_bv" FStar_Reflection_Basic.inspect_bv FStar_Reflection_Embeddings.e_bv FStar_Reflection_Embeddings.e_bv_view FStar_Reflection_Basic.inspect_bv FStar_Reflection_NBEEmbeddings.e_bv FStar_Reflection_NBEEmbeddings.e_bv_view)
in (

let uu____955 = (

let uu____958 = (mk1 "pack_bv" FStar_Reflection_Basic.pack_bv FStar_Reflection_Embeddings.e_bv_view FStar_Reflection_Embeddings.e_bv FStar_Reflection_Basic.pack_bv FStar_Reflection_NBEEmbeddings.e_bv_view FStar_Reflection_NBEEmbeddings.e_bv)
in (

let uu____959 = (

let uu____962 = (mk1 "sigelt_attrs" FStar_Reflection_Basic.sigelt_attrs FStar_Reflection_Embeddings.e_sigelt FStar_Reflection_Embeddings.e_attributes FStar_Reflection_Basic.sigelt_attrs FStar_Reflection_NBEEmbeddings.e_sigelt FStar_Reflection_NBEEmbeddings.e_attributes)
in (

let uu____967 = (

let uu____970 = (mk2 "set_sigelt_attrs" FStar_Reflection_Basic.set_sigelt_attrs FStar_Reflection_Embeddings.e_attributes FStar_Reflection_Embeddings.e_sigelt FStar_Reflection_Embeddings.e_sigelt FStar_Reflection_Basic.set_sigelt_attrs FStar_Reflection_NBEEmbeddings.e_attributes FStar_Reflection_NBEEmbeddings.e_sigelt FStar_Reflection_NBEEmbeddings.e_sigelt)
in (

let uu____975 = (

let uu____978 = (mk1 "inspect_binder" FStar_Reflection_Basic.inspect_binder FStar_Reflection_Embeddings.e_binder FStar_Reflection_Embeddings.e_binder_view FStar_Reflection_Basic.inspect_binder FStar_Reflection_NBEEmbeddings.e_binder FStar_Reflection_NBEEmbeddings.e_binder_view)
in (

let uu____979 = (

let uu____982 = (mk2 "pack_binder" FStar_Reflection_Basic.pack_binder FStar_Reflection_Embeddings.e_bv FStar_Reflection_Embeddings.e_aqualv FStar_Reflection_Embeddings.e_binder FStar_Reflection_Basic.pack_binder FStar_Reflection_NBEEmbeddings.e_bv FStar_Reflection_NBEEmbeddings.e_aqualv FStar_Reflection_NBEEmbeddings.e_binder)
in (

let uu____983 = (

let uu____986 = (mk2 "compare_bv" FStar_Reflection_Basic.compare_bv FStar_Reflection_Embeddings.e_bv FStar_Reflection_Embeddings.e_bv FStar_Reflection_Embeddings.e_order FStar_Reflection_Basic.compare_bv FStar_Reflection_NBEEmbeddings.e_bv FStar_Reflection_NBEEmbeddings.e_bv FStar_Reflection_NBEEmbeddings.e_order)
in (

let uu____987 = (

let uu____990 = (mk2 "is_free" FStar_Reflection_Basic.is_free FStar_Reflection_Embeddings.e_bv FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_bool FStar_Reflection_Basic.is_free FStar_Reflection_NBEEmbeddings.e_bv FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____991 = (

let uu____994 = (

let uu____995 = (FStar_Syntax_Embeddings.e_list FStar_Reflection_Embeddings.e_fv)
in (

let uu____1000 = (FStar_TypeChecker_NBETerm.e_list FStar_Reflection_NBEEmbeddings.e_fv)
in (mk2 "lookup_attr" FStar_Reflection_Basic.lookup_attr FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_env uu____995 FStar_Reflection_Basic.lookup_attr FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_env uu____1000)))
in (

let uu____1009 = (

let uu____1012 = (mk2 "term_eq" FStar_Reflection_Basic.term_eq FStar_Reflection_Embeddings.e_term FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_bool FStar_Reflection_Basic.term_eq FStar_Reflection_NBEEmbeddings.e_term FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_bool)
in (

let uu____1013 = (

let uu____1016 = (mk1 "moduleof" FStar_Reflection_Basic.moduleof FStar_Reflection_Embeddings.e_env FStar_Syntax_Embeddings.e_string_list FStar_Reflection_Basic.moduleof FStar_Reflection_NBEEmbeddings.e_env FStar_TypeChecker_NBETerm.e_string_list)
in (

let uu____1021 = (

let uu____1024 = (mk1 "term_to_string" FStar_Reflection_Basic.term_to_string FStar_Reflection_Embeddings.e_term FStar_Syntax_Embeddings.e_string FStar_Reflection_Basic.term_to_string FStar_Reflection_NBEEmbeddings.e_term FStar_TypeChecker_NBETerm.e_string)
in (

let uu____1025 = (

let uu____1028 = (mk1 "binders_of_env" FStar_Reflection_Basic.binders_of_env FStar_Reflection_Embeddings.e_env FStar_Reflection_Embeddings.e_binders FStar_Reflection_Basic.binders_of_env FStar_Reflection_NBEEmbeddings.e_env FStar_Reflection_NBEEmbeddings.e_binders)
in (

let uu____1029 = (

let uu____1032 = (

let uu____1033 = (FStar_Syntax_Embeddings.e_option FStar_Reflection_Embeddings.e_sigelt)
in (

let uu____1038 = (FStar_TypeChecker_NBETerm.e_option FStar_Reflection_NBEEmbeddings.e_sigelt)
in (mk2 "lookup_typ" FStar_Reflection_Basic.lookup_typ FStar_Reflection_Embeddings.e_env FStar_Syntax_Embeddings.e_string_list uu____1033 FStar_Reflection_Basic.lookup_typ FStar_Reflection_NBEEmbeddings.e_env FStar_TypeChecker_NBETerm.e_string_list uu____1038)))
in (uu____1032)::[])
in (uu____1028)::uu____1029))
in (uu____1024)::uu____1025))
in (uu____1016)::uu____1021))
in (uu____1012)::uu____1013))
in (uu____994)::uu____1009))
in (uu____990)::uu____991))
in (uu____986)::uu____987))
in (uu____982)::uu____983))
in (uu____978)::uu____979))
in (uu____970)::uu____975))
in (uu____962)::uu____967))
in (uu____958)::uu____959))
in (uu____954)::uu____955))
in (uu____950)::uu____951))
in (uu____946)::uu____947))
in (uu____942)::uu____943))
in (uu____938)::uu____939))
in (uu____930)::uu____935))
in (uu____922)::uu____927))
in (uu____918)::uu____919))
in (uu____914)::uu____915))





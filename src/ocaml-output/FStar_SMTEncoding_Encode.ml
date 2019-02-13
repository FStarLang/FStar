
open Prims
open FStar_Pervasives
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = mk1; is = is} -> begin
mk1
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = mk1; is = is} -> begin
is
end))


let prims : prims_t = (

let uu____136 = (FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____136) with
| (asym, a) -> begin
(

let uu____147 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____147) with
| (xsym, x) -> begin
(

let uu____158 = (FStar_SMTEncoding_Env.fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____158) with
| (ysym, y) -> begin
(

let quant = (fun vars body rng x1 -> (

let xname_decl = (

let uu____236 = (

let uu____248 = (FStar_All.pipe_right vars (FStar_List.map FStar_SMTEncoding_Term.fv_sort))
in ((x1), (uu____248), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____236))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____268 = (

let uu____276 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____276)))
in (FStar_SMTEncoding_Util.mkApp uu____268))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars)
in (

let uu____295 = (

let uu____298 = (

let uu____301 = (

let uu____304 = (

let uu____305 = (

let uu____313 = (

let uu____314 = (

let uu____325 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____325)))
in (FStar_SMTEncoding_Term.mkForall rng uu____314))
in ((uu____313), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____305))
in (

let uu____337 = (

let uu____340 = (

let uu____341 = (

let uu____349 = (

let uu____350 = (

let uu____361 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____361)))
in (FStar_SMTEncoding_Term.mkForall rng uu____350))
in ((uu____349), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____341))
in (uu____340)::[])
in (uu____304)::uu____337))
in (xtok_decl)::uu____301)
in (xname_decl)::uu____298)
in ((xtok1), ((FStar_List.length vars)), (uu____295))))))))))
in (

let axy = (FStar_List.map FStar_SMTEncoding_Term.mk_fv ((((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let xy = (FStar_List.map FStar_SMTEncoding_Term.mk_fv ((((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let qx = (FStar_List.map FStar_SMTEncoding_Term.mk_fv ((((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let prims1 = (

let uu____531 = (

let uu____552 = (

let uu____571 = (

let uu____572 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____572))
in (quant axy uu____571))
in ((FStar_Parser_Const.op_Eq), (uu____552)))
in (

let uu____589 = (

let uu____612 = (

let uu____633 = (

let uu____652 = (

let uu____653 = (

let uu____654 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____654))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____653))
in (quant axy uu____652))
in ((FStar_Parser_Const.op_notEq), (uu____633)))
in (

let uu____671 = (

let uu____694 = (

let uu____715 = (

let uu____734 = (

let uu____735 = (

let uu____736 = (

let uu____741 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____742 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____741), (uu____742))))
in (FStar_SMTEncoding_Util.mkLT uu____736))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____735))
in (quant xy uu____734))
in ((FStar_Parser_Const.op_LT), (uu____715)))
in (

let uu____759 = (

let uu____782 = (

let uu____803 = (

let uu____822 = (

let uu____823 = (

let uu____824 = (

let uu____829 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____830 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____829), (uu____830))))
in (FStar_SMTEncoding_Util.mkLTE uu____824))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____823))
in (quant xy uu____822))
in ((FStar_Parser_Const.op_LTE), (uu____803)))
in (

let uu____847 = (

let uu____870 = (

let uu____891 = (

let uu____910 = (

let uu____911 = (

let uu____912 = (

let uu____917 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____918 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____917), (uu____918))))
in (FStar_SMTEncoding_Util.mkGT uu____912))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____911))
in (quant xy uu____910))
in ((FStar_Parser_Const.op_GT), (uu____891)))
in (

let uu____935 = (

let uu____958 = (

let uu____979 = (

let uu____998 = (

let uu____999 = (

let uu____1000 = (

let uu____1005 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1006 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1005), (uu____1006))))
in (FStar_SMTEncoding_Util.mkGTE uu____1000))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____999))
in (quant xy uu____998))
in ((FStar_Parser_Const.op_GTE), (uu____979)))
in (

let uu____1023 = (

let uu____1046 = (

let uu____1067 = (

let uu____1086 = (

let uu____1087 = (

let uu____1088 = (

let uu____1093 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1094 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1093), (uu____1094))))
in (FStar_SMTEncoding_Util.mkSub uu____1088))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1087))
in (quant xy uu____1086))
in ((FStar_Parser_Const.op_Subtraction), (uu____1067)))
in (

let uu____1111 = (

let uu____1134 = (

let uu____1155 = (

let uu____1174 = (

let uu____1175 = (

let uu____1176 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____1176))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1175))
in (quant qx uu____1174))
in ((FStar_Parser_Const.op_Minus), (uu____1155)))
in (

let uu____1193 = (

let uu____1216 = (

let uu____1237 = (

let uu____1256 = (

let uu____1257 = (

let uu____1258 = (

let uu____1263 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1264 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1263), (uu____1264))))
in (FStar_SMTEncoding_Util.mkAdd uu____1258))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1257))
in (quant xy uu____1256))
in ((FStar_Parser_Const.op_Addition_lid), (uu____1237)))
in (

let uu____1281 = (

let uu____1304 = (

let uu____1325 = (

let uu____1344 = (

let uu____1345 = (

let uu____1346 = (

let uu____1351 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1352 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1351), (uu____1352))))
in (FStar_SMTEncoding_Util.mkMul uu____1346))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1345))
in (quant xy uu____1344))
in ((FStar_Parser_Const.op_Multiply), (uu____1325)))
in (

let uu____1369 = (

let uu____1392 = (

let uu____1413 = (

let uu____1432 = (

let uu____1433 = (

let uu____1434 = (

let uu____1439 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1440 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1439), (uu____1440))))
in (FStar_SMTEncoding_Util.mkDiv uu____1434))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1433))
in (quant xy uu____1432))
in ((FStar_Parser_Const.op_Division), (uu____1413)))
in (

let uu____1457 = (

let uu____1480 = (

let uu____1501 = (

let uu____1520 = (

let uu____1521 = (

let uu____1522 = (

let uu____1527 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1528 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1527), (uu____1528))))
in (FStar_SMTEncoding_Util.mkMod uu____1522))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1521))
in (quant xy uu____1520))
in ((FStar_Parser_Const.op_Modulus), (uu____1501)))
in (

let uu____1545 = (

let uu____1568 = (

let uu____1589 = (

let uu____1608 = (

let uu____1609 = (

let uu____1610 = (

let uu____1615 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1616 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1615), (uu____1616))))
in (FStar_SMTEncoding_Util.mkAnd uu____1610))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1609))
in (quant xy uu____1608))
in ((FStar_Parser_Const.op_And), (uu____1589)))
in (

let uu____1633 = (

let uu____1656 = (

let uu____1677 = (

let uu____1696 = (

let uu____1697 = (

let uu____1698 = (

let uu____1703 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1704 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1703), (uu____1704))))
in (FStar_SMTEncoding_Util.mkOr uu____1698))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1697))
in (quant xy uu____1696))
in ((FStar_Parser_Const.op_Or), (uu____1677)))
in (

let uu____1721 = (

let uu____1744 = (

let uu____1765 = (

let uu____1784 = (

let uu____1785 = (

let uu____1786 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____1786))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1785))
in (quant qx uu____1784))
in ((FStar_Parser_Const.op_Negation), (uu____1765)))
in (uu____1744)::[])
in (uu____1656)::uu____1721))
in (uu____1568)::uu____1633))
in (uu____1480)::uu____1545))
in (uu____1392)::uu____1457))
in (uu____1304)::uu____1369))
in (uu____1216)::uu____1281))
in (uu____1134)::uu____1193))
in (uu____1046)::uu____1111))
in (uu____958)::uu____1023))
in (uu____870)::uu____935))
in (uu____782)::uu____847))
in (uu____694)::uu____759))
in (uu____612)::uu____671))
in (uu____531)::uu____589))
in (

let mk1 = (fun l v1 -> (

let uu____2145 = (

let uu____2157 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____2247 -> (match (uu____2247) with
| (l', uu____2268) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____2157 (FStar_Option.map (fun uu____2367 -> (match (uu____2367) with
| (uu____2395, b) -> begin
(

let uu____2429 = (FStar_Ident.range_of_lid l)
in (b uu____2429 v1))
end)))))
in (FStar_All.pipe_right uu____2145 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____2512 -> (match (uu____2512) with
| (l', uu____2533) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_Range.range  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort * Prims.bool) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun rng env tapp vars -> (

let uu____2607 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____2607) with
| (xxsym, xx) -> begin
(

let uu____2618 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2618) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let uu____2634 = (

let uu____2642 = (

let uu____2643 = (

let uu____2654 = (

let uu____2655 = (FStar_SMTEncoding_Term.mk_fv ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____2665 = (

let uu____2676 = (FStar_SMTEncoding_Term.mk_fv ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))
in (uu____2676)::vars)
in (uu____2655)::uu____2665))
in (

let uu____2702 = (

let uu____2703 = (

let uu____2708 = (

let uu____2709 = (

let uu____2714 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____2714)))
in (FStar_SMTEncoding_Util.mkEq uu____2709))
in ((xx_has_type), (uu____2708)))
in (FStar_SMTEncoding_Util.mkImp uu____2703))
in ((((xx_has_type)::[])::[]), (uu____2654), (uu____2702))))
in (FStar_SMTEncoding_Term.mkForall rng uu____2643))
in (

let uu____2727 = (

let uu____2729 = (

let uu____2731 = (

let uu____2733 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____2733))
in (Prims.strcat module_name uu____2731))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____2729))
in ((uu____2642), (FStar_Pervasives_Native.Some ("pretyping")), (uu____2727))))
in (FStar_SMTEncoding_Util.mkAssume uu____2634)))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (FStar_SMTEncoding_Term.mk_fv (("x"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (FStar_SMTEncoding_Term.mk_fv (("y"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let uu____2786 = (

let uu____2787 = (

let uu____2795 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____2795), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2787))
in (

let uu____2800 = (

let uu____2803 = (

let uu____2804 = (

let uu____2812 = (

let uu____2813 = (

let uu____2824 = (

let uu____2825 = (

let uu____2830 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____2830)))
in (FStar_SMTEncoding_Util.mkImp uu____2825))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2824)))
in (

let uu____2855 = (

let uu____2870 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2870))
in (uu____2855 uu____2813)))
in ((uu____2812), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2804))
in (uu____2803)::[])
in (uu____2786)::uu____2800))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Bool_sort)))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____2898 = (

let uu____2899 = (

let uu____2907 = (

let uu____2908 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2909 = (

let uu____2920 = (

let uu____2925 = (

let uu____2928 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____2928)::[])
in (uu____2925)::[])
in (

let uu____2933 = (

let uu____2934 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____2934 tt))
in ((uu____2920), ((bb)::[]), (uu____2933))))
in (FStar_SMTEncoding_Term.mkForall uu____2908 uu____2909)))
in ((uu____2907), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2899))
in (

let uu____2959 = (

let uu____2962 = (

let uu____2963 = (

let uu____2971 = (

let uu____2972 = (

let uu____2983 = (

let uu____2984 = (

let uu____2989 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____2989)))
in (FStar_SMTEncoding_Util.mkImp uu____2984))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2983)))
in (

let uu____3016 = (

let uu____3031 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3031))
in (uu____3016 uu____2972)))
in ((uu____2971), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2963))
in (uu____2962)::[])
in (uu____2898)::uu____2959))))))
in (

let mk_int = (fun env nm tt -> (

let lex_t1 = (

let uu____3055 = (

let uu____3056 = (

let uu____3062 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____3062), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____3056))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3055))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Int_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Int_sort)))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes_y_x = (

let uu____3076 = (FStar_SMTEncoding_Util.mkApp (("Prims.precedes"), ((lex_t1)::(lex_t1)::(y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____3076))
in (

let uu____3081 = (

let uu____3082 = (

let uu____3090 = (

let uu____3091 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3092 = (

let uu____3103 = (

let uu____3108 = (

let uu____3111 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____3111)::[])
in (uu____3108)::[])
in (

let uu____3116 = (

let uu____3117 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____3117 tt))
in ((uu____3103), ((bb)::[]), (uu____3116))))
in (FStar_SMTEncoding_Term.mkForall uu____3091 uu____3092)))
in ((uu____3090), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____3082))
in (

let uu____3142 = (

let uu____3145 = (

let uu____3146 = (

let uu____3154 = (

let uu____3155 = (

let uu____3166 = (

let uu____3167 = (

let uu____3172 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____3172)))
in (FStar_SMTEncoding_Util.mkImp uu____3167))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____3166)))
in (

let uu____3199 = (

let uu____3214 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3214))
in (uu____3199 uu____3155)))
in ((uu____3154), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____3146))
in (

let uu____3219 = (

let uu____3222 = (

let uu____3223 = (

let uu____3231 = (

let uu____3232 = (

let uu____3243 = (

let uu____3244 = (

let uu____3249 = (

let uu____3250 = (

let uu____3253 = (

let uu____3256 = (

let uu____3259 = (

let uu____3260 = (

let uu____3265 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____3266 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____3265), (uu____3266))))
in (FStar_SMTEncoding_Util.mkGT uu____3260))
in (

let uu____3268 = (

let uu____3271 = (

let uu____3272 = (

let uu____3277 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____3278 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____3277), (uu____3278))))
in (FStar_SMTEncoding_Util.mkGTE uu____3272))
in (

let uu____3280 = (

let uu____3283 = (

let uu____3284 = (

let uu____3289 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____3290 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____3289), (uu____3290))))
in (FStar_SMTEncoding_Util.mkLT uu____3284))
in (uu____3283)::[])
in (uu____3271)::uu____3280))
in (uu____3259)::uu____3268))
in (typing_pred_y)::uu____3256)
in (typing_pred)::uu____3253)
in (FStar_SMTEncoding_Util.mk_and_l uu____3250))
in ((uu____3249), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____3244))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____3243)))
in (

let uu____3323 = (

let uu____3338 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3338))
in (uu____3323 uu____3232)))
in ((uu____3231), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____3223))
in (uu____3222)::[])
in (uu____3145)::uu____3219))
in (uu____3081)::uu____3142)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.String_sort)))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____3366 = (

let uu____3367 = (

let uu____3375 = (

let uu____3376 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3377 = (

let uu____3388 = (

let uu____3393 = (

let uu____3396 = (FStar_SMTEncoding_Term.boxString b)
in (uu____3396)::[])
in (uu____3393)::[])
in (

let uu____3401 = (

let uu____3402 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____3402 tt))
in ((uu____3388), ((bb)::[]), (uu____3401))))
in (FStar_SMTEncoding_Term.mkForall uu____3376 uu____3377)))
in ((uu____3375), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____3367))
in (

let uu____3427 = (

let uu____3430 = (

let uu____3431 = (

let uu____3439 = (

let uu____3440 = (

let uu____3451 = (

let uu____3452 = (

let uu____3457 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____3457)))
in (FStar_SMTEncoding_Util.mkImp uu____3452))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____3451)))
in (

let uu____3484 = (

let uu____3499 = (FStar_TypeChecker_Env.get_range env)
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____3499))
in (uu____3484 uu____3440)))
in ((uu____3439), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____3431))
in (uu____3430)::[])
in (uu____3366)::uu____3427))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (

let uu____3527 = (FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp")))
in (uu____3527)::[])))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____3555 = (

let uu____3556 = (

let uu____3564 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____3564), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3556))
in (uu____3555)::[])))
in (

let mk_and_interp = (fun env conj uu____3585 -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_and_a_b = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_and_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____3614 = (

let uu____3615 = (

let uu____3623 = (

let uu____3624 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3625 = (

let uu____3636 = (

let uu____3637 = (

let uu____3642 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____3642), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3637))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____3636)))
in (FStar_SMTEncoding_Term.mkForall uu____3624 uu____3625)))
in ((uu____3623), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3615))
in (uu____3614)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____3695 -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_or_a_b = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_or_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____3724 = (

let uu____3725 = (

let uu____3733 = (

let uu____3734 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3735 = (

let uu____3746 = (

let uu____3747 = (

let uu____3752 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____3752), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3747))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____3746)))
in (FStar_SMTEncoding_Term.mkForall uu____3734 uu____3735)))
in ((uu____3733), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3725))
in (uu____3724)::[]))))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xx1 = (FStar_SMTEncoding_Term.mk_fv (("x"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let yy1 = (FStar_SMTEncoding_Term.mk_fv (("y"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq2_x_y = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq2_x_y)::[])))
in (

let uu____3828 = (

let uu____3829 = (

let uu____3837 = (

let uu____3838 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3839 = (

let uu____3850 = (

let uu____3851 = (

let uu____3856 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____3856), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3851))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____3850)))
in (FStar_SMTEncoding_Term.mkForall uu____3838 uu____3839)))
in ((uu____3837), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3829))
in (uu____3828)::[]))))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xx1 = (FStar_SMTEncoding_Term.mk_fv (("x"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let yy1 = (FStar_SMTEncoding_Term.mk_fv (("y"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq3_x_y = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq3_x_y)::[])))
in (

let uu____3944 = (

let uu____3945 = (

let uu____3953 = (

let uu____3954 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3955 = (

let uu____3966 = (

let uu____3967 = (

let uu____3972 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____3972), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____3967))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____3966)))
in (FStar_SMTEncoding_Term.mkForall uu____3954 uu____3955)))
in ((uu____3953), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3945))
in (uu____3944)::[]))))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_imp_a_b = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_imp_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____4070 = (

let uu____4071 = (

let uu____4079 = (

let uu____4080 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4081 = (

let uu____4092 = (

let uu____4093 = (

let uu____4098 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____4098), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____4093))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____4092)))
in (FStar_SMTEncoding_Term.mkForall uu____4080 uu____4081)))
in ((uu____4079), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4071))
in (uu____4070)::[]))))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let bb = (FStar_SMTEncoding_Term.mk_fv (("b"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_iff_a_b = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_iff_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____4180 = (

let uu____4181 = (

let uu____4189 = (

let uu____4190 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4191 = (

let uu____4202 = (

let uu____4203 = (

let uu____4208 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____4208), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____4203))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____4202)))
in (FStar_SMTEncoding_Term.mkForall uu____4190 uu____4191)))
in ((uu____4189), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4181))
in (uu____4180)::[]))))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (FStar_SMTEncoding_Term.mk_fv (("a"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let l_not_a = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_not_a)::[])))
in (

let not_valid_a = (

let uu____4277 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____4277))
in (

let uu____4282 = (

let uu____4283 = (

let uu____4291 = (

let uu____4292 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4293 = (

let uu____4304 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____4304)))
in (FStar_SMTEncoding_Term.mkForall uu____4292 uu____4293)))
in ((uu____4291), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4283))
in (uu____4282)::[])))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____4355 = (

let uu____4356 = (

let uu____4364 = (

let uu____4365 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____4365 range_ty))
in (

let uu____4366 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "typing_range_const")
in ((uu____4364), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____4366))))
in (FStar_SMTEncoding_Util.mkAssume uu____4356))
in (uu____4355)::[])))
in (

let mk_inversion_axiom = (fun env inversion tt -> (

let tt1 = (FStar_SMTEncoding_Term.mk_fv (("t"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let xx1 = (FStar_SMTEncoding_Term.mk_fv (("x"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let inversion_t = (FStar_SMTEncoding_Util.mkApp ((inversion), ((t)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((inversion_t)::[])))
in (

let body = (

let hastypeZ = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 t)
in (

let hastypeS = (

let uu____4410 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____4410 x1 t))
in (

let uu____4412 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4413 = (

let uu____4424 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____4424)))
in (FStar_SMTEncoding_Term.mkForall uu____4412 uu____4413)))))
in (

let uu____4449 = (

let uu____4450 = (

let uu____4458 = (

let uu____4459 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4460 = (

let uu____4471 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____4471)))
in (FStar_SMTEncoding_Term.mkForall uu____4459 uu____4460)))
in ((uu____4458), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____4450))
in (uu____4449)::[])))))))))
in (

let mk_with_type_axiom = (fun env with_type1 tt -> (

let tt1 = (FStar_SMTEncoding_Term.mk_fv (("t"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let ee = (FStar_SMTEncoding_Term.mk_fv (("e"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let e = (FStar_SMTEncoding_Util.mkFreeV ee)
in (

let with_type_t_e = (FStar_SMTEncoding_Util.mkApp ((with_type1), ((t)::(e)::[])))
in (

let uu____4530 = (

let uu____4531 = (

let uu____4539 = (

let uu____4540 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____4541 = (

let uu____4557 = (

let uu____4558 = (

let uu____4563 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____4564 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____4563), (uu____4564))))
in (FStar_SMTEncoding_Util.mkAnd uu____4558))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____4557)))
in (FStar_SMTEncoding_Term.mkForall' uu____4540 uu____4541)))
in ((uu____4539), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____4531))
in (uu____4530)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____5094 = (FStar_Util.find_opt (fun uu____5132 -> (match (uu____5132) with
| (l, uu____5148) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____5094) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____5191, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5252 = (FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env)
in (match (uu____5252) with
| (form, decls) -> begin
(

let uu____5261 = (

let uu____5264 = (FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str))))
in (uu____5264)::[])
in (FStar_List.append decls uu____5261))
end))))


let encode_free_var : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____5317 = (((

let uu____5321 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.FStar_SMTEncoding_Env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____5321)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____5317) with
| true -> begin
(

let arg_sorts = (

let uu____5335 = (

let uu____5336 = (FStar_Syntax_Subst.compress t_norm)
in uu____5336.FStar_Syntax_Syntax.n)
in (match (uu____5335) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____5342) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____5380 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____5387 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____5389 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____5389) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____5429 -> begin
(

let uu____5431 = (prims.is lid)
in (match (uu____5431) with
| true -> begin
(

let vname = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar lid)
in (

let uu____5442 = (prims.mk lid vname)
in (match (uu____5442) with
| (tok, arity, definition) -> begin
(

let env1 = (FStar_SMTEncoding_Env.push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____5470 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____5476 = (

let uu____5495 = (FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp t_norm)
in (match (uu____5495) with
| (args, comp) -> begin
(

let comp1 = (

let uu____5523 = (FStar_TypeChecker_Env.is_reifiable_comp env.FStar_SMTEncoding_Env.tcenv comp)
in (match (uu____5523) with
| true -> begin
(

let uu____5528 = (FStar_TypeChecker_Env.reify_comp (

let uu___385_5531 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___385_5531.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___385_5531.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___385_5531.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___385_5531.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___385_5531.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___385_5531.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___385_5531.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___385_5531.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___385_5531.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___385_5531.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___385_5531.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___385_5531.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___385_5531.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___385_5531.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___385_5531.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___385_5531.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___385_5531.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___385_5531.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___385_5531.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___385_5531.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___385_5531.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___385_5531.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___385_5531.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___385_5531.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___385_5531.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___385_5531.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___385_5531.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___385_5531.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___385_5531.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___385_5531.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___385_5531.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___385_5531.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___385_5531.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___385_5531.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___385_5531.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___385_5531.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___385_5531.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___385_5531.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___385_5531.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___385_5531.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___385_5531.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___385_5531.FStar_TypeChecker_Env.nbe}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____5528))
end
| uu____5533 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____5554 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.FStar_SMTEncoding_Env.tcenv comp1)
in ((args), (uu____5554)))
end
| uu____5575 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____5476) with
| (formals, (pre_opt, res_t)) -> begin
(

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___375_5662 -> (match (uu___375_5662) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____5666 = (FStar_Util.prefix vars)
in (match (uu____5666) with
| (uu____5699, xxv) -> begin
(

let xx = (

let uu____5738 = (

let uu____5739 = (

let uu____5745 = (FStar_SMTEncoding_Term.fv_name xxv)
in ((uu____5745), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____5739))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____5738))
in (

let uu____5748 = (

let uu____5749 = (

let uu____5757 = (

let uu____5758 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____5759 = (

let uu____5770 = (

let uu____5771 = (

let uu____5776 = (

let uu____5777 = (FStar_SMTEncoding_Term.mk_tester (FStar_SMTEncoding_Env.escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____5777))
in ((vapp), (uu____5776)))
in (FStar_SMTEncoding_Util.mkEq uu____5771))
in ((((vapp)::[])::[]), (vars), (uu____5770)))
in (FStar_SMTEncoding_Term.mkForall uu____5758 uu____5759)))
in ((uu____5757), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (FStar_SMTEncoding_Env.escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____5749))
in (uu____5748)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____5792 = (FStar_Util.prefix vars)
in (match (uu____5792) with
| (uu____5825, xxv) -> begin
(

let xx = (

let uu____5864 = (

let uu____5865 = (

let uu____5871 = (FStar_SMTEncoding_Term.fv_name xxv)
in ((uu____5871), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____5865))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____5864))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (FStar_SMTEncoding_Env.mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____5882 = (

let uu____5883 = (

let uu____5891 = (

let uu____5892 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____5893 = (

let uu____5904 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____5904)))
in (FStar_SMTEncoding_Term.mkForall uu____5892 uu____5893)))
in ((uu____5891), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____5883))
in (uu____5882)::[])))))
end))
end
| uu____5917 -> begin
[]
end)))))
in (

let uu____5918 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals env)
in (match (uu____5918) with
| (vars, guards, env', decls1, uu____5945) -> begin
(

let uu____5958 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5971 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____5971), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____5975 = (FStar_SMTEncoding_EncodeTerm.encode_formula p env')
in (match (uu____5975) with
| (g, ds) -> begin
(

let uu____5988 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____5988), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____5958) with
| (guard, decls11) -> begin
(

let dummy_var = (FStar_SMTEncoding_Term.mk_fv (("@dummy"), (FStar_SMTEncoding_Term.dummy_sort)))
in (

let dummy_tm = (FStar_SMTEncoding_Term.mkFreeV dummy_var FStar_Range.dummyRange)
in (

let should_thunk = (fun uu____6013 -> (

let is_type1 = (fun t -> (

let uu____6021 = (

let uu____6022 = (FStar_Syntax_Subst.compress t)
in uu____6022.FStar_Syntax_Syntax.n)
in (match (uu____6021) with
| FStar_Syntax_Syntax.Tm_type (uu____6026) -> begin
true
end
| uu____6028 -> begin
false
end)))
in (

let is_squash1 = (fun t -> (

let uu____6037 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____6037) with
| (head1, uu____6056) -> begin
(

let uu____6081 = (

let uu____6082 = (FStar_Syntax_Util.un_uinst head1)
in uu____6082.FStar_Syntax_Syntax.n)
in (match (uu____6081) with
| FStar_Syntax_Syntax.Tm_fvar (fv1) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 FStar_Parser_Const.squash_lid)
end
| FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = uu____6087; FStar_Syntax_Syntax.index = uu____6088; FStar_Syntax_Syntax.sort = {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____6090; FStar_Syntax_Syntax.vars = uu____6091}}, uu____6092) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv1 FStar_Parser_Const.unit_lid)
end
| uu____6100 -> begin
false
end))
end)))
in ((((Prims.op_disEquality lid.FStar_Ident.nsstr "Prims") && (

let uu____6105 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (not (uu____6105)))) && (

let uu____6111 = (is_squash1 t_norm)
in (not (uu____6111)))) && (

let uu____6114 = (is_type1 t_norm)
in (not (uu____6114)))))))
in (

let uu____6116 = (match (vars) with
| [] when (should_thunk ()) -> begin
((true), ((dummy_var)::[]))
end
| uu____6175 -> begin
((false), (vars))
end)
in (match (uu____6116) with
| (thunked, vars1) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____6227 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked env lid arity thunked)
in (match (uu____6227) with
| (vname, vtok_opt, env1) -> begin
(

let get_vtok = (fun uu____6265 -> (FStar_Option.get vtok_opt))
in (

let vtok_tm = (match (formals) with
| [] when (not (thunked)) -> begin
(

let uu____6274 = (FStar_SMTEncoding_Term.mk_fv ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____6274))
end
| [] when thunked -> begin
(FStar_SMTEncoding_Util.mkApp ((vname), ((dummy_tm)::[])))
end
| uu____6285 -> begin
(

let uu____6294 = (

let uu____6302 = (get_vtok ())
in ((uu____6302), ([])))
in (FStar_SMTEncoding_Util.mkApp uu____6294))
end)
in (

let vapp = (

let uu____6308 = (

let uu____6316 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in ((vname), (uu____6316)))
in (FStar_SMTEncoding_Util.mkApp uu____6308))
in (

let uu____6330 = (

let vname_decl = (

let uu____6338 = (

let uu____6350 = (FStar_All.pipe_right vars1 (FStar_List.map FStar_SMTEncoding_Term.fv_sort))
in ((vname), (uu____6350), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____6338))
in (

let uu____6361 = (

let env2 = (

let uu___386_6367 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___386_6367.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___386_6367.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___386_6367.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___386_6367.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___386_6367.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___386_6367.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___386_6367.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___386_6367.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___386_6367.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___386_6367.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let uu____6368 = (

let uu____6370 = (FStar_SMTEncoding_EncodeTerm.head_normal env2 tt)
in (not (uu____6370)))
in (match (uu____6368) with
| true -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____6377 -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____6361) with
| (tok_typing, decls2) -> begin
(

let uu____6387 = (match (vars1) with
| [] -> begin
(

let tok_typing1 = (FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
in (

let uu____6413 = (

let uu____6414 = (

let uu____6417 = (

let uu____6418 = (FStar_SMTEncoding_Term.mk_fv ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mkFreeV uu____6418))
in (FStar_All.pipe_left (fun _0_1 -> FStar_Pervasives_Native.Some (_0_1)) uu____6417))
in (FStar_SMTEncoding_Env.push_free_var env1 lid arity vname uu____6414))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____6413))))
end
| uu____6428 when thunked -> begin
(

let uu____6439 = (FStar_Options.protect_top_level_axioms ())
in (match (uu____6439) with
| true -> begin
((decls2), (env1))
end
| uu____6450 -> begin
(

let intro_ambient1 = (

let t = (

let uu____6454 = (

let uu____6462 = (

let uu____6465 = (

let uu____6468 = (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort), (true)))
in (uu____6468)::[])
in (FStar_SMTEncoding_Term.mk_Term_unit)::uu____6465)
in (("FStar.Pervasives.ambient"), (uu____6462)))
in (FStar_SMTEncoding_Term.mkApp uu____6454 FStar_Range.dummyRange))
in (

let uu____6476 = (

let uu____6484 = (FStar_SMTEncoding_Term.mk_Valid t)
in ((uu____6484), (FStar_Pervasives_Native.Some ("Ambient nullary symbol trigger")), ((Prims.strcat "intro_ambient_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____6476)))
in (((FStar_List.append decls2 ((intro_ambient1)::[]))), (env1)))
end))
end
| uu____6491 -> begin
(

let vtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm vars1)
in (

let vtok = (get_vtok ())
in (

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let name_tok_corr_formula = (fun pat -> (

let uu____6516 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6517 = (

let uu____6528 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((pat)::[])::[]), (vars1), (uu____6528)))
in (FStar_SMTEncoding_Term.mkForall uu____6516 uu____6517))))
in (

let name_tok_corr = (

let uu____6538 = (

let uu____6546 = (name_tok_corr_formula vtok_app)
in ((uu____6546), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____6538))
in (

let tok_typing1 = (

let ff = (FStar_SMTEncoding_Term.mk_fv (("ty"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_r = (

let uu____6557 = (

let uu____6558 = (FStar_SMTEncoding_Term.mk_fv ((vtok), (FStar_SMTEncoding_Term.Term_sort)))
in (uu____6558)::[])
in (FStar_SMTEncoding_EncodeTerm.mk_Apply f uu____6557))
in (

let guarded_tok_typing = (

let uu____6585 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6586 = (

let uu____6597 = (

let uu____6598 = (

let uu____6603 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in (

let uu____6604 = (name_tok_corr_formula vapp)
in ((uu____6603), (uu____6604))))
in (FStar_SMTEncoding_Util.mkAnd uu____6598))
in ((((vtok_app_r)::[])::[]), ((ff)::[]), (uu____6597)))
in (FStar_SMTEncoding_Term.mkForall uu____6585 uu____6586)))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))))))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1))))))))
end)
in (match (uu____6387) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end))
end)))
in (match (uu____6330) with
| (decls2, env2) -> begin
(

let uu____6661 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____6671 = (FStar_SMTEncoding_EncodeTerm.encode_term res_t1 env')
in (match (uu____6671) with
| (encoded_res_t, decls) -> begin
(

let uu____6686 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____6686), (decls)))
end)))
in (match (uu____6661) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____6703 = (

let uu____6711 = (

let uu____6712 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6713 = (

let uu____6724 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars1), (uu____6724)))
in (FStar_SMTEncoding_Term.mkForall uu____6712 uu____6713)))
in ((uu____6711), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____6703))
in (

let freshness = (

let uu____6740 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____6740) with
| true -> begin
(

let uu____6748 = (

let uu____6749 = (FStar_Syntax_Syntax.range_of_fv fv)
in (

let uu____6750 = (

let uu____6763 = (FStar_All.pipe_right vars1 (FStar_List.map FStar_SMTEncoding_Term.fv_sort))
in (

let uu____6770 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((vname), (uu____6763), (FStar_SMTEncoding_Term.Term_sort), (uu____6770))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____6749 uu____6750)))
in (

let uu____6776 = (

let uu____6779 = (

let uu____6780 = (FStar_Syntax_Syntax.range_of_fv fv)
in (pretype_axiom uu____6780 env2 vapp vars1))
in (uu____6779)::[])
in (uu____6748)::uu____6776))
end
| uu____6781 -> begin
[]
end))
in (

let g = (

let uu____6786 = (

let uu____6789 = (

let uu____6792 = (

let uu____6795 = (

let uu____6798 = (mk_disc_proj_axioms guard encoded_res_t vapp vars1)
in (typingAx)::uu____6798)
in (FStar_List.append freshness uu____6795))
in (FStar_List.append decls3 uu____6792))
in (FStar_List.append decls2 uu____6789))
in (FStar_List.append decls11 uu____6786))
in ((g), (env2)))))
end))
end)))))
end)))
end)))))
end))
end)))
end)))
end))
end))))


let declare_top_level_let : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env x t t_norm -> (

let uu____6836 = (FStar_SMTEncoding_Env.lookup_fvar_binding env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____6836) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6847 = (encode_free_var false env x t t_norm [])
in (match (uu____6847) with
| (decls, env1) -> begin
(

let fvb = (FStar_SMTEncoding_Env.lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env lid t quals -> (

let tt = (FStar_SMTEncoding_EncodeTerm.norm env t)
in (

let uu____6918 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____6918) with
| (decls, env1) -> begin
(

let uu____6937 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____6937) with
| true -> begin
(

let uu____6946 = (

let uu____6949 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____6949))
in ((uu____6946), (env1)))
end
| uu____6954 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____7009 lb -> (match (uu____7009) with
| (decls, env1) -> begin
(

let uu____7029 = (

let uu____7036 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____7036 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____7029) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____7069 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____7069) with
| (hd1, args) -> begin
(

let uu____7113 = (

let uu____7114 = (FStar_Syntax_Util.un_uinst hd1)
in uu____7114.FStar_Syntax_Syntax.n)
in (match (uu____7113) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____7120, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____7144 -> begin
false
end))
end))))

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____7155 -> begin
false
end))


let copy_env : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Env.env_t = (fun en -> (

let uu___387_7163 = en
in (

let uu____7164 = (FStar_Util.smap_copy en.FStar_SMTEncoding_Env.cache)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___387_7163.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___387_7163.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___387_7163.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___387_7163.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___387_7163.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu____7164; FStar_SMTEncoding_Env.nolabels = uu___387_7163.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___387_7163.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___387_7163.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___387_7163.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___387_7163.FStar_SMTEncoding_Env.encoding_quantifier})))


let encode_top_level_let : FStar_SMTEncoding_Env.env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env uu____7196 quals -> (match (uu____7196) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____7303 = (FStar_Util.first_N nbinders formals)
in (match (uu____7303) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____7404 uu____7405 -> (match (((uu____7404), (uu____7405))) with
| ((formal, uu____7431), (binder, uu____7433)) -> begin
(

let uu____7454 = (

let uu____7461 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____7461)))
in FStar_Syntax_Syntax.NT (uu____7454))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____7475 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____7516 -> (match (uu____7516) with
| (x, i) -> begin
(

let uu____7535 = (

let uu___388_7536 = x
in (

let uu____7537 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___388_7536.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___388_7536.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____7537}))
in ((uu____7535), (i)))
end))))
in (FStar_All.pipe_right uu____7475 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____7561 = (

let uu____7566 = (FStar_Syntax_Subst.compress body)
in (

let uu____7567 = (

let uu____7568 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____7568))
in (FStar_Syntax_Syntax.extend_app_n uu____7566 uu____7567)))
in (uu____7561 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun t e -> (

let tcenv = (

let uu___389_7619 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___389_7619.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___389_7619.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___389_7619.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___389_7619.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_sig = uu___389_7619.FStar_TypeChecker_Env.gamma_sig; FStar_TypeChecker_Env.gamma_cache = uu___389_7619.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___389_7619.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___389_7619.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___389_7619.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.attrtab = uu___389_7619.FStar_TypeChecker_Env.attrtab; FStar_TypeChecker_Env.is_pattern = uu___389_7619.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___389_7619.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___389_7619.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___389_7619.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___389_7619.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___389_7619.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___389_7619.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___389_7619.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___389_7619.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___389_7619.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___389_7619.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.phase1 = uu___389_7619.FStar_TypeChecker_Env.phase1; FStar_TypeChecker_Env.failhard = uu___389_7619.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___389_7619.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.uvar_subtyping = uu___389_7619.FStar_TypeChecker_Env.uvar_subtyping; FStar_TypeChecker_Env.tc_term = uu___389_7619.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___389_7619.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___389_7619.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___389_7619.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___389_7619.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___389_7619.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___389_7619.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.fv_delta_depths = uu___389_7619.FStar_TypeChecker_Env.fv_delta_depths; FStar_TypeChecker_Env.proof_ns = uu___389_7619.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___389_7619.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___389_7619.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.postprocess = uu___389_7619.FStar_TypeChecker_Env.postprocess; FStar_TypeChecker_Env.is_native_tactic = uu___389_7619.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___389_7619.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___389_7619.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___389_7619.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.nbe = uu___389_7619.FStar_TypeChecker_Env.nbe})
in (

let subst_comp1 = (fun formals actuals comp -> (

let subst1 = (FStar_List.map2 (fun uu____7691 uu____7692 -> (match (((uu____7691), (uu____7692))) with
| ((x, uu____7718), (b, uu____7720)) -> begin
(

let uu____7741 = (

let uu____7748 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____7748)))
in FStar_Syntax_Syntax.NT (uu____7741))
end)) formals actuals)
in (FStar_Syntax_Subst.subst_comp subst1 comp)))
in (

let rec arrow_formals_comp_norm = (fun norm1 t1 -> (

let t2 = (

let uu____7773 = (FStar_Syntax_Subst.compress t1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____7773))
in (match (t2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (formals, comp) -> begin
(FStar_Syntax_Subst.open_comp formals comp)
end
| FStar_Syntax_Syntax.Tm_refine (uu____7802) -> begin
(

let uu____7809 = (FStar_Syntax_Util.unrefine t2)
in (arrow_formals_comp_norm norm1 uu____7809))
end
| uu____7810 when (not (norm1)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.AllowUnboundUniverses)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Weak)::(FStar_TypeChecker_Env.HNF)::(FStar_TypeChecker_Env.Exclude (FStar_TypeChecker_Env.Zeta))::(FStar_TypeChecker_Env.UnfoldUntil (FStar_Syntax_Syntax.delta_constant))::(FStar_TypeChecker_Env.EraseUniverses)::[]) tcenv t2)
in (arrow_formals_comp_norm true t_norm))
end
| uu____7813 -> begin
(

let uu____7814 = (FStar_Syntax_Syntax.mk_Total t2)
in (([]), (uu____7814)))
end)))
in (

let aux = (fun t1 e1 -> (

let uu____7856 = (FStar_Syntax_Util.abs_formals e1)
in (match (uu____7856) with
| (binders, body, lopt) -> begin
(

let uu____7888 = (match (binders) with
| [] -> begin
(arrow_formals_comp_norm true t1)
end
| uu____7904 -> begin
(arrow_formals_comp_norm false t1)
end)
in (match (uu____7888) with
| (formals, comp) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let uu____7938 = (match ((nformals < nbinders)) with
| true -> begin
(

let uu____7982 = (FStar_Util.first_N nformals binders)
in (match (uu____7982) with
| (bs0, rest) -> begin
(

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____8066 = (subst_comp1 formals bs0 comp)
in ((bs0), (body1), (uu____8066))))
end))
end
| uu____8077 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____8106 = (eta_expand1 binders formals body (FStar_Syntax_Util.comp_result comp))
in (match (uu____8106) with
| (binders1, body1) -> begin
(

let uu____8159 = (subst_comp1 formals binders1 comp)
in ((binders1), (body1), (uu____8159)))
end))
end
| uu____8170 -> begin
(

let uu____8172 = (subst_comp1 formals binders comp)
in ((binders), (body), (uu____8172)))
end)
end)
in (match (uu____7938) with
| (binders1, body1, comp1) -> begin
((binders1), (body1), (comp1))
end))))
end))
end)))
in (

let uu____8232 = (aux t e)
in (match (uu____8232) with
| (binders, body, comp) -> begin
(

let uu____8278 = (

let uu____8289 = (FStar_TypeChecker_Env.is_reifiable_comp tcenv comp)
in (match (uu____8289) with
| true -> begin
(

let comp1 = (FStar_TypeChecker_Env.reify_comp tcenv comp FStar_Syntax_Syntax.U_unknown)
in (

let body1 = (FStar_TypeChecker_Util.reify_body tcenv body)
in (

let uu____8304 = (aux comp1 body1)
in (match (uu____8304) with
| (more_binders, body2, comp2) -> begin
(((FStar_List.append binders more_binders)), (body2), (comp2))
end))))
end
| uu____8364 -> begin
((binders), (body), (comp))
end))
in (match (uu____8278) with
| (binders1, body1, comp1) -> begin
(

let uu____8387 = (FStar_Syntax_Util.ascribe body1 ((FStar_Util.Inl ((FStar_Syntax_Util.comp_result comp1))), (FStar_Pervasives_Native.None)))
in ((binders1), (uu____8387), (comp1)))
end))
end)))))))
in (FStar_All.try_with (fun uu___391_8414 -> (match (()) with
| () -> begin
(

let uu____8421 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____8421) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____8435 -> begin
(

let uu____8437 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____8500 lb -> (match (uu____8500) with
| (toks, typs, decls, env1) -> begin
((

let uu____8555 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____8555) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____8558 -> begin
()
end));
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____8561 = (

let uu____8570 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____8570 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____8561) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____8437) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let env_decls = (copy_env env1)
in (

let typs1 = (FStar_List.rev typs)
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____8711; FStar_Syntax_Syntax.lbeff = uu____8712; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____8714; FStar_Syntax_Syntax.lbpos = uu____8715})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let uu____8739 = (

let uu____8746 = (FStar_TypeChecker_Env.open_universes_in env2.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____8746) with
| (tcenv', uu____8762, e_t) -> begin
(

let uu____8768 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____8779 -> begin
(failwith "Impossible")
end)
in (match (uu____8768) with
| (e1, t_norm1) -> begin
(((

let uu___392_8796 = env2
in {FStar_SMTEncoding_Env.bvar_bindings = uu___392_8796.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___392_8796.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___392_8796.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___392_8796.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___392_8796.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___392_8796.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___392_8796.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___392_8796.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___392_8796.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___392_8796.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____8739) with
| (env', e1, t_norm1) -> begin
(

let uu____8806 = (destruct_bound_function t_norm1 e1)
in (match (uu____8806) with
| (binders, body, t_body_comp) -> begin
(

let t_body = (FStar_Syntax_Util.comp_result t_body_comp)
in ((

let uu____8826 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____8826) with
| true -> begin
(

let uu____8831 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____8834 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____8831 uu____8834)))
end
| uu____8837 -> begin
()
end));
(

let uu____8839 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____8839) with
| (vars, _guards, env'1, binder_decls, uu____8866) -> begin
(

let uu____8879 = (match ((fvb.FStar_SMTEncoding_Env.fvb_thunked && (Prims.op_Equality vars []))) with
| true -> begin
(

let dummy_var = (FStar_SMTEncoding_Term.mk_fv (("@dummy"), (FStar_SMTEncoding_Term.dummy_sort)))
in (

let dummy_tm = (FStar_SMTEncoding_Term.mkFreeV dummy_var FStar_Range.dummyRange)
in (

let app = (

let uu____8896 = (FStar_Syntax_Util.range_of_lbname lbn)
in (FStar_SMTEncoding_Term.mkApp ((fvb.FStar_SMTEncoding_Env.smt_id), ((dummy_tm)::[])) uu____8896))
in (((dummy_var)::[]), (app)))))
end
| uu____8916 -> begin
(

let uu____8918 = (

let uu____8919 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____8920 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb uu____8919 fvb uu____8920)))
in ((vars), (uu____8918)))
end)
in (match (uu____8879) with
| (vars1, app) -> begin
(

let uu____8931 = (

let is_logical = (

let uu____8944 = (

let uu____8945 = (FStar_Syntax_Subst.compress t_body)
in uu____8945.FStar_Syntax_Syntax.n)
in (match (uu____8944) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.logical_lid) -> begin
true
end
| uu____8951 -> begin
false
end))
in (

let is_prims = (

let uu____8955 = (

let uu____8956 = (FStar_All.pipe_right lbn FStar_Util.right)
in (FStar_All.pipe_right uu____8956 FStar_Syntax_Syntax.lid_of_fv))
in (FStar_All.pipe_right uu____8955 (fun lid -> (

let uu____8965 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (FStar_Ident.lid_equals uu____8965 FStar_Parser_Const.prims_lid)))))
in (

let uu____8966 = ((not (is_prims)) && ((FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) || is_logical))
in (match (uu____8966) with
| true -> begin
(

let uu____8982 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____8983 = (FStar_SMTEncoding_EncodeTerm.encode_formula body env'1)
in ((app), (uu____8982), (uu____8983))))
end
| uu____8992 -> begin
(

let uu____8994 = (FStar_SMTEncoding_EncodeTerm.encode_term body env'1)
in ((app), (app), (uu____8994)))
end))))
in (match (uu____8931) with
| (pat, app1, (body1, decls2)) -> begin
(

let eqn = (

let uu____9018 = (

let uu____9026 = (

let uu____9027 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9028 = (

let uu____9039 = (FStar_SMTEncoding_Util.mkEq ((app1), (body1)))
in ((((pat)::[])::[]), (vars1), (uu____9039)))
in (FStar_SMTEncoding_Term.mkForall uu____9027 uu____9028)))
in (

let uu____9048 = (

let uu____9049 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____9049))
in ((uu____9026), (uu____9048), ((Prims.strcat "equation_" fvb.FStar_SMTEncoding_Env.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____9018))
in (

let uu____9055 = (

let uu____9058 = (

let uu____9061 = (

let uu____9064 = (

let uu____9067 = (primitive_type_axioms env2.FStar_SMTEncoding_Env.tcenv flid fvb.FStar_SMTEncoding_Env.smt_id app1)
in (FStar_List.append ((eqn)::[]) uu____9067))
in (FStar_List.append decls2 uu____9064))
in (FStar_List.append binder_decls uu____9061))
in (FStar_List.append decls1 uu____9058))
in ((uu____9055), (env2))))
end))
end))
end));
))
end))
end)))
end
| uu____9072 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____9132 = (

let uu____9138 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "fuel")
in ((uu____9138), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____9132))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____9144 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____9197 fvb -> (match (uu____9197) with
| (gtoks, env3) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let g = (

let uu____9252 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____9252))
in (

let gtok = (

let uu____9256 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____9256))
in (

let env4 = (

let uu____9259 = (

let uu____9262 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_2 -> FStar_Pervasives_Native.Some (_0_2)) uu____9262))
in (FStar_SMTEncoding_Env.push_free_var env3 flid fvb.FStar_SMTEncoding_Env.smt_arity gtok uu____9259))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____9144) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____9389 t_norm uu____9391 -> (match (((uu____9389), (uu____9391))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____9423; FStar_Syntax_Syntax.lbeff = uu____9424; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____9426; FStar_Syntax_Syntax.lbpos = uu____9427}) -> begin
(

let uu____9454 = (

let uu____9461 = (FStar_TypeChecker_Env.open_universes_in env3.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____9461) with
| (tcenv', uu____9477, e_t) -> begin
(

let uu____9483 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____9494 -> begin
(failwith "Impossible")
end)
in (match (uu____9483) with
| (e1, t_norm1) -> begin
(((

let uu___393_9511 = env3
in {FStar_SMTEncoding_Env.bvar_bindings = uu___393_9511.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___393_9511.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___393_9511.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___393_9511.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___393_9511.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___393_9511.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___393_9511.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___393_9511.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___393_9511.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___393_9511.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____9454) with
| (env', e1, t_norm1) -> begin
((

let uu____9526 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____9526) with
| true -> begin
(

let uu____9531 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____9533 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____9535 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____9531 uu____9533 uu____9535))))
end
| uu____9538 -> begin
()
end));
(

let uu____9540 = (destruct_bound_function t_norm1 e1)
in (match (uu____9540) with
| (binders, body, tres_comp) -> begin
(

let curry = (Prims.op_disEquality fvb.FStar_SMTEncoding_Env.smt_arity (FStar_List.length binders))
in (

let uu____9569 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env3.FStar_SMTEncoding_Env.tcenv tres_comp)
in (match (uu____9569) with
| (pre_opt, tres) -> begin
((

let uu____9593 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____9593) with
| true -> begin
(

let uu____9598 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____9600 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____9603 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____9605 = (FStar_Syntax_Print.comp_to_string tres_comp)
in (FStar_Util.print4 "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n" uu____9598 uu____9600 uu____9603 uu____9605)))))
end
| uu____9608 -> begin
()
end));
(

let uu____9610 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____9610) with
| (vars, guards, env'1, binder_decls, uu____9641) -> begin
(

let uu____9654 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9667 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____9667), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____9671 = (FStar_SMTEncoding_EncodeTerm.encode_formula pre env'1)
in (match (uu____9671) with
| (guard, decls0) -> begin
(

let uu____9684 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append guards ((guard)::[])))
in ((uu____9684), (decls0)))
end))
end)
in (match (uu____9654) with
| (guard, guard_decls) -> begin
(

let binder_decls1 = (FStar_List.append binder_decls guard_decls)
in (

let decl_g = (

let uu____9707 = (

let uu____9719 = (

let uu____9722 = (

let uu____9725 = (

let uu____9728 = (FStar_Util.first_N fvb.FStar_SMTEncoding_Env.smt_arity vars)
in (FStar_Pervasives_Native.fst uu____9728))
in (FStar_List.map FStar_SMTEncoding_Term.fv_sort uu____9725))
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____9722)
in ((g), (uu____9719), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____9707))
in (

let env02 = (FStar_SMTEncoding_Env.push_zfuel_name env01 fvb.FStar_SMTEncoding_Env.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let rng = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let app = (

let uu____9758 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb rng fvb uu____9758))
in (

let mk_g_app = (fun args -> (FStar_SMTEncoding_EncodeTerm.maybe_curry_app rng (FStar_Util.Inl (FStar_SMTEncoding_Term.Var (g))) (fvb.FStar_SMTEncoding_Env.smt_arity + (Prims.parse_int "1")) args))
in (

let gsapp = (

let uu____9773 = (

let uu____9776 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____9776)::vars_tm)
in (mk_g_app uu____9773))
in (

let gmax = (

let uu____9782 = (

let uu____9785 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____9785)::vars_tm)
in (mk_g_app uu____9782))
in (

let uu____9790 = (FStar_SMTEncoding_EncodeTerm.encode_term body env'1)
in (match (uu____9790) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____9808 = (

let uu____9816 = (

let uu____9817 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9818 = (

let uu____9834 = (

let uu____9835 = (

let uu____9840 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((guard), (uu____9840)))
in (FStar_SMTEncoding_Util.mkImp uu____9835))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____9834)))
in (FStar_SMTEncoding_Term.mkForall' uu____9817 uu____9818)))
in (

let uu____9854 = (

let uu____9855 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.FStar_SMTEncoding_Env.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____9855))
in ((uu____9816), (uu____9854), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____9808))
in (

let eqn_f = (

let uu____9862 = (

let uu____9870 = (

let uu____9871 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9872 = (

let uu____9883 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____9883)))
in (FStar_SMTEncoding_Term.mkForall uu____9871 uu____9872)))
in ((uu____9870), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____9862))
in (

let eqn_g' = (

let uu____9897 = (

let uu____9905 = (

let uu____9906 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9907 = (

let uu____9918 = (

let uu____9919 = (

let uu____9924 = (

let uu____9925 = (

let uu____9928 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____9928)::vars_tm)
in (mk_g_app uu____9925))
in ((gsapp), (uu____9924)))
in (FStar_SMTEncoding_Util.mkEq uu____9919))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____9918)))
in (FStar_SMTEncoding_Term.mkForall uu____9906 uu____9907)))
in ((uu____9905), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____9897))
in (

let uu____9942 = (

let gapp = (mk_g_app ((fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (

let uu____9954 = (

let uu____9955 = (FStar_SMTEncoding_Term.mk_fv ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____9955))
in (FStar_SMTEncoding_EncodeTerm.mk_Apply uu____9954 ((fuel)::vars)))
in (

let uu____9957 = (

let uu____9965 = (

let uu____9966 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____9967 = (

let uu____9978 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____9978)))
in (FStar_SMTEncoding_Term.mkForall uu____9966 uu____9967)))
in ((uu____9965), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____9957)))
in (

let uu____9991 = (

let uu____10000 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tres env'1 gapp)
in (match (uu____10000) with
| (g_typing, d3) -> begin
(

let uu____10015 = (

let uu____10018 = (

let uu____10019 = (

let uu____10027 = (

let uu____10028 = (FStar_Syntax_Util.range_of_lbname lbn)
in (

let uu____10029 = (

let uu____10040 = (FStar_SMTEncoding_Util.mkImp ((guard), (g_typing)))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____10040)))
in (FStar_SMTEncoding_Term.mkForall uu____10028 uu____10029)))
in ((uu____10027), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____10019))
in (uu____10018)::[])
in ((d3), (uu____10015)))
end))
in (match (uu____9991) with
| (aux_decls, typing_corr) -> begin
((aux_decls), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end))))
in (match (uu____9942) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls1 (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))))
end))
end));
)
end)))
end));
)
end))
end))
in (

let uu____10103 = (

let uu____10116 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____10179 uu____10180 -> (match (((uu____10179), (uu____10180))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____10305 = (encode_one_binding env01 gtok ty lb)
in (match (uu____10305) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____10116))
in (match (uu____10103) with
| (decls2, eqns, env01) -> begin
(

let uu____10378 = (

let isDeclFun = (fun uu___376_10393 -> (match (uu___376_10393) with
| FStar_SMTEncoding_Term.DeclFun (uu____10395) -> begin
true
end
| uu____10408 -> begin
false
end))
in (

let uu____10410 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____10410 (FStar_List.partition isDeclFun))))
in (match (uu____10378) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____10450 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___377_10456 -> (match (uu___377_10456) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____10459 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____10467 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.FStar_SMTEncoding_Env.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____10467))))))
in (match (uu____10450) with
| true -> begin
((decls1), (env_decls))
end
| uu____10480 -> begin
(FStar_All.try_with (fun uu___395_10489 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____10503 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___394_10506 -> (match (uu___394_10506) with
| FStar_SMTEncoding_Env.Inner_let_rec -> begin
((decls1), (env_decls))
end)))
end))))))))
end))
end))
end)) (fun uu___390_10518 -> (match (uu___390_10518) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____10527 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____10527 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let nm = (

let uu____10597 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____10597) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____10603 = (encode_sigelt' env se)
in (match (uu____10603) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____10615 = (

let uu____10616 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10616))
in (uu____10615)::[])
end
| uu____10619 -> begin
(

let uu____10620 = (

let uu____10623 = (

let uu____10624 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10624))
in (uu____10623)::g)
in (

let uu____10627 = (

let uu____10630 = (

let uu____10631 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____10631))
in (uu____10630)::[])
in (FStar_List.append uu____10620 uu____10627)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> ((

let uu____10641 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10641) with
| true -> begin
(

let uu____10646 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "@@@Encoding sigelt %s\n" uu____10646))
end
| uu____10649 -> begin
()
end));
(

let is_opaque_to_smt = (fun t -> (

let uu____10658 = (

let uu____10659 = (FStar_Syntax_Subst.compress t)
in uu____10659.FStar_Syntax_Syntax.n)
in (match (uu____10658) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____10664)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____10669 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____10678 = (

let uu____10679 = (FStar_Syntax_Subst.compress t)
in uu____10679.FStar_Syntax_Syntax.n)
in (match (uu____10678) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____10684)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____10689 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____10695) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____10701) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____10713) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____10714) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____10715) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____10728) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____10730 = (

let uu____10732 = (FStar_TypeChecker_Env.is_reifiable_effect env.FStar_SMTEncoding_Env.tcenv ed.FStar_Syntax_Syntax.mname)
in (not (uu____10732)))
in (match (uu____10730) with
| true -> begin
(([]), (env))
end
| uu____10739 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____10761 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____10793 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____10793) with
| (formals, uu____10813) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____10837 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____10837) with
| (aname, atok, env2) -> begin
(

let uu____10863 = (

let uu____10868 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (FStar_SMTEncoding_EncodeTerm.encode_term uu____10868 env2))
in (match (uu____10863) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____10880 = (

let uu____10881 = (

let uu____10893 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10913 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____10893), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____10881))
in (uu____10880)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____10930 = (

let aux = (fun uu____10976 uu____10977 -> (match (((uu____10976), (uu____10977))) with
| ((bv, uu____11021), (env3, acc_sorts, acc)) -> begin
(

let uu____11053 = (FStar_SMTEncoding_Env.gen_term_var env3 bv)
in (match (uu____11053) with
| (xxsym, xx, env4) -> begin
(

let uu____11076 = (

let uu____11079 = (FStar_SMTEncoding_Term.mk_fv ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (uu____11079)::acc_sorts)
in ((env4), (uu____11076), ((xx)::acc)))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____10930) with
| (uu____11111, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____11127 = (

let uu____11135 = (

let uu____11136 = (FStar_Ident.range_of_lid a.FStar_Syntax_Syntax.action_name)
in (

let uu____11137 = (

let uu____11148 = (

let uu____11149 = (

let uu____11154 = (FStar_SMTEncoding_EncodeTerm.mk_Apply tm xs_sorts)
in ((app), (uu____11154)))
in (FStar_SMTEncoding_Util.mkEq uu____11149))
in ((((app)::[])::[]), (xs_sorts), (uu____11148)))
in (FStar_SMTEncoding_Term.mkForall uu____11136 uu____11137)))
in ((uu____11135), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____11127))
in (

let tok_correspondence = (

let tok_term = (

let uu____11169 = (FStar_SMTEncoding_Term.mk_fv ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____11169))
in (

let tok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply tok_term xs_sorts)
in (

let uu____11172 = (

let uu____11180 = (

let uu____11181 = (FStar_Ident.range_of_lid a.FStar_Syntax_Syntax.action_name)
in (

let uu____11182 = (

let uu____11193 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____11193)))
in (FStar_SMTEncoding_Term.mkForall uu____11181 uu____11182)))
in ((uu____11180), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____11172))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____11208 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____11208) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11234, uu____11235) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____11236 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____11236) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____11258, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____11265 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___378_11271 -> (match (uu___378_11271) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____11274) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____11280) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____11283 -> begin
false
end))))
in (not (uu____11265)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____11290 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____11293 = (

let uu____11300 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____11300 env fv t quals))
in (match (uu____11293) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (

let uu____11318 = (FStar_SMTEncoding_Term.mk_fv ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____11318))
in (

let uu____11320 = (

let uu____11321 = (primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv lid tname tsym)
in (FStar_List.append decls uu____11321))
in ((uu____11320), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____11327 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____11327) with
| (uvs, f1) -> begin
(

let env1 = (

let uu___396_11339 = env
in (

let uu____11340 = (FStar_TypeChecker_Env.push_univ_vars env.FStar_SMTEncoding_Env.tcenv uvs)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___396_11339.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___396_11339.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___396_11339.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu____11340; FStar_SMTEncoding_Env.warn = uu___396_11339.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___396_11339.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___396_11339.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___396_11339.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___396_11339.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___396_11339.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___396_11339.FStar_SMTEncoding_Env.encoding_quantifier}))
in (

let f2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::[]) env1.FStar_SMTEncoding_Env.tcenv f1)
in (

let uu____11342 = (FStar_SMTEncoding_EncodeTerm.encode_formula f2 env1)
in (match (uu____11342) with
| (f3, decls) -> begin
(

let g = (

let uu____11356 = (

let uu____11357 = (

let uu____11365 = (

let uu____11366 = (

let uu____11368 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____11368))
in FStar_Pervasives_Native.Some (uu____11366))
in (

let uu____11372 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f3), (uu____11365), (uu____11372))))
in (FStar_SMTEncoding_Util.mkAssume uu____11357))
in (uu____11356)::[])
in (((FStar_List.append decls g)), (env1)))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____11377) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____11391 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____11413 = (

let uu____11416 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____11416.FStar_Syntax_Syntax.fv_name)
in uu____11413.FStar_Syntax_Syntax.v)
in (

let uu____11417 = (

let uu____11419 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.FStar_SMTEncoding_Env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____11419))
in (match (uu____11417) with
| true -> begin
(

let val_decl = (

let uu___397_11451 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___397_11451.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___397_11451.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___397_11451.FStar_Syntax_Syntax.sigattrs})
in (

let uu____11452 = (encode_sigelt' env1 val_decl)
in (match (uu____11452) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____11467 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____11391) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____11488, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____11490; FStar_Syntax_Syntax.lbtyp = uu____11491; FStar_Syntax_Syntax.lbeff = uu____11492; FStar_Syntax_Syntax.lbdef = uu____11493; FStar_Syntax_Syntax.lbattrs = uu____11494; FStar_Syntax_Syntax.lbpos = uu____11495})::[]), uu____11496) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____11515 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____11515) with
| (tname, ttok, env1) -> begin
(

let xx = (FStar_SMTEncoding_Term.mk_fv (("x"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2t_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2t_x)::[])))
in (

let decls = (

let uu____11553 = (

let uu____11556 = (

let uu____11557 = (

let uu____11565 = (

let uu____11566 = (FStar_Syntax_Syntax.range_of_fv b2t1)
in (

let uu____11567 = (

let uu____11578 = (

let uu____11579 = (

let uu____11584 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____11584)))
in (FStar_SMTEncoding_Util.mkEq uu____11579))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____11578)))
in (FStar_SMTEncoding_Term.mkForall uu____11566 uu____11567)))
in ((uu____11565), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____11557))
in (uu____11556)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____11553)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____11622, uu____11623) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___379_11633 -> (match (uu___379_11633) with
| FStar_Syntax_Syntax.Discriminator (uu____11635) -> begin
true
end
| uu____11637 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____11639, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____11651 = (

let uu____11653 = (FStar_List.hd l.FStar_Ident.ns)
in uu____11653.FStar_Ident.idText)
in (Prims.op_Equality uu____11651 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___380_11660 -> (match (uu___380_11660) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____11663 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____11666) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___381_11680 -> (match (uu___381_11680) with
| FStar_Syntax_Syntax.Projector (uu____11682) -> begin
true
end
| uu____11688 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11692 = (FStar_SMTEncoding_Env.try_lookup_free_var env l)
in (match (uu____11692) with
| FStar_Pervasives_Native.Some (uu____11699) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___398_11701 = se
in (

let uu____11702 = (FStar_Ident.range_of_lid l)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____11702; FStar_Syntax_Syntax.sigquals = uu___398_11701.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___398_11701.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___398_11701.FStar_Syntax_Syntax.sigattrs}))
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____11705) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____11720) -> begin
(

let uu____11729 = (encode_sigelts env ses)
in (match (uu____11729) with
| (g, env1) -> begin
(

let uu____11746 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___382_11769 -> (match (uu___382_11769) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____11771; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____11772; FStar_SMTEncoding_Term.assumption_fact_ids = uu____11773}) -> begin
false
end
| uu____11780 -> begin
true
end))))
in (match (uu____11746) with
| (g', inversions) -> begin
(

let uu____11796 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___383_11817 -> (match (uu___383_11817) with
| FStar_SMTEncoding_Term.DeclFun (uu____11819) -> begin
true
end
| uu____11832 -> begin
false
end))))
in (match (uu____11796) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____11849, tps, k, uu____11852, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___384_11871 -> (match (uu___384_11871) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____11875 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____11888 = c
in (match (uu____11888) with
| (name, args, uu____11893, uu____11894, uu____11895) -> begin
(

let uu____11906 = (

let uu____11907 = (

let uu____11919 = (FStar_All.pipe_right args (FStar_List.map (fun uu____11946 -> (match (uu____11946) with
| (uu____11955, sort, uu____11957) -> begin
sort
end))))
in ((name), (uu____11919), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____11907))
in (uu____11906)::[])
end))
end
| uu____11966 -> begin
(

let uu____11968 = (FStar_Ident.range_of_lid t)
in (FStar_SMTEncoding_Term.constructor_to_decl uu____11968 c))
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____11986 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____11994 = (FStar_TypeChecker_Env.try_lookup_lid env.FStar_SMTEncoding_Env.tcenv l)
in (FStar_All.pipe_right uu____11994 FStar_Option.isNone)))))
in (match (uu____11986) with
| true -> begin
[]
end
| uu____12027 -> begin
(

let uu____12029 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12029) with
| (xxsym, xx) -> begin
(

let uu____12042 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____12081 l -> (match (uu____12081) with
| (out, decls) -> begin
(

let uu____12101 = (FStar_TypeChecker_Env.lookup_datacon env.FStar_SMTEncoding_Env.tcenv l)
in (match (uu____12101) with
| (uu____12112, data_t) -> begin
(

let uu____12114 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____12114) with
| (args, res) -> begin
(

let indices = (

let uu____12158 = (

let uu____12159 = (FStar_Syntax_Subst.compress res)
in uu____12159.FStar_Syntax_Syntax.n)
in (match (uu____12158) with
| FStar_Syntax_Syntax.Tm_app (uu____12162, indices) -> begin
indices
end
| uu____12188 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____12218 -> (match (uu____12218) with
| (x, uu____12226) -> begin
(

let uu____12231 = (

let uu____12232 = (

let uu____12240 = (FStar_SMTEncoding_Env.mk_term_projector_name l x)
in ((uu____12240), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____12232))
in (FStar_SMTEncoding_Env.push_term_var env1 x uu____12231))
end)) env))
in (

let uu____12245 = (FStar_SMTEncoding_EncodeTerm.encode_args indices env1)
in (match (uu____12245) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____12267 -> begin
()
end);
(

let eqs = (

let uu____12270 = (FStar_List.map2 (fun v1 a -> (

let uu____12278 = (

let uu____12283 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____12283), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____12278))) vars indices1)
in (FStar_All.pipe_right uu____12270 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____12286 = (

let uu____12287 = (

let uu____12292 = (

let uu____12293 = (

let uu____12298 = (FStar_SMTEncoding_Env.mk_data_tester env1 l xx)
in ((uu____12298), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____12293))
in ((out), (uu____12292)))
in (FStar_SMTEncoding_Util.mkOr uu____12287))
in ((uu____12286), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____12042) with
| (data_ax, decls) -> begin
(

let uu____12311 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____12311) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____12328 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____12328 xx tapp))
end
| uu____12333 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____12335 = (

let uu____12343 = (

let uu____12344 = (FStar_Ident.range_of_lid t)
in (

let uu____12345 = (

let uu____12356 = (

let uu____12357 = (FStar_SMTEncoding_Term.mk_fv ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let uu____12359 = (

let uu____12362 = (FStar_SMTEncoding_Term.mk_fv ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (uu____12362)::vars)
in (FStar_SMTEncoding_Env.add_fuel uu____12357 uu____12359)))
in (

let uu____12364 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____12356), (uu____12364))))
in (FStar_SMTEncoding_Term.mkForall uu____12344 uu____12345)))
in (

let uu____12373 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____12343), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____12373))))
in (FStar_SMTEncoding_Util.mkAssume uu____12335)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____12379 = (

let uu____12384 = (

let uu____12385 = (FStar_Syntax_Subst.compress k)
in uu____12385.FStar_Syntax_Syntax.n)
in (match (uu____12384) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____12420 -> begin
((tps), (k))
end))
in (match (uu____12379) with
| (formals, res) -> begin
(

let uu____12427 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____12427) with
| (formals1, res1) -> begin
(

let uu____12438 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____12438) with
| (vars, guards, env', binder_decls, uu____12463) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____12477 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env t arity)
in (match (uu____12477) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____12507 = (

let uu____12515 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____12515)))
in (FStar_SMTEncoding_Util.mkApp uu____12507))
in (

let uu____12521 = (

let tname_decl = (

let uu____12531 = (

let uu____12532 = (FStar_All.pipe_right vars (FStar_List.map (fun fv -> (

let uu____12551 = (

let uu____12553 = (FStar_SMTEncoding_Term.fv_name fv)
in (Prims.strcat tname uu____12553))
in (

let uu____12555 = (FStar_SMTEncoding_Term.fv_sort fv)
in ((uu____12551), (uu____12555), (false)))))))
in (

let uu____12559 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((tname), (uu____12532), (FStar_SMTEncoding_Term.Term_sort), (uu____12559), (false))))
in (constructor_or_logic_type_decl uu____12531))
in (

let uu____12567 = (match (vars) with
| [] -> begin
(

let uu____12580 = (

let uu____12581 = (

let uu____12584 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_3 -> FStar_Pervasives_Native.Some (_0_3)) uu____12584))
in (FStar_SMTEncoding_Env.push_free_var env1 t arity tname uu____12581))
in (([]), (uu____12580)))
end
| uu____12596 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____12606 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____12606))
in (

let ttok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____12622 = (

let uu____12630 = (

let uu____12631 = (FStar_Ident.range_of_lid t)
in (

let uu____12632 = (

let uu____12648 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____12648)))
in (FStar_SMTEncoding_Term.mkForall' uu____12631 uu____12632)))
in ((uu____12630), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12622))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____12567) with
| (tok_decls, env2) -> begin
(

let uu____12675 = (FStar_Ident.lid_equals t FStar_Parser_Const.lex_t_lid)
in (match (uu____12675) with
| true -> begin
((tok_decls), (env2))
end
| uu____12686 -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end))
end)))
in (match (uu____12521) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____12703 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____12703) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____12725 = (

let uu____12726 = (

let uu____12734 = (

let uu____12735 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____12735))
in ((uu____12734), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12726))
in (uu____12725)::[])
end
| uu____12741 -> begin
[]
end)
in (

let uu____12743 = (

let uu____12746 = (

let uu____12749 = (

let uu____12750 = (

let uu____12758 = (

let uu____12759 = (FStar_Ident.range_of_lid t)
in (

let uu____12760 = (

let uu____12771 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____12771)))
in (FStar_SMTEncoding_Term.mkForall uu____12759 uu____12760)))
in ((uu____12758), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12750))
in (uu____12749)::[])
in (FStar_List.append karr uu____12746))
in (FStar_List.append decls1 uu____12743)))
end))
in (

let aux = (

let uu____12786 = (

let uu____12789 = (inversion_axioms tapp vars)
in (

let uu____12792 = (

let uu____12795 = (

let uu____12796 = (FStar_Ident.range_of_lid t)
in (pretype_axiom uu____12796 env2 tapp vars))
in (uu____12795)::[])
in (FStar_List.append uu____12789 uu____12792)))
in (FStar_List.append kindingAx uu____12786))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____12801, uu____12802, uu____12803, uu____12804, uu____12805) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____12813, t, uu____12815, n_tps, uu____12817) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____12827 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____12827) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____12875 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env d arity)
in (match (uu____12875) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____12903 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____12903) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____12923 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____12923) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____13002 = (FStar_SMTEncoding_Env.mk_term_projector_name d x)
in ((uu____13002), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____13009 = (

let uu____13010 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____13010), (true)))
in (

let uu____13018 = (

let uu____13025 = (FStar_Ident.range_of_lid d)
in (FStar_SMTEncoding_Term.constructor_to_decl uu____13025))
in (FStar_All.pipe_right uu____13009 uu____13018)))
in (

let app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____13037 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____13037) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____13049)::uu____13050 -> begin
(

let ff = (FStar_SMTEncoding_Term.mk_fv (("ty"), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (

let uu____13099 = (

let uu____13100 = (FStar_SMTEncoding_Term.mk_fv ((ddtok), (FStar_SMTEncoding_Term.Term_sort)))
in (uu____13100)::[])
in (FStar_SMTEncoding_EncodeTerm.mk_Apply f uu____13099))
in (

let uu____13126 = (FStar_Ident.range_of_lid d)
in (

let uu____13127 = (

let uu____13138 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____13138)))
in (FStar_SMTEncoding_Term.mkForall uu____13126 uu____13127)))))))
end
| uu____13165 -> begin
tok_typing
end)
in (

let uu____13176 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____13176) with
| (vars', guards', env'', decls_formals, uu____13201) -> begin
(

let uu____13214 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (FStar_SMTEncoding_EncodeTerm.encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____13214) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____13244 -> begin
(

let uu____13253 = (

let uu____13254 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____13254))
in (uu____13253)::[])
end)
in (

let encode_elim = (fun uu____13270 -> (

let uu____13271 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____13271) with
| (head1, args) -> begin
(

let uu____13322 = (

let uu____13323 = (FStar_Syntax_Subst.compress head1)
in uu____13323.FStar_Syntax_Syntax.n)
in (match (uu____13322) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____13335; FStar_Syntax_Syntax.vars = uu____13336}, uu____13337) -> begin
(

let encoded_head_fvb = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____13343 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____13343) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____13406 -> begin
(

let uu____13407 = (

let uu____13413 = (

let uu____13415 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____13415))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____13413)))
in (FStar_Errors.raise_error uu____13407 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____13438 = (

let uu____13440 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____13440))
in (match (uu____13438) with
| true -> begin
(

let uu____13462 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____13462)::[])
end
| uu____13463 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____13465 = (

let uu____13479 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____13536 uu____13537 -> (match (((uu____13536), (uu____13537))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____13648 = (

let uu____13656 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____13656))
in (match (uu____13648) with
| (uu____13670, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____13681 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____13681)::eqns_or_guards)
end
| uu____13684 -> begin
(

let uu____13686 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____13686)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____13479))
in (match (uu____13465) with
| (uu____13707, arg_vars, elim_eqns_or_guards, uu____13710) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p encoded_head_fvb arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____13737 = (

let uu____13745 = (

let uu____13746 = (FStar_Ident.range_of_lid d)
in (

let uu____13747 = (

let uu____13758 = (

let uu____13759 = (FStar_SMTEncoding_Term.mk_fv ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Env.add_fuel uu____13759 (FStar_List.append vars arg_binders)))
in (

let uu____13761 = (

let uu____13762 = (

let uu____13767 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____13767)))
in (FStar_SMTEncoding_Util.mkImp uu____13762))
in ((((ty_pred)::[])::[]), (uu____13758), (uu____13761))))
in (FStar_SMTEncoding_Term.mkForall uu____13746 uu____13747)))
in ((uu____13745), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____13737))
in (

let subterm_ordering = (

let lex_t1 = (

let uu____13782 = (

let uu____13783 = (

let uu____13789 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____13789), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____13783))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____13782))
in (

let uu____13792 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____13792) with
| true -> begin
(

let x = (

let uu____13796 = (

let uu____13802 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____13802), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____13796))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____13807 = (

let uu____13815 = (

let uu____13816 = (FStar_Ident.range_of_lid d)
in (

let uu____13817 = (

let uu____13828 = (

let uu____13833 = (

let uu____13836 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in (uu____13836)::[])
in (uu____13833)::[])
in (

let uu____13841 = (

let uu____13842 = (

let uu____13847 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____13849 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in ((uu____13847), (uu____13849))))
in (FStar_SMTEncoding_Util.mkImp uu____13842))
in ((uu____13828), ((x)::[]), (uu____13841))))
in (FStar_SMTEncoding_Term.mkForall uu____13816 uu____13817)))
in (

let uu____13870 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____13815), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____13870))))
in (FStar_SMTEncoding_Util.mkAssume uu____13807))))
end
| uu____13876 -> begin
(

let prec = (

let uu____13881 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____13902 -> begin
(

let uu____13904 = (

let uu____13905 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 uu____13905 dapp1))
in (uu____13904)::[])
end))))
in (FStar_All.pipe_right uu____13881 FStar_List.flatten))
in (

let uu____13912 = (

let uu____13920 = (

let uu____13921 = (FStar_Ident.range_of_lid d)
in (

let uu____13922 = (

let uu____13933 = (

let uu____13934 = (FStar_SMTEncoding_Term.mk_fv ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Env.add_fuel uu____13934 (FStar_List.append vars arg_binders)))
in (

let uu____13936 = (

let uu____13937 = (

let uu____13942 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____13942)))
in (FStar_SMTEncoding_Util.mkImp uu____13937))
in ((((ty_pred)::[])::[]), (uu____13933), (uu____13936))))
in (FStar_SMTEncoding_Term.mkForall uu____13921 uu____13922)))
in ((uu____13920), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____13912)))
end)))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head_fvb = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____13961 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____13961) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____14024 -> begin
(

let uu____14025 = (

let uu____14031 = (

let uu____14033 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____14033))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____14031)))
in (FStar_Errors.raise_error uu____14025 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____14056 = (

let uu____14058 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____14058))
in (match (uu____14056) with
| true -> begin
(

let uu____14080 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____14080)::[])
end
| uu____14081 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____14083 = (

let uu____14097 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____14154 uu____14155 -> (match (((uu____14154), (uu____14155))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____14266 = (

let uu____14274 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____14274))
in (match (uu____14266) with
| (uu____14288, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____14299 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____14299)::eqns_or_guards)
end
| uu____14302 -> begin
(

let uu____14304 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14304)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____14097))
in (match (uu____14083) with
| (uu____14325, arg_vars, elim_eqns_or_guards, uu____14328) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_fvb fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p encoded_head_fvb arg_vars1)
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____14355 = (

let uu____14363 = (

let uu____14364 = (FStar_Ident.range_of_lid d)
in (

let uu____14365 = (

let uu____14376 = (

let uu____14377 = (FStar_SMTEncoding_Term.mk_fv ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Env.add_fuel uu____14377 (FStar_List.append vars arg_binders)))
in (

let uu____14379 = (

let uu____14380 = (

let uu____14385 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____14385)))
in (FStar_SMTEncoding_Util.mkImp uu____14380))
in ((((ty_pred)::[])::[]), (uu____14376), (uu____14379))))
in (FStar_SMTEncoding_Term.mkForall uu____14364 uu____14365)))
in ((uu____14363), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____14355))
in (

let subterm_ordering = (

let lex_t1 = (

let uu____14400 = (

let uu____14401 = (

let uu____14407 = (FStar_Ident.text_of_lid FStar_Parser_Const.lex_t_lid)
in ((uu____14407), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____14401))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____14400))
in (

let uu____14410 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____14410) with
| true -> begin
(

let x = (

let uu____14414 = (

let uu____14420 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____14420), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_fv uu____14414))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14425 = (

let uu____14433 = (

let uu____14434 = (FStar_Ident.range_of_lid d)
in (

let uu____14435 = (

let uu____14446 = (

let uu____14451 = (

let uu____14454 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in (uu____14454)::[])
in (uu____14451)::[])
in (

let uu____14459 = (

let uu____14460 = (

let uu____14465 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14467 = (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 xtm dapp1)
in ((uu____14465), (uu____14467))))
in (FStar_SMTEncoding_Util.mkImp uu____14460))
in ((uu____14446), ((x)::[]), (uu____14459))))
in (FStar_SMTEncoding_Term.mkForall uu____14434 uu____14435)))
in (

let uu____14488 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____14433), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____14488))))
in (FStar_SMTEncoding_Util.mkAssume uu____14425))))
end
| uu____14494 -> begin
(

let prec = (

let uu____14499 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____14520 -> begin
(

let uu____14522 = (

let uu____14523 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes lex_t1 lex_t1 uu____14523 dapp1))
in (uu____14522)::[])
end))))
in (FStar_All.pipe_right uu____14499 FStar_List.flatten))
in (

let uu____14530 = (

let uu____14538 = (

let uu____14539 = (FStar_Ident.range_of_lid d)
in (

let uu____14540 = (

let uu____14551 = (

let uu____14552 = (FStar_SMTEncoding_Term.mk_fv ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Env.add_fuel uu____14552 (FStar_List.append vars arg_binders)))
in (

let uu____14554 = (

let uu____14555 = (

let uu____14560 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14560)))
in (FStar_SMTEncoding_Util.mkImp uu____14555))
in ((((ty_pred)::[])::[]), (uu____14551), (uu____14554))))
in (FStar_SMTEncoding_Term.mkForall uu____14539 uu____14540)))
in ((uu____14538), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____14530)))
end)))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____14577 -> begin
((

let uu____14579 = (

let uu____14585 = (

let uu____14587 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14589 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14587 uu____14589)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____14585)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____14579));
(([]), ([]));
)
end))
end)))
in (

let uu____14597 = (encode_elim ())
in (match (uu____14597) with
| (decls2, elim) -> begin
(

let g = (

let uu____14623 = (

let uu____14626 = (

let uu____14629 = (

let uu____14632 = (

let uu____14635 = (

let uu____14636 = (

let uu____14648 = (

let uu____14649 = (

let uu____14651 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14651))
in FStar_Pervasives_Native.Some (uu____14649))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14648)))
in FStar_SMTEncoding_Term.DeclFun (uu____14636))
in (uu____14635)::[])
in (

let uu____14658 = (

let uu____14661 = (

let uu____14664 = (

let uu____14667 = (

let uu____14670 = (

let uu____14673 = (FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok))))
in (

let uu____14678 = (

let uu____14681 = (

let uu____14682 = (

let uu____14690 = (

let uu____14691 = (FStar_Ident.range_of_lid d)
in (

let uu____14692 = (

let uu____14703 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14703)))
in (FStar_SMTEncoding_Term.mkForall uu____14691 uu____14692)))
in ((uu____14690), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____14682))
in (

let uu____14716 = (

let uu____14719 = (

let uu____14720 = (

let uu____14728 = (

let uu____14729 = (FStar_Ident.range_of_lid d)
in (

let uu____14730 = (

let uu____14741 = (

let uu____14742 = (FStar_SMTEncoding_Term.mk_fv ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)))
in (FStar_SMTEncoding_Env.add_fuel uu____14742 vars'))
in (

let uu____14744 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14741), (uu____14744))))
in (FStar_SMTEncoding_Term.mkForall uu____14729 uu____14730)))
in ((uu____14728), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____14720))
in (uu____14719)::[])
in (uu____14681)::uu____14716))
in (uu____14673)::uu____14678))
in (FStar_List.append uu____14670 elim))
in (FStar_List.append decls_pred uu____14667))
in (FStar_List.append decls_formals uu____14664))
in (FStar_List.append proxy_fresh uu____14661))
in (FStar_List.append uu____14632 uu____14658)))
in (FStar_List.append decls3 uu____14629))
in (FStar_List.append decls2 uu____14626))
in (FStar_List.append binder_decls uu____14623))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end)))
end)))
end)))
end)));
))
and encode_sigelts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14782 se -> (match (uu____14782) with
| (g, env1) -> begin
(

let uu____14802 = (encode_sigelt env1 se)
in (match (uu____14802) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14870 -> (match (uu____14870) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_Syntax_Syntax.Binding_univ (uu____14907) -> begin
(((i + (Prims.parse_int "1"))), (decls), (env1))
end
| FStar_Syntax_Syntax.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env1.FStar_SMTEncoding_Env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14915 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14915) with
| true -> begin
(

let uu____14920 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14922 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14924 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14920 uu____14922 uu____14924))))
end
| uu____14927 -> begin
()
end));
(

let uu____14929 = (FStar_SMTEncoding_EncodeTerm.encode_term t1 env1)
in (match (uu____14929) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14947 = (

let uu____14955 = (

let uu____14957 = (

let uu____14959 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____14959 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____14957))
in (FStar_SMTEncoding_Env.new_term_constant_from_string env1 x uu____14955))
in (match (uu____14947) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____14979 = (FStar_Options.log_queries ())
in (match (uu____14979) with
| true -> begin
(

let uu____14982 = (

let uu____14984 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14986 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14988 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14984 uu____14986 uu____14988))))
in FStar_Pervasives_Native.Some (uu____14982))
end
| uu____14992 -> begin
FStar_Pervasives_Native.None
end))
in (

let ax = (

let a_name = (Prims.strcat "binder_" xxsym)
in (FStar_SMTEncoding_Util.mkAssume ((t2), (FStar_Pervasives_Native.Some (a_name)), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_Syntax_Syntax.Binding_lid (x, (uu____15012, t)) -> begin
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____15032 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____15032) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end)
end))
in (

let uu____15059 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____15059) with
| (uu____15086, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : FStar_SMTEncoding_Term.error_label Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15139 -> (match (uu____15139) with
| (l, uu____15148, uu____15149) -> begin
(

let uu____15152 = (

let uu____15164 = (FStar_SMTEncoding_Term.fv_name l)
in ((uu____15164), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____15152))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15197 -> (match (uu____15197) with
| (l, uu____15208, uu____15209) -> begin
(

let uu____15212 = (

let uu____15213 = (FStar_SMTEncoding_Term.fv_name l)
in (FStar_All.pipe_left (fun _0_4 -> FStar_SMTEncoding_Term.Echo (_0_4)) uu____15213))
in (

let uu____15216 = (

let uu____15219 = (

let uu____15220 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15220))
in (uu____15219)::[])
in (uu____15212)::uu____15216))
end))))
in ((prefix1), (suffix)))))


let last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> (

let uu____15249 = (

let uu____15252 = (

let uu____15253 = (FStar_Util.psmap_empty ())
in (

let uu____15268 = (FStar_Util.psmap_empty ())
in (

let uu____15271 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____15275 = (

let uu____15277 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____15277 FStar_Ident.string_of_lid))
in {FStar_SMTEncoding_Env.bvar_bindings = uu____15253; FStar_SMTEncoding_Env.fvar_bindings = uu____15268; FStar_SMTEncoding_Env.depth = (Prims.parse_int "0"); FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu____15271; FStar_SMTEncoding_Env.nolabels = false; FStar_SMTEncoding_Env.use_zfuel_name = false; FStar_SMTEncoding_Env.encode_non_total_function_typ = true; FStar_SMTEncoding_Env.current_module_name = uu____15275; FStar_SMTEncoding_Env.encoding_quantifier = false}))))
in (uu____15252)::[])
in (FStar_ST.op_Colon_Equals last_env uu____15249)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Env.env_t = (fun cmn tcenv -> (

let uu____15319 = (FStar_ST.op_Bang last_env)
in (match (uu____15319) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15347 -> begin
(

let uu___399_15350 = e
in (

let uu____15351 = (FStar_Ident.string_of_lid cmn)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___399_15350.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___399_15350.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___399_15350.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = uu___399_15350.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___399_15350.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___399_15350.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___399_15350.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___399_15350.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu____15351; FStar_SMTEncoding_Env.encoding_quantifier = uu___399_15350.FStar_SMTEncoding_Env.encoding_quantifier}))
end)))


let set_env : FStar_SMTEncoding_Env.env_t  ->  unit = (fun env -> (

let uu____15359 = (FStar_ST.op_Bang last_env)
in (match (uu____15359) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15386)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : unit  ->  unit = (fun uu____15418 -> (

let uu____15419 = (FStar_ST.op_Bang last_env)
in (match (uu____15419) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let top = (copy_env hd1)
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1)))
end)))


let pop_env : unit  ->  unit = (fun uu____15479 -> (

let uu____15480 = (FStar_ST.op_Bang last_env)
in (match (uu____15480) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15507)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let snapshot_env : unit  ->  (Prims.int * unit) = (fun uu____15544 -> (FStar_Common.snapshot push_env last_env ()))


let rollback_env : Prims.int FStar_Pervasives_Native.option  ->  unit = (fun depth -> (FStar_Common.rollback pop_env last_env depth))


let init : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[]));
))


let snapshot : Prims.string  ->  (FStar_TypeChecker_Env.solver_depth_t * unit) = (fun msg -> (FStar_Util.atomically (fun uu____15597 -> (

let uu____15598 = (snapshot_env ())
in (match (uu____15598) with
| (env_depth, ()) -> begin
(

let uu____15620 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.snapshot ())
in (match (uu____15620) with
| (varops_depth, ()) -> begin
(

let uu____15642 = (FStar_SMTEncoding_Z3.snapshot msg)
in (match (uu____15642) with
| (z3_depth, ()) -> begin
((((env_depth), (varops_depth), (z3_depth))), (()))
end))
end))
end)))))


let rollback : Prims.string  ->  FStar_TypeChecker_Env.solver_depth_t FStar_Pervasives_Native.option  ->  unit = (fun msg depth -> (FStar_Util.atomically (fun uu____15700 -> (

let uu____15701 = (match (depth) with
| FStar_Pervasives_Native.Some (s1, s2, s3) -> begin
((FStar_Pervasives_Native.Some (s1)), (FStar_Pervasives_Native.Some (s2)), (FStar_Pervasives_Native.Some (s3)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end)
in (match (uu____15701) with
| (env_depth, varops_depth, z3_depth) -> begin
((rollback_env env_depth);
(FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.rollback varops_depth);
(FStar_SMTEncoding_Z3.rollback msg z3_depth);
)
end)))))


let push : Prims.string  ->  unit = (fun msg -> (

let uu____15796 = (snapshot msg)
in ()))


let pop : Prims.string  ->  unit = (fun msg -> (rollback msg FStar_Pervasives_Native.None))


let open_fact_db_tags : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____15842)::uu____15843, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___400_15851 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___400_15851.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___400_15851.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___400_15851.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____15852 -> begin
d
end))


let fact_dbs_for_lid : FStar_SMTEncoding_Env.env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____15872 = (

let uu____15875 = (

let uu____15876 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____15876))
in (

let uu____15877 = (open_fact_db_tags env)
in (uu____15875)::uu____15877))
in (FStar_SMTEncoding_Term.Name (lid))::uu____15872))


let encode_top_level_facts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____15904 = (encode_sigelt env se)
in (match (uu____15904) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____15949 = (FStar_Options.log_queries ())
in (match (uu____15949) with
| true -> begin
(

let uu____15954 = (

let uu____15955 = (

let uu____15957 = (

let uu____15959 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15959 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15957))
in FStar_SMTEncoding_Term.Caption (uu____15955))
in (uu____15954)::decls)
end
| uu____15975 -> begin
decls
end)))
in ((

let uu____15978 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____15978) with
| true -> begin
(

let uu____15981 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____15981))
end
| uu____15984 -> begin
()
end));
(

let env = (

let uu____15987 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____15987 tcenv))
in (

let uu____15988 = (encode_top_level_facts env se)
in (match (uu____15988) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____16002 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____16002));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun tcenv modul -> (

let uu____16016 = ((FStar_Options.lax ()) && (FStar_Options.ml_ish ()))
in (match (uu____16016) with
| true -> begin
()
end
| uu____16019 -> begin
(

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____16027 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____16031 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____16031) with
| true -> begin
(

let uu____16034 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____16034))
end
| uu____16039 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____16080 se -> (match (uu____16080) with
| (g, env2) -> begin
(

let uu____16100 = (encode_top_level_facts env2 se)
in (match (uu____16100) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____16123 = (encode_signature (

let uu___401_16132 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___401_16132.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___401_16132.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___401_16132.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___401_16132.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = false; FStar_SMTEncoding_Env.cache = uu___401_16132.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___401_16132.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___401_16132.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___401_16132.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___401_16132.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___401_16132.FStar_SMTEncoding_Env.encoding_quantifier}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____16123) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____16152 = (FStar_Options.log_queries ())
in (match (uu____16152) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_SMTEncoding_Term.Module (((name), ((FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[]))))))::[])
end
| uu____16164 -> begin
(FStar_SMTEncoding_Term.Module (((name), (decls1))))::[]
end)))
in ((set_env (

let uu___402_16172 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___402_16172.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___402_16172.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___402_16172.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___402_16172.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu___402_16172.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___402_16172.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___402_16172.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___402_16172.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___402_16172.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___402_16172.FStar_SMTEncoding_Env.encoding_quantifier}));
(

let uu____16175 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium)
in (match (uu____16175) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____16179 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
))
end)))


let encode_query : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____16240 = (

let uu____16242 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____16242.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____16240));
(

let env = (

let uu____16244 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____16244 tcenv))
in (

let uu____16245 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Syntax_Syntax.Binding_var (x))::rest -> begin
(

let uu____16284 = (aux rest)
in (match (uu____16284) with
| (out, rest1) -> begin
(

let t = (

let uu____16312 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____16312) with
| FStar_Pervasives_Native.Some (uu____16315) -> begin
(

let uu____16316 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____16316 x.FStar_Syntax_Syntax.sort))
end
| uu____16317 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Env.Eager_unfolding)::(FStar_TypeChecker_Env.Beta)::(FStar_TypeChecker_Env.Simplify)::(FStar_TypeChecker_Env.Primops)::(FStar_TypeChecker_Env.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t)
in (

let uu____16321 = (

let uu____16324 = (FStar_Syntax_Syntax.mk_binder (

let uu___403_16327 = x
in {FStar_Syntax_Syntax.ppname = uu___403_16327.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___403_16327.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____16324)::out)
in ((uu____16321), (rest1)))))
end))
end
| uu____16332 -> begin
(([]), (bindings))
end))
in (

let uu____16339 = (aux tcenv.FStar_TypeChecker_Env.gamma)
in (match (uu____16339) with
| (closing, bindings) -> begin
(

let uu____16366 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____16366), (bindings)))
end)))
in (match (uu____16245) with
| (q1, bindings) -> begin
(

let uu____16397 = (encode_env_bindings env bindings)
in (match (uu____16397) with
| (env_decls, env1) -> begin
((

let uu____16419 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Medium) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____16419) with
| true -> begin
(

let uu____16426 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____16426))
end
| uu____16429 -> begin
()
end));
(

let uu____16431 = (FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1)
in (match (uu____16431) with
| (phi, qdecls) -> begin
(

let uu____16452 = (

let uu____16457 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____16457 phi))
in (match (uu____16452) with
| (labels, phi1) -> begin
(

let uu____16474 = (encode_labels labels)
in (match (uu____16474) with
| (label_prefix, label_suffix) -> begin
(

let caption = (

let uu____16510 = (FStar_Options.log_queries ())
in (match (uu____16510) with
| true -> begin
(

let uu____16515 = (

let uu____16516 = (

let uu____16518 = (FStar_Syntax_Print.term_to_string q1)
in (Prims.strcat "Encoding query formula: " uu____16518))
in FStar_SMTEncoding_Term.Caption (uu____16516))
in (uu____16515)::[])
end
| uu____16521 -> begin
[]
end))
in (

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix (FStar_List.append qdecls caption)))
in (

let qry = (

let uu____16527 = (

let uu____16535 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____16536 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "@query")
in ((uu____16535), (FStar_Pervasives_Native.Some ("query")), (uu____16536))))
in (FStar_SMTEncoding_Util.mkAssume uu____16527))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix))))))
end))
end))
end));
)
end))
end)));
))





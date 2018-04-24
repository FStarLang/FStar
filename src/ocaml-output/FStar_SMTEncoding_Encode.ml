
open Prims
open FStar_Pervasives
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * Prims.int * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__mk
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__is
end))


let prims : prims_t = (

let uu____119 = (FStar_SMTEncoding_Env.fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____119) with
| (asym, a) -> begin
(

let uu____126 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____126) with
| (xsym, x) -> begin
(

let uu____133 = (FStar_SMTEncoding_Env.fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____133) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____187 = (

let uu____198 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____198), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____187))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____224 = (

let uu____231 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____231)))
in (FStar_SMTEncoding_Util.mkApp uu____224))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars)
in (

let uu____244 = (

let uu____247 = (

let uu____250 = (

let uu____253 = (

let uu____254 = (

let uu____261 = (

let uu____262 = (

let uu____273 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____273)))
in (FStar_SMTEncoding_Util.mkForall uu____262))
in ((uu____261), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____254))
in (

let uu____290 = (

let uu____293 = (

let uu____294 = (

let uu____301 = (

let uu____302 = (

let uu____313 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____313)))
in (FStar_SMTEncoding_Util.mkForall uu____302))
in ((uu____301), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____294))
in (uu____293)::[])
in (uu____253)::uu____290))
in (xtok_decl)::uu____250)
in (xname_decl)::uu____247)
in ((xtok1), ((FStar_List.length vars)), (uu____244))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____411 = (

let uu____427 = (

let uu____440 = (

let uu____441 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____441))
in (quant axy uu____440))
in ((FStar_Parser_Const.op_Eq), (uu____427)))
in (

let uu____453 = (

let uu____471 = (

let uu____487 = (

let uu____500 = (

let uu____501 = (

let uu____502 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____502))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____501))
in (quant axy uu____500))
in ((FStar_Parser_Const.op_notEq), (uu____487)))
in (

let uu____514 = (

let uu____532 = (

let uu____548 = (

let uu____561 = (

let uu____562 = (

let uu____563 = (

let uu____568 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____569 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____568), (uu____569))))
in (FStar_SMTEncoding_Util.mkLT uu____563))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____562))
in (quant xy uu____561))
in ((FStar_Parser_Const.op_LT), (uu____548)))
in (

let uu____581 = (

let uu____599 = (

let uu____615 = (

let uu____628 = (

let uu____629 = (

let uu____630 = (

let uu____635 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____636 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____635), (uu____636))))
in (FStar_SMTEncoding_Util.mkLTE uu____630))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____629))
in (quant xy uu____628))
in ((FStar_Parser_Const.op_LTE), (uu____615)))
in (

let uu____648 = (

let uu____666 = (

let uu____682 = (

let uu____695 = (

let uu____696 = (

let uu____697 = (

let uu____702 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____703 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____702), (uu____703))))
in (FStar_SMTEncoding_Util.mkGT uu____697))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____696))
in (quant xy uu____695))
in ((FStar_Parser_Const.op_GT), (uu____682)))
in (

let uu____715 = (

let uu____733 = (

let uu____749 = (

let uu____762 = (

let uu____763 = (

let uu____764 = (

let uu____769 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____770 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____769), (uu____770))))
in (FStar_SMTEncoding_Util.mkGTE uu____764))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____763))
in (quant xy uu____762))
in ((FStar_Parser_Const.op_GTE), (uu____749)))
in (

let uu____782 = (

let uu____800 = (

let uu____816 = (

let uu____829 = (

let uu____830 = (

let uu____831 = (

let uu____836 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____837 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____836), (uu____837))))
in (FStar_SMTEncoding_Util.mkSub uu____831))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____830))
in (quant xy uu____829))
in ((FStar_Parser_Const.op_Subtraction), (uu____816)))
in (

let uu____849 = (

let uu____867 = (

let uu____883 = (

let uu____896 = (

let uu____897 = (

let uu____898 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____898))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____897))
in (quant qx uu____896))
in ((FStar_Parser_Const.op_Minus), (uu____883)))
in (

let uu____910 = (

let uu____928 = (

let uu____944 = (

let uu____957 = (

let uu____958 = (

let uu____959 = (

let uu____964 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____965 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____964), (uu____965))))
in (FStar_SMTEncoding_Util.mkAdd uu____959))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____958))
in (quant xy uu____957))
in ((FStar_Parser_Const.op_Addition), (uu____944)))
in (

let uu____977 = (

let uu____995 = (

let uu____1011 = (

let uu____1024 = (

let uu____1025 = (

let uu____1026 = (

let uu____1031 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1032 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1031), (uu____1032))))
in (FStar_SMTEncoding_Util.mkMul uu____1026))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1025))
in (quant xy uu____1024))
in ((FStar_Parser_Const.op_Multiply), (uu____1011)))
in (

let uu____1044 = (

let uu____1062 = (

let uu____1078 = (

let uu____1091 = (

let uu____1092 = (

let uu____1093 = (

let uu____1098 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1099 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1098), (uu____1099))))
in (FStar_SMTEncoding_Util.mkDiv uu____1093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1092))
in (quant xy uu____1091))
in ((FStar_Parser_Const.op_Division), (uu____1078)))
in (

let uu____1111 = (

let uu____1129 = (

let uu____1145 = (

let uu____1158 = (

let uu____1159 = (

let uu____1160 = (

let uu____1165 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____1166 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____1165), (uu____1166))))
in (FStar_SMTEncoding_Util.mkMod uu____1160))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____1159))
in (quant xy uu____1158))
in ((FStar_Parser_Const.op_Modulus), (uu____1145)))
in (

let uu____1178 = (

let uu____1196 = (

let uu____1212 = (

let uu____1225 = (

let uu____1226 = (

let uu____1227 = (

let uu____1232 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1233 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1232), (uu____1233))))
in (FStar_SMTEncoding_Util.mkAnd uu____1227))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1226))
in (quant xy uu____1225))
in ((FStar_Parser_Const.op_And), (uu____1212)))
in (

let uu____1245 = (

let uu____1263 = (

let uu____1279 = (

let uu____1292 = (

let uu____1293 = (

let uu____1294 = (

let uu____1299 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____1300 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____1299), (uu____1300))))
in (FStar_SMTEncoding_Util.mkOr uu____1294))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1293))
in (quant xy uu____1292))
in ((FStar_Parser_Const.op_Or), (uu____1279)))
in (

let uu____1312 = (

let uu____1330 = (

let uu____1346 = (

let uu____1359 = (

let uu____1360 = (

let uu____1361 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____1361))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____1360))
in (quant qx uu____1359))
in ((FStar_Parser_Const.op_Negation), (uu____1346)))
in (uu____1330)::[])
in (uu____1263)::uu____1312))
in (uu____1196)::uu____1245))
in (uu____1129)::uu____1178))
in (uu____1062)::uu____1111))
in (uu____995)::uu____1044))
in (uu____928)::uu____977))
in (uu____867)::uu____910))
in (uu____800)::uu____849))
in (uu____733)::uu____782))
in (uu____666)::uu____715))
in (uu____599)::uu____648))
in (uu____532)::uu____581))
in (uu____471)::uu____514))
in (uu____411)::uu____453))
in (

let mk1 = (fun l v1 -> (

let uu____1632 = (

let uu____1643 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____1713 -> (match (uu____1713) with
| (l', uu____1729) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____1643 (FStar_Option.map (fun uu____1805 -> (match (uu____1805) with
| (uu____1828, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____1632 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____1919 -> (match (uu____1919) with
| (l', uu____1935) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____1985 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____1985) with
| (xxsym, xx) -> begin
(

let uu____1992 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1992) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let uu____2002 = (

let uu____2009 = (

let uu____2010 = (

let uu____2021 = (

let uu____2022 = (

let uu____2027 = (

let uu____2028 = (

let uu____2033 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____2033)))
in (FStar_SMTEncoding_Util.mkEq uu____2028))
in ((xx_has_type), (uu____2027)))
in (FStar_SMTEncoding_Util.mkImp uu____2022))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____2021)))
in (FStar_SMTEncoding_Util.mkForall uu____2010))
in (

let uu____2058 = (

let uu____2059 = (

let uu____2060 = (

let uu____2061 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____2061))
in (Prims.strcat module_name uu____2060))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____2059))
in ((uu____2009), (FStar_Pervasives_Native.Some ("pretyping")), (uu____2058))))
in (FStar_SMTEncoding_Util.mkAssume uu____2002)))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let uu____2111 = (

let uu____2112 = (

let uu____2119 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____2119), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2112))
in (

let uu____2122 = (

let uu____2125 = (

let uu____2126 = (

let uu____2133 = (

let uu____2134 = (

let uu____2145 = (

let uu____2146 = (

let uu____2151 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____2151)))
in (FStar_SMTEncoding_Util.mkImp uu____2146))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2145)))
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2134))
in ((uu____2133), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2126))
in (uu____2125)::[])
in (uu____2111)::uu____2122))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____2199 = (

let uu____2200 = (

let uu____2207 = (

let uu____2208 = (

let uu____2219 = (

let uu____2224 = (

let uu____2227 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____2227)::[])
in (uu____2224)::[])
in (

let uu____2232 = (

let uu____2233 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____2233 tt))
in ((uu____2219), ((bb)::[]), (uu____2232))))
in (FStar_SMTEncoding_Util.mkForall uu____2208))
in ((uu____2207), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2200))
in (

let uu____2254 = (

let uu____2257 = (

let uu____2258 = (

let uu____2265 = (

let uu____2266 = (

let uu____2277 = (

let uu____2278 = (

let uu____2283 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____2283)))
in (FStar_SMTEncoding_Util.mkImp uu____2278))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2277)))
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2266))
in ((uu____2265), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2258))
in (uu____2257)::[])
in (uu____2199)::uu____2254))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes = (

let uu____2339 = (

let uu____2340 = (

let uu____2347 = (

let uu____2350 = (

let uu____2353 = (

let uu____2356 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____2357 = (

let uu____2360 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____2360)::[])
in (uu____2356)::uu____2357))
in (tt)::uu____2353)
in (tt)::uu____2350)
in (("Prims.Precedes"), (uu____2347)))
in (FStar_SMTEncoding_Util.mkApp uu____2340))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2339))
in (

let precedes_y_x = (

let uu____2364 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____2364))
in (

let uu____2367 = (

let uu____2368 = (

let uu____2375 = (

let uu____2376 = (

let uu____2387 = (

let uu____2392 = (

let uu____2395 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____2395)::[])
in (uu____2392)::[])
in (

let uu____2400 = (

let uu____2401 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____2401 tt))
in ((uu____2387), ((bb)::[]), (uu____2400))))
in (FStar_SMTEncoding_Util.mkForall uu____2376))
in ((uu____2375), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2368))
in (

let uu____2422 = (

let uu____2425 = (

let uu____2426 = (

let uu____2433 = (

let uu____2434 = (

let uu____2445 = (

let uu____2446 = (

let uu____2451 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____2451)))
in (FStar_SMTEncoding_Util.mkImp uu____2446))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2445)))
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2434))
in ((uu____2433), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2426))
in (

let uu____2476 = (

let uu____2479 = (

let uu____2480 = (

let uu____2487 = (

let uu____2488 = (

let uu____2499 = (

let uu____2500 = (

let uu____2505 = (

let uu____2506 = (

let uu____2509 = (

let uu____2512 = (

let uu____2515 = (

let uu____2516 = (

let uu____2521 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____2522 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____2521), (uu____2522))))
in (FStar_SMTEncoding_Util.mkGT uu____2516))
in (

let uu____2523 = (

let uu____2526 = (

let uu____2527 = (

let uu____2532 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____2533 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____2532), (uu____2533))))
in (FStar_SMTEncoding_Util.mkGTE uu____2527))
in (

let uu____2534 = (

let uu____2537 = (

let uu____2538 = (

let uu____2543 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____2544 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____2543), (uu____2544))))
in (FStar_SMTEncoding_Util.mkLT uu____2538))
in (uu____2537)::[])
in (uu____2526)::uu____2534))
in (uu____2515)::uu____2523))
in (typing_pred_y)::uu____2512)
in (typing_pred)::uu____2509)
in (FStar_SMTEncoding_Util.mk_and_l uu____2506))
in ((uu____2505), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____2500))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____2499)))
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2488))
in ((uu____2487), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____2480))
in (uu____2479)::[])
in (uu____2425)::uu____2476))
in (uu____2367)::uu____2422)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____2596 = (

let uu____2597 = (

let uu____2604 = (

let uu____2605 = (

let uu____2616 = (

let uu____2621 = (

let uu____2624 = (FStar_SMTEncoding_Term.boxString b)
in (uu____2624)::[])
in (uu____2621)::[])
in (

let uu____2629 = (

let uu____2630 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____2630 tt))
in ((uu____2616), ((bb)::[]), (uu____2629))))
in (FStar_SMTEncoding_Util.mkForall uu____2605))
in ((uu____2604), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____2597))
in (

let uu____2651 = (

let uu____2654 = (

let uu____2655 = (

let uu____2662 = (

let uu____2663 = (

let uu____2674 = (

let uu____2675 = (

let uu____2680 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____2680)))
in (FStar_SMTEncoding_Util.mkImp uu____2675))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____2674)))
in (FStar_SMTEncoding_EncodeTerm.mkForall_fuel uu____2663))
in ((uu____2662), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____2655))
in (uu____2654)::[])
in (uu____2596)::uu____2651))))))
in (

let mk_eq2_interp = (fun nm env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
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

let uu____2750 = (

let uu____2751 = (

let uu____2758 = (

let uu____2759 = (

let uu____2770 = (

let uu____2771 = (

let uu____2776 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____2776), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____2771))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____2770)))
in (FStar_SMTEncoding_Util.mkForall uu____2759))
in ((uu____2758), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), (nm)))
in (FStar_SMTEncoding_Util.mkAssume uu____2751))
in (uu____2750)::[]))))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
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

let uu____2855 = (

let uu____2856 = (

let uu____2863 = (

let uu____2864 = (

let uu____2875 = (

let uu____2876 = (

let uu____2881 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____2881), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____2876))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____2875)))
in (FStar_SMTEncoding_Util.mkForall uu____2864))
in ((uu____2863), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____2856))
in (uu____2855)::[]))))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____2937 = (

let uu____2938 = (

let uu____2945 = (

let uu____2946 = (FStar_SMTEncoding_Term.mk_Range_const ())
in (FStar_SMTEncoding_Term.mk_HasTypeZ uu____2946 range_ty))
in (

let uu____2947 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "typing_range_const")
in ((uu____2945), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____2947))))
in (FStar_SMTEncoding_Util.mkAssume uu____2938))
in (uu____2937)::[])))
in (

let mk_inversion_axiom = (fun env inversion tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
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

let uu____2987 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____2987 x1 t))
in (

let uu____2988 = (

let uu____2999 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____2999)))
in (FStar_SMTEncoding_Util.mkForall uu____2988))))
in (

let uu____3022 = (

let uu____3023 = (

let uu____3030 = (

let uu____3031 = (

let uu____3042 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____3042)))
in (FStar_SMTEncoding_Util.mkForall uu____3031))
in ((uu____3030), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____3023))
in (uu____3022)::[])))))))))
in (

let mk_with_type_axiom = (fun env with_type1 tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let ee = (("e"), (FStar_SMTEncoding_Term.Term_sort))
in (

let e = (FStar_SMTEncoding_Util.mkFreeV ee)
in (

let with_type_t_e = (FStar_SMTEncoding_Util.mkApp ((with_type1), ((t)::(e)::[])))
in (

let uu____3098 = (

let uu____3099 = (

let uu____3106 = (

let uu____3107 = (

let uu____3122 = (

let uu____3123 = (

let uu____3128 = (FStar_SMTEncoding_Util.mkEq ((with_type_t_e), (e)))
in (

let uu____3129 = (FStar_SMTEncoding_Term.mk_HasType with_type_t_e t)
in ((uu____3128), (uu____3129))))
in (FStar_SMTEncoding_Util.mkAnd uu____3123))
in ((((with_type_t_e)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((tt1)::(ee)::[]), (uu____3122)))
in (FStar_SMTEncoding_Util.mkForall' uu____3107))
in ((uu____3106), (FStar_Pervasives_Native.Some ("with_type primitive axiom")), ("@with_type_primitive_axiom")))
in (FStar_SMTEncoding_Util.mkAssume uu____3099))
in (uu____3098)::[])))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.t_eq2_lid), ((mk_eq2_interp "t_eq2-interp"))))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::(((FStar_Parser_Const.with_type_lid), (mk_with_type_axiom)))::[]
in (fun env t s tt -> (

let uu____3391 = (FStar_Util.find_opt (fun uu____3423 -> (match (uu____3423) with
| (l, uu____3435) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____3391) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____3469, f) -> begin
(f env s tt)
end)))))))))))))))))


let encode_smt_lemma : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____3520 = (FStar_SMTEncoding_EncodeTerm.encode_function_type_as_formula t env)
in (match (uu____3520) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____3572 = (((

let uu____3575 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.FStar_SMTEncoding_Env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____3575)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____3572) with
| true -> begin
(

let arg_sorts = (

let uu____3585 = (

let uu____3586 = (FStar_Syntax_Subst.compress t_norm)
in uu____3586.FStar_Syntax_Syntax.n)
in (match (uu____3585) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____3592) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____3622 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____3627 -> begin
[]
end))
in (

let arity = (FStar_List.length arg_sorts)
in (

let uu____3629 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____3629) with
| (vname, vtok, env1) -> begin
(

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1))))
end))))
end
| uu____3661 -> begin
(

let uu____3662 = (prims.is lid)
in (match (uu____3662) with
| true -> begin
(

let vname = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar lid)
in (

let uu____3670 = (prims.mk lid vname)
in (match (uu____3670) with
| (tok, arity, definition) -> begin
(

let env1 = (FStar_SMTEncoding_Env.push_free_var env lid arity vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____3695 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____3697 = (

let uu____3708 = (FStar_SMTEncoding_EncodeTerm.curried_arrow_formals_comp t_norm)
in (match (uu____3708) with
| (args, comp) -> begin
(

let comp1 = (

let uu____3726 = (FStar_TypeChecker_Env.is_reifiable_comp env.FStar_SMTEncoding_Env.tcenv comp)
in (match (uu____3726) with
| true -> begin
(

let uu____3727 = (FStar_TypeChecker_Env.reify_comp (

let uu___85_3730 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___85_3730.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___85_3730.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___85_3730.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___85_3730.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___85_3730.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___85_3730.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___85_3730.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___85_3730.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___85_3730.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___85_3730.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___85_3730.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___85_3730.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___85_3730.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___85_3730.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___85_3730.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___85_3730.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___85_3730.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___85_3730.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___85_3730.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___85_3730.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___85_3730.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___85_3730.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___85_3730.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___85_3730.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___85_3730.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___85_3730.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___85_3730.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___85_3730.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___85_3730.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___85_3730.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___85_3730.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___85_3730.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___85_3730.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___85_3730.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___85_3730.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___85_3730.FStar_TypeChecker_Env.dep_graph}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____3727))
end
| uu____3731 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____3742 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.FStar_SMTEncoding_Env.tcenv comp1)
in ((args), (uu____3742)))
end
| uu____3755 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____3697) with
| (formals, (pre_opt, res_t)) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____3792 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid arity)
in (match (uu____3792) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____3817 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___74_3867 -> (match (uu___74_3867) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____3871 = (FStar_Util.prefix vars)
in (match (uu____3871) with
| (uu____3892, (xxsym, uu____3894)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____3912 = (

let uu____3913 = (

let uu____3920 = (

let uu____3921 = (

let uu____3932 = (

let uu____3933 = (

let uu____3938 = (

let uu____3939 = (FStar_SMTEncoding_Term.mk_tester (FStar_SMTEncoding_Env.escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____3939))
in ((vapp), (uu____3938)))
in (FStar_SMTEncoding_Util.mkEq uu____3933))
in ((((vapp)::[])::[]), (vars), (uu____3932)))
in (FStar_SMTEncoding_Util.mkForall uu____3921))
in ((uu____3920), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (FStar_SMTEncoding_Env.escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____3913))
in (uu____3912)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____3958 = (FStar_Util.prefix vars)
in (match (uu____3958) with
| (uu____3979, (xxsym, uu____3981)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (FStar_SMTEncoding_Env.mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____4004 = (

let uu____4005 = (

let uu____4012 = (

let uu____4013 = (

let uu____4024 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____4024)))
in (FStar_SMTEncoding_Util.mkForall uu____4013))
in ((uu____4012), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____4005))
in (uu____4004)::[])))))
end))
end
| uu____4041 -> begin
[]
end)))))
in (

let uu____4042 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____4042) with
| (vars, guards, env', decls1, uu____4069) -> begin
(

let uu____4082 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4091 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4091), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____4093 = (FStar_SMTEncoding_EncodeTerm.encode_formula p env')
in (match (uu____4093) with
| (g, ds) -> begin
(

let uu____4104 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____4104), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____4082) with
| (guard, decls11) -> begin
(

let vtok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____4117 = (

let uu____4124 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____4124)))
in (FStar_SMTEncoding_Util.mkApp uu____4117))
in (

let uu____4133 = (

let vname_decl = (

let uu____4141 = (

let uu____4152 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____4162 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____4152), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____4141))
in (

let uu____4171 = (

let env2 = (

let uu___86_4177 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___86_4177.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___86_4177.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___86_4177.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___86_4177.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___86_4177.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___86_4177.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___86_4177.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___86_4177.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___86_4177.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___86_4177.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let uu____4178 = (

let uu____4179 = (FStar_SMTEncoding_EncodeTerm.head_normal env2 tt)
in (not (uu____4179)))
in (match (uu____4178) with
| true -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____4184 -> begin
(FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____4171) with
| (tok_typing, decls2) -> begin
(

let uu____4193 = (match (formals) with
| [] -> begin
(

let tok_typing1 = (FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
in (

let uu____4213 = (

let uu____4214 = (

let uu____4217 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_18 -> FStar_Pervasives_Native.Some (_0_18)) uu____4217))
in (FStar_SMTEncoding_Env.push_free_var env1 lid arity vname uu____4214))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____4213))))
end
| uu____4226 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_app_0 = (

let uu____4233 = (

let uu____4240 = (FStar_List.hd vars)
in (uu____4240)::[])
in (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm uu____4233))
in (

let name_tok_corr_formula = (fun pat -> (

let uu____4247 = (

let uu____4258 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((pat)::[])::[]), (vars), (uu____4258)))
in (FStar_SMTEncoding_Util.mkForall uu____4247)))
in (

let name_tok_corr = (

let uu____4270 = (

let uu____4277 = (name_tok_corr_formula vtok_app)
in ((uu____4277), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____4270))
in (

let tok_typing1 = (

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (FStar_SMTEncoding_EncodeTerm.mk_Apply vtok_tm ((ff)::[]))
in (

let vtok_app_r = (FStar_SMTEncoding_EncodeTerm.mk_Apply f ((((vtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let guarded_tok_typing = (

let uu____4306 = (

let uu____4317 = (

let uu____4318 = (

let uu____4323 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in (

let uu____4324 = (name_tok_corr_formula vapp)
in ((uu____4323), (uu____4324))))
in (FStar_SMTEncoding_Util.mkAnd uu____4318))
in ((((vtok_app_r)::[])::[]), ((ff)::[]), (uu____4317)))
in (FStar_SMTEncoding_Util.mkForall uu____4306))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
in (((FStar_List.append decls2 ((vtok_decl)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))))
end)
in (match (uu____4193) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end))
end)))
in (match (uu____4133) with
| (decls2, env2) -> begin
(

let uu____4377 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____4385 = (FStar_SMTEncoding_EncodeTerm.encode_term res_t1 env')
in (match (uu____4385) with
| (encoded_res_t, decls) -> begin
(

let uu____4398 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____4398), (decls)))
end)))
in (match (uu____4377) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____4409 = (

let uu____4416 = (

let uu____4417 = (

let uu____4428 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____4428)))
in (FStar_SMTEncoding_Util.mkForall uu____4417))
in ((uu____4416), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____4409))
in (

let freshness = (

let uu____4444 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____4444) with
| true -> begin
(

let uu____4449 = (

let uu____4450 = (

let uu____4461 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____4472 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((vname), (uu____4461), (FStar_SMTEncoding_Term.Term_sort), (uu____4472))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____4450))
in (

let uu____4475 = (

let uu____4478 = (pretype_axiom env2 vapp vars)
in (uu____4478)::[])
in (uu____4449)::uu____4475))
end
| uu____4479 -> begin
[]
end))
in (

let g = (

let uu____4483 = (

let uu____4486 = (

let uu____4489 = (

let uu____4492 = (

let uu____4495 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____4495)
in (FStar_List.append freshness uu____4492))
in (FStar_List.append decls3 uu____4489))
in (FStar_List.append decls2 uu____4486))
in (FStar_List.append decls11 uu____4483))
in ((g), (env2)))))
end))
end))))
end))
end))))
end)))
end)))
end))
end))))


let declare_top_level_let : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Env.fvar_binding * FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env x t t_norm -> (

let uu____4528 = (FStar_SMTEncoding_Env.lookup_fvar_binding env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____4528) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4539 = (encode_free_var false env x t t_norm [])
in (match (uu____4539) with
| (decls, env1) -> begin
(

let fvb = (FStar_SMTEncoding_Env.lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in ((fvb), (decls), (env1)))
end))
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((fvb), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun uninterpreted env lid t quals -> (

let tt = (FStar_SMTEncoding_EncodeTerm.norm env t)
in (

let uu____4602 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____4602) with
| (decls, env1) -> begin
(

let uu____4621 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____4621) with
| true -> begin
(

let uu____4628 = (

let uu____4631 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____4631))
in ((uu____4628), (env1)))
end
| uu____4636 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____4689 lb -> (match (uu____4689) with
| (decls, env1) -> begin
(

let uu____4709 = (

let uu____4716 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____4716 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____4709) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____4739 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____4739) with
| (hd1, args) -> begin
(

let uu____4776 = (

let uu____4777 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4777.FStar_Syntax_Syntax.n)
in (match (uu____4776) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____4781, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____4800 -> begin
false
end))
end))))

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____4806 -> begin
false
end))


let encode_top_level_let : FStar_SMTEncoding_Env.env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env uu____4834 quals -> (match (uu____4834) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____4918 = (FStar_Util.first_N nbinders formals)
in (match (uu____4918) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____4999 uu____5000 -> (match (((uu____4999), (uu____5000))) with
| ((formal, uu____5018), (binder, uu____5020)) -> begin
(

let uu____5029 = (

let uu____5036 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____5036)))
in FStar_Syntax_Syntax.NT (uu____5029))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____5044 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____5075 -> (match (uu____5075) with
| (x, i) -> begin
(

let uu____5086 = (

let uu___87_5087 = x
in (

let uu____5088 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___87_5087.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___87_5087.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____5088}))
in ((uu____5086), (i)))
end))))
in (FStar_All.pipe_right uu____5044 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____5106 = (

let uu____5111 = (FStar_Syntax_Subst.compress body)
in (

let uu____5112 = (

let uu____5113 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____5113))
in (FStar_Syntax_Syntax.extend_app_n uu____5111 uu____5112)))
in (uu____5106 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____5182 = (FStar_TypeChecker_Env.is_reifiable_comp env.FStar_SMTEncoding_Env.tcenv c)
in (match (uu____5182) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___88_5185 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___88_5185.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___88_5185.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___88_5185.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___88_5185.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___88_5185.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___88_5185.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___88_5185.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___88_5185.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___88_5185.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___88_5185.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___88_5185.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___88_5185.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___88_5185.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___88_5185.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___88_5185.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___88_5185.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___88_5185.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___88_5185.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___88_5185.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___88_5185.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___88_5185.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___88_5185.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___88_5185.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___88_5185.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___88_5185.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___88_5185.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___88_5185.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___88_5185.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___88_5185.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___88_5185.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___88_5185.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___88_5185.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___88_5185.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___88_5185.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___88_5185.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___88_5185.FStar_TypeChecker_Env.dep_graph}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____5186 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____5222 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____5222) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____5286)::uu____5287 -> begin
(

let uu____5302 = (

let uu____5303 = (

let uu____5306 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____5306))
in uu____5303.FStar_Syntax_Syntax.n)
in (match (uu____5302) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____5349 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____5349) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____5391 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____5391) with
| true -> begin
(

let uu____5426 = (FStar_Util.first_N nformals binders)
in (match (uu____5426) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____5520 uu____5521 -> (match (((uu____5520), (uu____5521))) with
| ((x, uu____5539), (b, uu____5541)) -> begin
(

let uu____5550 = (

let uu____5557 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____5557)))
in FStar_Syntax_Syntax.NT (uu____5550))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____5559 = (

let uu____5580 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____5580)))
in ((uu____5559), (false)))))
end))
end
| uu____5613 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____5648 = (eta_expand1 binders formals1 body tres)
in (match (uu____5648) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____5727 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____5737) -> begin
(

let uu____5742 = (

let uu____5763 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____5763))
in ((uu____5742), (true)))
end
| uu____5828 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____5830 -> begin
(

let uu____5831 = (

let uu____5832 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____5833 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____5832 uu____5833)))
in (failwith uu____5831))
end))
end
| uu____5858 -> begin
(

let rec aux' = (fun t_norm2 -> (

let uu____5885 = (

let uu____5886 = (FStar_Syntax_Subst.compress t_norm2)
in uu____5886.FStar_Syntax_Syntax.n)
in (match (uu____5885) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____5927 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____5927) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____5955 = (eta_expand1 [] formals1 e tres)
in (match (uu____5955) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____6035) -> begin
(aux' bv.FStar_Syntax_Syntax.sort)
end
| uu____6040 -> begin
(((([]), (e), ([]), (t_norm2))), (false))
end)))
in (aux' t_norm1))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___90_6089 -> (match (()) with
| () -> begin
(

let uu____6096 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____6096) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____6107 -> begin
(

let uu____6108 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____6171 lb -> (match (uu____6171) with
| (toks, typs, decls, env1) -> begin
((

let uu____6226 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____6226) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____6227 -> begin
()
end));
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____6229 = (

let uu____6238 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____6238 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____6229) with
| (tok, decl, env2) -> begin
(((tok)::toks), ((t_norm)::typs), ((decl)::decls), (env2))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____6108) with
| (toks, typs, decls, env1) -> begin
(

let toks_fvbs = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun rng curry fvb vars -> (

let mk_fv = (fun uu____6363 -> (match ((Prims.op_Equality fvb.FStar_SMTEncoding_Env.smt_arity (Prims.parse_int "0"))) with
| true -> begin
(FStar_SMTEncoding_Util.mkFreeV ((fvb.FStar_SMTEncoding_Env.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____6364 -> begin
(FStar_SMTEncoding_EncodeTerm.raise_arity_mismatch fvb.FStar_SMTEncoding_Env.smt_id fvb.FStar_SMTEncoding_Env.smt_arity (Prims.parse_int "0") rng)
end))
in (match (vars) with
| [] -> begin
(mk_fv ())
end
| uu____6369 -> begin
(match (curry) with
| true -> begin
(match (fvb.FStar_SMTEncoding_Env.smt_token) with
| FStar_Pervasives_Native.Some (ftok) -> begin
(FStar_SMTEncoding_EncodeTerm.mk_Apply ftok vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6377 = (mk_fv ())
in (FStar_SMTEncoding_EncodeTerm.mk_Apply uu____6377 vars))
end)
end
| uu____6378 -> begin
(

let uu____6379 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (FStar_SMTEncoding_EncodeTerm.maybe_curry_app rng (FStar_SMTEncoding_Term.Var (fvb.FStar_SMTEncoding_Env.smt_id)) fvb.FStar_SMTEncoding_Env.smt_arity uu____6379))
end)
end)))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks1 env2 -> (match (((bindings1), (typs2), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6439; FStar_Syntax_Syntax.lbeff = uu____6440; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____6442; FStar_Syntax_Syntax.lbpos = uu____6443})::[], (t_norm)::[], (fvb)::[]) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let uu____6467 = (

let uu____6474 = (FStar_TypeChecker_Env.open_universes_in env2.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____6474) with
| (tcenv', uu____6492, e_t) -> begin
(

let uu____6498 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____6509 -> begin
(failwith "Impossible")
end)
in (match (uu____6498) with
| (e1, t_norm1) -> begin
(((

let uu___91_6525 = env2
in {FStar_SMTEncoding_Env.bvar_bindings = uu___91_6525.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___91_6525.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___91_6525.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___91_6525.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___91_6525.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___91_6525.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___91_6525.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___91_6525.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___91_6525.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___91_6525.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____6467) with
| (env', e1, t_norm1) -> begin
(

let uu____6535 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____6535) with
| ((binders, body, uu____6556, t_body), curry) -> begin
(

let is_prop = (

let uu____6568 = (

let uu____6569 = (FStar_Syntax_Subst.compress t_body)
in uu____6569.FStar_Syntax_Syntax.n)
in (match (uu____6568) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.prop_lid)
end
| uu____6573 -> begin
false
end))
in (

let is_lbname_squash = (match (lbn) with
| FStar_Util.Inl (uu____6575) -> begin
false
end
| FStar_Util.Inr (fv) -> begin
((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid))
end)
in ((

let uu____6578 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6578) with
| true -> begin
(

let uu____6579 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____6580 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____6579 uu____6580)))
end
| uu____6581 -> begin
()
end));
(

let uu____6582 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____6582) with
| (vars, guards, env'1, binder_decls, uu____6609) -> begin
(

let body1 = (

let uu____6623 = (FStar_TypeChecker_Env.is_reifiable_function env'1.FStar_SMTEncoding_Env.tcenv t_norm1)
in (match (uu____6623) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.FStar_SMTEncoding_Env.tcenv body)
end
| uu____6624 -> begin
(FStar_Syntax_Util.ascribe body ((FStar_Util.Inl (t_body)), (FStar_Pervasives_Native.None)))
end))
in (

let app = (

let uu____6640 = (FStar_Syntax_Util.range_of_lbname lbn)
in (mk_app1 uu____6640 curry fvb vars))
in (

let uu____6641 = (FStar_SMTEncoding_EncodeTerm.encode_term body1 env'1)
in (match (uu____6641) with
| (body', decls2) -> begin
(

let eqn = (

let uu____6655 = (

let uu____6662 = (

let uu____6663 = (

let uu____6674 = (FStar_SMTEncoding_Util.mkEq ((app), (body')))
in ((((app)::[])::[]), (vars), (uu____6674)))
in (FStar_SMTEncoding_Util.mkForall uu____6663))
in (

let uu____6685 = (

let uu____6688 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____6688))
in ((uu____6662), (uu____6685), ((Prims.strcat "equation_" fvb.FStar_SMTEncoding_Env.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6655))
in (

let eqns = (match ((is_prop && (not (is_lbname_squash)))) with
| true -> begin
((

let uu____6697 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6697) with
| true -> begin
(

let uu____6698 = (FStar_Syntax_Print.lbname_to_string lbn)
in (FStar_Util.print1 "is_prop %s\n" uu____6698))
end
| uu____6699 -> begin
()
end));
(

let uu____6700 = (

let uu____6709 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____6710 = (FStar_SMTEncoding_EncodeTerm.encode_formula body1 env'1)
in ((uu____6709), (uu____6710))))
in (match (uu____6700) with
| (app1, (body'1, decls21)) -> begin
(

let eqn1 = (

let uu____6729 = (

let uu____6736 = (

let uu____6737 = (

let uu____6748 = (FStar_SMTEncoding_Util.mkEq ((app1), (body'1)))
in ((((app1)::[])::[]), (vars), (uu____6748)))
in (FStar_SMTEncoding_Util.mkForall uu____6737))
in (

let uu____6759 = (

let uu____6762 = (FStar_Util.format1 "Valid Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____6762))
in ((uu____6736), (uu____6759), ((Prims.strcat "valid_equation_" fvb.FStar_SMTEncoding_Env.smt_id)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6729))
in (eqn1)::[])
end));
)
end
| uu____6765 -> begin
[]
end)
in (

let uu____6766 = (

let uu____6769 = (

let uu____6772 = (

let uu____6775 = (

let uu____6778 = (

let uu____6781 = (primitive_type_axioms env2.FStar_SMTEncoding_Env.tcenv flid fvb.FStar_SMTEncoding_Env.smt_id app)
in (FStar_List.append eqns uu____6781))
in (FStar_List.append ((eqn)::[]) uu____6778))
in (FStar_List.append decls2 uu____6775))
in (FStar_List.append binder_decls uu____6772))
in (FStar_List.append decls1 uu____6769))
in ((uu____6766), (env2)))))
end))))
end));
)))
end))
end)))
end
| uu____6786 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks1 env2 -> (

let fuel = (

let uu____6849 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "fuel")
in ((uu____6849), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____6852 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____6899 fvb -> (match (uu____6899) with
| (gtoks, env3) -> begin
(

let flid = fvb.FStar_SMTEncoding_Env.fvar_lid
in (

let g = (

let uu____6945 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____6945))
in (

let gtok = (

let uu____6947 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.new_fvar uu____6947))
in (

let env4 = (

let uu____6949 = (

let uu____6952 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_19 -> FStar_Pervasives_Native.Some (_0_19)) uu____6952))
in (FStar_SMTEncoding_Env.push_free_var env3 flid fvb.FStar_SMTEncoding_Env.smt_arity gtok uu____6949))
in (((((fvb), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____6852) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____7060 t_norm uu____7062 -> (match (((uu____7060), (uu____7062))) with
| ((fvb, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____7092; FStar_Syntax_Syntax.lbeff = uu____7093; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = uu____7095; FStar_Syntax_Syntax.lbpos = uu____7096}) -> begin
(

let uu____7117 = (

let uu____7124 = (FStar_TypeChecker_Env.open_universes_in env3.FStar_SMTEncoding_Env.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____7124) with
| (tcenv', uu____7146, e_t) -> begin
(

let uu____7152 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____7163 -> begin
(failwith "Impossible")
end)
in (match (uu____7152) with
| (e1, t_norm1) -> begin
(((

let uu___92_7179 = env3
in {FStar_SMTEncoding_Env.bvar_bindings = uu___92_7179.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___92_7179.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___92_7179.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv'; FStar_SMTEncoding_Env.warn = uu___92_7179.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___92_7179.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___92_7179.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___92_7179.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___92_7179.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___92_7179.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___92_7179.FStar_SMTEncoding_Env.encoding_quantifier})), (e1), (t_norm1))
end))
end))
in (match (uu____7117) with
| (env', e1, t_norm1) -> begin
((

let uu____7194 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____7194) with
| true -> begin
(

let uu____7195 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____7196 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____7197 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____7195 uu____7196 uu____7197))))
end
| uu____7198 -> begin
()
end));
(

let uu____7199 = (destruct_bound_function fvb.FStar_SMTEncoding_Env.fvar_lid t_norm1 e1)
in (match (uu____7199) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____7236 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____7236) with
| true -> begin
(

let uu____7237 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____7238 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____7239 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____7240 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____7237 uu____7238 uu____7239 uu____7240)))))
end
| uu____7241 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____7243 -> begin
()
end);
(

let uu____7244 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____7244) with
| (vars, guards, env'1, binder_decls, uu____7275) -> begin
(

let decl_g = (

let uu____7289 = (

let uu____7300 = (

let uu____7303 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____7303)
in ((g), (uu____7300), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____7289))
in (

let env02 = (FStar_SMTEncoding_Env.push_zfuel_name env01 fvb.FStar_SMTEncoding_Env.fvar_lid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____7328 = (

let uu____7335 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((fvb.FStar_SMTEncoding_Env.smt_id), (uu____7335)))
in (FStar_SMTEncoding_Util.mkApp uu____7328))
in (

let gsapp = (

let uu____7345 = (

let uu____7352 = (

let uu____7355 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____7355)::vars_tm)
in ((g), (uu____7352)))
in (FStar_SMTEncoding_Util.mkApp uu____7345))
in (

let gmax = (

let uu____7361 = (

let uu____7368 = (

let uu____7371 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____7371)::vars_tm)
in ((g), (uu____7368)))
in (FStar_SMTEncoding_Util.mkApp uu____7361))
in (

let body1 = (

let uu____7377 = (FStar_TypeChecker_Env.is_reifiable_function env'1.FStar_SMTEncoding_Env.tcenv t_norm1)
in (match (uu____7377) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.FStar_SMTEncoding_Env.tcenv body)
end
| uu____7378 -> begin
body
end))
in (

let uu____7379 = (FStar_SMTEncoding_EncodeTerm.encode_term body1 env'1)
in (match (uu____7379) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____7397 = (

let uu____7404 = (

let uu____7405 = (

let uu____7420 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____7420)))
in (FStar_SMTEncoding_Util.mkForall' uu____7405))
in (

let uu____7441 = (

let uu____7444 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" fvb.FStar_SMTEncoding_Env.fvar_lid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____7444))
in ((uu____7404), (uu____7441), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7397))
in (

let eqn_f = (

let uu____7448 = (

let uu____7455 = (

let uu____7456 = (

let uu____7467 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____7467)))
in (FStar_SMTEncoding_Util.mkForall uu____7456))
in ((uu____7455), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____7448))
in (

let eqn_g' = (

let uu____7481 = (

let uu____7488 = (

let uu____7489 = (

let uu____7500 = (

let uu____7501 = (

let uu____7506 = (

let uu____7507 = (

let uu____7514 = (

let uu____7517 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____7517)::vars_tm)
in ((g), (uu____7514)))
in (FStar_SMTEncoding_Util.mkApp uu____7507))
in ((gsapp), (uu____7506)))
in (FStar_SMTEncoding_Util.mkEq uu____7501))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____7500)))
in (FStar_SMTEncoding_Util.mkForall uu____7489))
in ((uu____7488), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____7481))
in (

let uu____7540 = (

let uu____7549 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____7549) with
| (vars1, v_guards, env4, binder_decls1, uu____7578) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____7603 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_EncodeTerm.mk_Apply uu____7603 ((fuel)::vars1)))
in (

let uu____7608 = (

let uu____7615 = (

let uu____7616 = (

let uu____7627 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____7627)))
in (FStar_SMTEncoding_Util.mkForall uu____7616))
in ((uu____7615), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____7608)))
in (

let uu____7648 = (

let uu____7655 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____7655) with
| (g_typing, d3) -> begin
(

let uu____7668 = (

let uu____7671 = (

let uu____7672 = (

let uu____7679 = (

let uu____7680 = (

let uu____7691 = (

let uu____7692 = (

let uu____7697 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____7697), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____7692))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____7691)))
in (FStar_SMTEncoding_Util.mkForall uu____7680))
in ((uu____7679), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____7672))
in (uu____7671)::[])
in ((d3), (uu____7668)))
end))
in (match (uu____7648) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____7540) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))
end));
)
end));
)
end))
end))
in (

let uu____7762 = (

let uu____7775 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____7836 uu____7837 -> (match (((uu____7836), (uu____7837))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____7962 = (encode_one_binding env01 gtok ty lb)
in (match (uu____7962) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____7775))
in (match (uu____7762) with
| (decls2, eqns, env01) -> begin
(

let uu____8035 = (

let isDeclFun = (fun uu___75_8049 -> (match (uu___75_8049) with
| FStar_SMTEncoding_Term.DeclFun (uu____8050) -> begin
true
end
| uu____8061 -> begin
false
end))
in (

let uu____8062 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____8062 (FStar_List.partition isDeclFun))))
in (match (uu____8035) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____8102 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___76_8106 -> (match (uu___76_8106) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____8107 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____8113 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.FStar_SMTEncoding_Env.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____8113))))))
in (match (uu____8102) with
| true -> begin
((decls1), (env1))
end
| uu____8122 -> begin
(FStar_All.try_with (fun uu___94_8130 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks_fvbs env1)
end
| uu____8143 -> begin
(encode_rec_lbdefs bindings typs1 toks_fvbs env1)
end)
end)) (fun uu___93_8145 -> (match (uu___93_8145) with
| FStar_SMTEncoding_Env.Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___89_8157 -> (match (uu___89_8157) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____8165 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____8165 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let nm = (

let uu____8226 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____8226) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____8230 = (encode_sigelt' env se)
in (match (uu____8230) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____8246 = (

let uu____8247 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____8247))
in (uu____8246)::[])
end
| uu____8248 -> begin
(

let uu____8249 = (

let uu____8252 = (

let uu____8253 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____8253))
in (uu____8252)::g)
in (

let uu____8254 = (

let uu____8257 = (

let uu____8258 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____8258))
in (uu____8257)::[])
in (FStar_List.append uu____8249 uu____8254)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____8273 = (

let uu____8274 = (FStar_Syntax_Subst.compress t)
in uu____8274.FStar_Syntax_Syntax.n)
in (match (uu____8273) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____8278)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____8279 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____8286 = (

let uu____8287 = (FStar_Syntax_Subst.compress t)
in uu____8287.FStar_Syntax_Syntax.n)
in (match (uu____8286) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____8291)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____8292 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____8297) -> begin
(failwith "impossible -- new_effect_for_free should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_splice (uu____8302) -> begin
(failwith "impossible -- splice should have been removed by Tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____8313) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____8316) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____8319) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____8334) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____8338 = (

let uu____8339 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____8339 Prims.op_Negation))
in (match (uu____8338) with
| true -> begin
(([]), (env))
end
| uu____8348 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____8367 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____8391 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____8391) with
| (formals, uu____8409) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____8427 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name arity)
in (match (uu____8427) with
| (aname, atok, env2) -> begin
(

let uu____8447 = (

let uu____8452 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (FStar_SMTEncoding_EncodeTerm.encode_term uu____8452 env2))
in (match (uu____8447) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____8464 = (

let uu____8465 = (

let uu____8476 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____8492 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____8476), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____8465))
in (uu____8464)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____8505 = (

let aux = (fun uu____8561 uu____8562 -> (match (((uu____8561), (uu____8562))) with
| ((bv, uu____8614), (env3, acc_sorts, acc)) -> begin
(

let uu____8652 = (FStar_SMTEncoding_Env.gen_term_var env3 bv)
in (match (uu____8652) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____8505) with
| (uu____8724, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____8747 = (

let uu____8754 = (

let uu____8755 = (

let uu____8766 = (

let uu____8767 = (

let uu____8772 = (FStar_SMTEncoding_EncodeTerm.mk_Apply tm xs_sorts)
in ((app), (uu____8772)))
in (FStar_SMTEncoding_Util.mkEq uu____8767))
in ((((app)::[])::[]), (xs_sorts), (uu____8766)))
in (FStar_SMTEncoding_Util.mkForall uu____8755))
in ((uu____8754), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____8747))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply tok_term xs_sorts)
in (

let uu____8792 = (

let uu____8799 = (

let uu____8800 = (

let uu____8811 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____8811)))
in (FStar_SMTEncoding_Util.mkForall uu____8800))
in ((uu____8799), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____8792))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end)))
end)))
in (

let uu____8830 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____8830) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____8858, uu____8859) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____8860 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid (Prims.parse_int "4"))
in (match (uu____8860) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____8877, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____8883 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___77_8887 -> (match (uu___77_8887) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____8888) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____8893) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____8894 -> begin
false
end))))
in (not (uu____8883)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____8901 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____8903 = (

let uu____8910 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____8910 env fv t quals))
in (match (uu____8903) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____8925 = (

let uu____8928 = (primitive_type_axioms env1.FStar_SMTEncoding_Env.tcenv lid tname tsym)
in (FStar_List.append decls uu____8928))
in ((uu____8925), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____8936 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____8936) with
| (uu____8945, f1) -> begin
(

let uu____8947 = (FStar_SMTEncoding_EncodeTerm.encode_formula f1 env)
in (match (uu____8947) with
| (f2, decls) -> begin
(

let g = (

let uu____8961 = (

let uu____8962 = (

let uu____8969 = (

let uu____8972 = (

let uu____8973 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____8973))
in FStar_Pervasives_Native.Some (uu____8972))
in (

let uu____8974 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____8969), (uu____8974))))
in (FStar_SMTEncoding_Util.mkAssume uu____8962))
in (uu____8961)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____8980) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____8992 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____9010 = (

let uu____9013 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____9013.FStar_Syntax_Syntax.fv_name)
in uu____9010.FStar_Syntax_Syntax.v)
in (

let uu____9014 = (

let uu____9015 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.FStar_SMTEncoding_Env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____9015))
in (match (uu____9014) with
| true -> begin
(

let val_decl = (

let uu___95_9043 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___95_9043.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___95_9043.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___95_9043.FStar_Syntax_Syntax.sigattrs})
in (

let uu____9048 = (encode_sigelt' env1 val_decl)
in (match (uu____9048) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____9059 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____8992) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____9076, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2p1); FStar_Syntax_Syntax.lbunivs = uu____9078; FStar_Syntax_Syntax.lbtyp = uu____9079; FStar_Syntax_Syntax.lbeff = uu____9080; FStar_Syntax_Syntax.lbdef = uu____9081; FStar_Syntax_Syntax.lbattrs = uu____9082; FStar_Syntax_Syntax.lbpos = uu____9083})::[]), uu____9084) when (FStar_Syntax_Syntax.fv_eq_lid b2p1 FStar_Parser_Const.b2p_lid) -> begin
(

let uu____9107 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env b2p1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v (Prims.parse_int "1"))
in (match (uu____9107) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2p_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2p"), ((x)::[])))
in (

let valid_b2p_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2p_x)::[])))
in (

let decls = (

let uu____9136 = (

let uu____9139 = (

let uu____9140 = (

let uu____9147 = (

let uu____9148 = (

let uu____9159 = (

let uu____9160 = (

let uu____9165 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2p_x), (uu____9165)))
in (FStar_SMTEncoding_Util.mkEq uu____9160))
in ((((b2p_x)::[])::[]), ((xx)::[]), (uu____9159)))
in (FStar_SMTEncoding_Util.mkForall uu____9148))
in ((uu____9147), (FStar_Pervasives_Native.Some ("b2p def")), ("b2p_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____9140))
in (uu____9139)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____9136)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____9198, uu____9199) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___78_9208 -> (match (uu___78_9208) with
| FStar_Syntax_Syntax.Discriminator (uu____9209) -> begin
true
end
| uu____9210 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____9213, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____9224 = (

let uu____9225 = (FStar_List.hd l.FStar_Ident.ns)
in uu____9225.FStar_Ident.idText)
in (Prims.op_Equality uu____9224 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___79_9229 -> (match (uu___79_9229) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____9230 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____9234) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___80_9251 -> (match (uu___80_9251) with
| FStar_Syntax_Syntax.Projector (uu____9252) -> begin
true
end
| uu____9257 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9260 = (FStar_SMTEncoding_Env.try_lookup_free_var env l)
in (match (uu____9260) with
| FStar_Pervasives_Native.Some (uu____9267) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___96_9271 = se
in (

let uu____9272 = (FStar_Ident.range_of_lid l)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu____9272; FStar_Syntax_Syntax.sigquals = uu___96_9271.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___96_9271.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___96_9271.FStar_Syntax_Syntax.sigattrs}))
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____9279) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____9297) -> begin
(

let uu____9306 = (encode_sigelts env ses)
in (match (uu____9306) with
| (g, env1) -> begin
(

let uu____9323 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___81_9346 -> (match (uu___81_9346) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____9347; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____9348; FStar_SMTEncoding_Term.assumption_fact_ids = uu____9349}) -> begin
false
end
| uu____9352 -> begin
true
end))))
in (match (uu____9323) with
| (g', inversions) -> begin
(

let uu____9367 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___82_9388 -> (match (uu___82_9388) with
| FStar_SMTEncoding_Term.DeclFun (uu____9389) -> begin
true
end
| uu____9400 -> begin
false
end))))
in (match (uu____9367) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____9418, tps, k, uu____9421, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_assumption = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___83_9438 -> (match (uu___83_9438) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____9439 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_assumption) with
| true -> begin
(

let uu____9450 = c
in (match (uu____9450) with
| (name, args, uu____9455, uu____9456, uu____9457) -> begin
(

let uu____9462 = (

let uu____9463 = (

let uu____9474 = (FStar_All.pipe_right args (FStar_List.map (fun uu____9491 -> (match (uu____9491) with
| (uu____9498, sort, uu____9500) -> begin
sort
end))))
in ((name), (uu____9474), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____9463))
in (uu____9462)::[])
end))
end
| uu____9505 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____9531 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____9537 = (FStar_TypeChecker_Env.try_lookup_lid env.FStar_SMTEncoding_Env.tcenv l)
in (FStar_All.pipe_right uu____9537 FStar_Option.isNone)))))
in (match (uu____9531) with
| true -> begin
[]
end
| uu____9568 -> begin
(

let uu____9569 = (FStar_SMTEncoding_Env.fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____9569) with
| (xxsym, xx) -> begin
(

let uu____9578 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____9617 l -> (match (uu____9617) with
| (out, decls) -> begin
(

let uu____9637 = (FStar_TypeChecker_Env.lookup_datacon env.FStar_SMTEncoding_Env.tcenv l)
in (match (uu____9637) with
| (uu____9648, data_t) -> begin
(

let uu____9650 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____9650) with
| (args, res) -> begin
(

let indices = (

let uu____9696 = (

let uu____9697 = (FStar_Syntax_Subst.compress res)
in uu____9697.FStar_Syntax_Syntax.n)
in (match (uu____9696) with
| FStar_Syntax_Syntax.Tm_app (uu____9708, indices) -> begin
indices
end
| uu____9730 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____9754 -> (match (uu____9754) with
| (x, uu____9760) -> begin
(

let uu____9761 = (

let uu____9762 = (

let uu____9769 = (FStar_SMTEncoding_Env.mk_term_projector_name l x)
in ((uu____9769), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____9762))
in (FStar_SMTEncoding_Env.push_term_var env1 x uu____9761))
end)) env))
in (

let uu____9772 = (FStar_SMTEncoding_EncodeTerm.encode_args indices env1)
in (match (uu____9772) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____9796 -> begin
()
end);
(

let eqs = (

let uu____9798 = (FStar_List.map2 (fun v1 a -> (

let uu____9814 = (

let uu____9819 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____9819), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____9814))) vars indices1)
in (FStar_All.pipe_right uu____9798 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____9822 = (

let uu____9823 = (

let uu____9828 = (

let uu____9829 = (

let uu____9834 = (FStar_SMTEncoding_Env.mk_data_tester env1 l xx)
in ((uu____9834), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____9829))
in ((out), (uu____9828)))
in (FStar_SMTEncoding_Util.mkOr uu____9823))
in ((uu____9822), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____9578) with
| (data_ax, decls) -> begin
(

let uu____9847 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____9847) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____9858 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____9858 xx tapp))
end
| uu____9861 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____9862 = (

let uu____9869 = (

let uu____9870 = (

let uu____9881 = (FStar_SMTEncoding_Env.add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____9896 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____9881), (uu____9896))))
in (FStar_SMTEncoding_Util.mkForall uu____9870))
in (

let uu____9911 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____9869), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____9911))))
in (FStar_SMTEncoding_Util.mkAssume uu____9862)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____9914 = (

let uu____9927 = (

let uu____9928 = (FStar_Syntax_Subst.compress k)
in uu____9928.FStar_Syntax_Syntax.n)
in (match (uu____9927) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____9973 -> begin
((tps), (k))
end))
in (match (uu____9914) with
| (formals, res) -> begin
(

let uu____9996 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____9996) with
| (formals1, res1) -> begin
(

let uu____10007 = (FStar_SMTEncoding_EncodeTerm.encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____10007) with
| (vars, guards, env', binder_decls, uu____10032) -> begin
(

let arity = (FStar_List.length vars)
in (

let uu____10046 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env t arity)
in (match (uu____10046) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____10069 = (

let uu____10076 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____10076)))
in (FStar_SMTEncoding_Util.mkApp uu____10069))
in (

let uu____10085 = (

let tname_decl = (

let uu____10095 = (

let uu____10096 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____10128 -> (match (uu____10128) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____10141 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((tname), (uu____10096), (FStar_SMTEncoding_Term.Term_sort), (uu____10141), (false))))
in (constructor_or_logic_type_decl uu____10095))
in (

let uu____10150 = (match (vars) with
| [] -> begin
(

let uu____10163 = (

let uu____10164 = (

let uu____10167 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_20 -> FStar_Pervasives_Native.Some (_0_20)) uu____10167))
in (FStar_SMTEncoding_Env.push_free_var env1 t arity tname uu____10164))
in (([]), (uu____10163)))
end
| uu____10178 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____10187 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____10187))
in (

let ttok_app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____10201 = (

let uu____10208 = (

let uu____10209 = (

let uu____10224 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____10224)))
in (FStar_SMTEncoding_Util.mkForall' uu____10209))
in ((uu____10208), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____10201))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____10150) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____10085) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____10264 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____10264) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____10282 = (

let uu____10283 = (

let uu____10290 = (

let uu____10291 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____10291))
in ((uu____10290), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____10283))
in (uu____10282)::[])
end
| uu____10294 -> begin
[]
end)
in (

let uu____10295 = (

let uu____10298 = (

let uu____10301 = (

let uu____10302 = (

let uu____10309 = (

let uu____10310 = (

let uu____10321 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____10321)))
in (FStar_SMTEncoding_Util.mkForall uu____10310))
in ((uu____10309), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____10302))
in (uu____10301)::[])
in (FStar_List.append karr uu____10298))
in (FStar_List.append decls1 uu____10295)))
end))
in (

let aux = (

let uu____10337 = (

let uu____10340 = (inversion_axioms tapp vars)
in (

let uu____10343 = (

let uu____10346 = (pretype_axiom env2 tapp vars)
in (uu____10346)::[])
in (FStar_List.append uu____10340 uu____10343)))
in (FStar_List.append kindingAx uu____10337))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end)))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____10353, uu____10354, uu____10355, uu____10356, uu____10357) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____10365, t, uu____10367, n_tps, uu____10369) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____10377 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____10377) with
| (formals, t_res) -> begin
(

let arity = (FStar_List.length formals)
in (

let uu____10417 = (FStar_SMTEncoding_Env.new_term_constant_and_tok_from_lid env d arity)
in (match (uu____10417) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____10438 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____10438) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____10452 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____10452) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____10522 = (FStar_SMTEncoding_Env.mk_term_projector_name d x)
in ((uu____10522), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____10524 = (

let uu____10543 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____10543), (true)))
in (FStar_All.pipe_right uu____10524 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____10582 = (FStar_SMTEncoding_EncodeTerm.encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____10582) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____10594)::uu____10595 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (FStar_SMTEncoding_EncodeTerm.mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (FStar_SMTEncoding_EncodeTerm.mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____10640 = (

let uu____10651 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____10651)))
in (FStar_SMTEncoding_Util.mkForall uu____10640))))))
end
| uu____10676 -> begin
tok_typing
end)
in (

let uu____10685 = (FStar_SMTEncoding_EncodeTerm.encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____10685) with
| (vars', guards', env'', decls_formals, uu____10710) -> begin
(

let uu____10723 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (FStar_SMTEncoding_EncodeTerm.encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____10723) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____10754 -> begin
(

let uu____10761 = (

let uu____10762 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10762))
in (uu____10761)::[])
end)
in (

let encode_elim = (fun uu____10774 -> (

let uu____10775 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____10775) with
| (head1, args) -> begin
(

let uu____10818 = (

let uu____10819 = (FStar_Syntax_Subst.compress head1)
in uu____10819.FStar_Syntax_Syntax.n)
in (match (uu____10818) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10829; FStar_Syntax_Syntax.vars = uu____10830}, uu____10831) -> begin
(

let uu____10836 = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____10836) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____10849 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____10849) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____10898 -> begin
(

let uu____10899 = (

let uu____10904 = (

let uu____10905 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____10905))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____10904)))
in (FStar_Errors.raise_error uu____10899 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____10921 = (

let uu____10922 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____10922))
in (match (uu____10921) with
| true -> begin
(

let uu____10935 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____10935)::[])
end
| uu____10936 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____10937 = (

let uu____10950 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____11000 uu____11001 -> (match (((uu____11000), (uu____11001))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____11096 = (

let uu____11103 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____11103))
in (match (uu____11096) with
| (uu____11116, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____11124 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____11124)::eqns_or_guards)
end
| uu____11125 -> begin
(

let uu____11126 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____11126)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____10950))
in (match (uu____10937) with
| (uu____11141, arg_vars, elim_eqns_or_guards, uu____11144) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
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

let uu____11172 = (

let uu____11179 = (

let uu____11180 = (

let uu____11191 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____11202 = (

let uu____11203 = (

let uu____11208 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____11208)))
in (FStar_SMTEncoding_Util.mkImp uu____11203))
in ((((ty_pred)::[])::[]), (uu____11191), (uu____11202))))
in (FStar_SMTEncoding_Util.mkForall uu____11180))
in ((uu____11179), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____11172))
in (

let subterm_ordering = (

let uu____11226 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____11226) with
| true -> begin
(

let x = (

let uu____11232 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____11232), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____11234 = (

let uu____11241 = (

let uu____11242 = (

let uu____11253 = (

let uu____11258 = (

let uu____11261 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____11261)::[])
in (uu____11258)::[])
in (

let uu____11266 = (

let uu____11267 = (

let uu____11272 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____11273 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____11272), (uu____11273))))
in (FStar_SMTEncoding_Util.mkImp uu____11267))
in ((uu____11253), ((x)::[]), (uu____11266))))
in (FStar_SMTEncoding_Util.mkForall uu____11242))
in (

let uu____11292 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____11241), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____11292))))
in (FStar_SMTEncoding_Util.mkAssume uu____11234))))
end
| uu____11295 -> begin
(

let prec = (

let uu____11299 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____11326 -> begin
(

let uu____11327 = (

let uu____11328 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____11328 dapp1))
in (uu____11327)::[])
end))))
in (FStar_All.pipe_right uu____11299 FStar_List.flatten))
in (

let uu____11335 = (

let uu____11342 = (

let uu____11343 = (

let uu____11354 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____11365 = (

let uu____11366 = (

let uu____11371 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____11371)))
in (FStar_SMTEncoding_Util.mkImp uu____11366))
in ((((ty_pred)::[])::[]), (uu____11354), (uu____11365))))
in (FStar_SMTEncoding_Util.mkForall uu____11343))
in ((uu____11342), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____11335)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11391 = (FStar_SMTEncoding_Env.lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____11391) with
| (encoded_head, encoded_head_arity) -> begin
(

let uu____11404 = (FStar_SMTEncoding_EncodeTerm.encode_args args env')
in (match (uu____11404) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____11453 -> begin
(

let uu____11454 = (

let uu____11459 = (

let uu____11460 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____11460))
in ((FStar_Errors.Fatal_NonVariableInductiveTypeParameter), (uu____11459)))
in (FStar_Errors.raise_error uu____11454 orig_arg.FStar_Syntax_Syntax.pos))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____11476 = (

let uu____11477 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____11477))
in (match (uu____11476) with
| true -> begin
(

let uu____11490 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____11490)::[])
end
| uu____11491 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____11492 = (

let uu____11505 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____11555 uu____11556 -> (match (((uu____11555), (uu____11556))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____11651 = (

let uu____11658 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_SMTEncoding_Env.gen_term_var env2 uu____11658))
in (match (uu____11651) with
| (uu____11671, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____11679 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____11679)::eqns_or_guards)
end
| uu____11680 -> begin
(

let uu____11681 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____11681)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____11505))
in (match (uu____11492) with
| (uu____11696, arg_vars, elim_eqns_or_guards, uu____11699) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_EncodeTerm.maybe_curry_app fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.p (FStar_SMTEncoding_Term.Var (encoded_head)) encoded_head_arity arg_vars1)
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

let uu____11727 = (

let uu____11734 = (

let uu____11735 = (

let uu____11746 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____11757 = (

let uu____11758 = (

let uu____11763 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____11763)))
in (FStar_SMTEncoding_Util.mkImp uu____11758))
in ((((ty_pred)::[])::[]), (uu____11746), (uu____11757))))
in (FStar_SMTEncoding_Util.mkForall uu____11735))
in ((uu____11734), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____11727))
in (

let subterm_ordering = (

let uu____11781 = (FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)
in (match (uu____11781) with
| true -> begin
(

let x = (

let uu____11787 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "x")
in ((uu____11787), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____11789 = (

let uu____11796 = (

let uu____11797 = (

let uu____11808 = (

let uu____11813 = (

let uu____11816 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____11816)::[])
in (uu____11813)::[])
in (

let uu____11821 = (

let uu____11822 = (

let uu____11827 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____11828 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____11827), (uu____11828))))
in (FStar_SMTEncoding_Util.mkImp uu____11822))
in ((uu____11808), ((x)::[]), (uu____11821))))
in (FStar_SMTEncoding_Util.mkForall uu____11797))
in (

let uu____11847 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "lextop")
in ((uu____11796), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____11847))))
in (FStar_SMTEncoding_Util.mkAssume uu____11789))))
end
| uu____11850 -> begin
(

let prec = (

let uu____11854 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____11881 -> begin
(

let uu____11882 = (

let uu____11883 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____11883 dapp1))
in (uu____11882)::[])
end))))
in (FStar_All.pipe_right uu____11854 FStar_List.flatten))
in (

let uu____11890 = (

let uu____11897 = (

let uu____11898 = (

let uu____11909 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____11920 = (

let uu____11921 = (

let uu____11926 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____11926)))
in (FStar_SMTEncoding_Util.mkImp uu____11921))
in ((((ty_pred)::[])::[]), (uu____11909), (uu____11920))))
in (FStar_SMTEncoding_Util.mkForall uu____11898))
in ((uu____11897), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____11890)))
end))
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end))
end))
end
| uu____11945 -> begin
((

let uu____11947 = (

let uu____11952 = (

let uu____11953 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____11954 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____11953 uu____11954)))
in ((FStar_Errors.Warning_ConstructorBuildsUnexpectedType), (uu____11952)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____11947));
(([]), ([]));
)
end))
end)))
in (

let uu____11959 = (encode_elim ())
in (match (uu____11959) with
| (decls2, elim) -> begin
(

let g = (

let uu____11979 = (

let uu____11982 = (

let uu____11985 = (

let uu____11988 = (

let uu____11991 = (

let uu____11992 = (

let uu____12003 = (

let uu____12006 = (

let uu____12007 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____12007))
in FStar_Pervasives_Native.Some (uu____12006))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____12003)))
in FStar_SMTEncoding_Term.DeclFun (uu____11992))
in (uu____11991)::[])
in (

let uu____12012 = (

let uu____12015 = (

let uu____12018 = (

let uu____12021 = (

let uu____12024 = (

let uu____12027 = (

let uu____12030 = (

let uu____12031 = (

let uu____12038 = (

let uu____12039 = (

let uu____12050 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____12050)))
in (FStar_SMTEncoding_Util.mkForall uu____12039))
in ((uu____12038), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12031))
in (

let uu____12063 = (

let uu____12066 = (

let uu____12067 = (

let uu____12074 = (

let uu____12075 = (

let uu____12086 = (FStar_SMTEncoding_Env.add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____12097 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____12086), (uu____12097))))
in (FStar_SMTEncoding_Util.mkForall uu____12075))
in ((uu____12074), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____12067))
in (uu____12066)::[])
in (uu____12030)::uu____12063))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____12027)
in (FStar_List.append uu____12024 elim))
in (FStar_List.append decls_pred uu____12021))
in (FStar_List.append decls_formals uu____12018))
in (FStar_List.append proxy_fresh uu____12015))
in (FStar_List.append uu____11988 uu____12012)))
in (FStar_List.append decls3 uu____11985))
in (FStar_List.append decls2 uu____11982))
in (FStar_List.append binder_decls uu____11979))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end)))
end)))
end)))
end))))
and encode_sigelts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____12143 se -> (match (uu____12143) with
| (g, env1) -> begin
(

let uu____12163 = (encode_sigelt env1 se)
in (match (uu____12163) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : FStar_SMTEncoding_Env.env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____12228 -> (match (uu____12228) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____12260) -> begin
(((i + (Prims.parse_int "1"))), (decls), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.FStar_SMTEncoding_Env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____12266 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12266) with
| true -> begin
(

let uu____12267 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____12268 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____12269 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____12267 uu____12268 uu____12269))))
end
| uu____12270 -> begin
()
end));
(

let uu____12271 = (FStar_SMTEncoding_EncodeTerm.encode_term t1 env1)
in (match (uu____12271) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____12287 = (

let uu____12294 = (

let uu____12295 = (

let uu____12296 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____12296 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____12295))
in (FStar_SMTEncoding_Env.new_term_constant_from_string env1 x uu____12294))
in (match (uu____12287) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____12312 = (FStar_Options.log_queries ())
in (match (uu____12312) with
| true -> begin
(

let uu____12315 = (

let uu____12316 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____12317 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____12318 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____12316 uu____12317 uu____12318))))
in FStar_Pervasives_Native.Some (uu____12315))
end
| uu____12319 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____12334, t)) -> begin
(

let t_norm = (FStar_SMTEncoding_EncodeTerm.whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____12348 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____12348) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____12371, se, uu____12373) -> begin
(

let uu____12378 = (encode_sigelt env1 se)
in (match (uu____12378) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____12395, se) -> begin
(

let uu____12401 = (encode_sigelt env1 se)
in (match (uu____12401) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____12418 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____12418) with
| (uu____12441, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____12456 'Auu____12457 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____12456 * 'Auu____12457) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____12526 -> (match (uu____12526) with
| (l, uu____12538, uu____12539) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____12585 -> (match (uu____12585) with
| (l, uu____12599, uu____12600) -> begin
(

let uu____12609 = (FStar_All.pipe_left (fun _0_21 -> FStar_SMTEncoding_Term.Echo (_0_21)) (FStar_Pervasives_Native.fst l))
in (

let uu____12610 = (

let uu____12613 = (

let uu____12614 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____12614))
in (uu____12613)::[])
in (uu____12609)::uu____12610))
end))))
in ((prefix1), (suffix)))))


let last_env : FStar_SMTEncoding_Env.env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> (

let uu____12665 = (

let uu____12668 = (

let uu____12669 = (FStar_Util.psmap_empty ())
in (

let uu____12684 = (FStar_Util.psmap_empty ())
in (

let uu____12687 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____12690 = (

let uu____12691 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____12691 FStar_Ident.string_of_lid))
in {FStar_SMTEncoding_Env.bvar_bindings = uu____12669; FStar_SMTEncoding_Env.fvar_bindings = uu____12684; FStar_SMTEncoding_Env.depth = (Prims.parse_int "0"); FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu____12687; FStar_SMTEncoding_Env.nolabels = false; FStar_SMTEncoding_Env.use_zfuel_name = false; FStar_SMTEncoding_Env.encode_non_total_function_typ = true; FStar_SMTEncoding_Env.current_module_name = uu____12690; FStar_SMTEncoding_Env.encoding_quantifier = false}))))
in (uu____12668)::[])
in (FStar_ST.op_Colon_Equals last_env uu____12665)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Env.env_t = (fun cmn tcenv -> (

let uu____12735 = (FStar_ST.op_Bang last_env)
in (match (uu____12735) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____12772 -> begin
(

let uu___97_12775 = e
in (

let uu____12776 = (FStar_Ident.string_of_lid cmn)
in {FStar_SMTEncoding_Env.bvar_bindings = uu___97_12775.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___97_12775.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___97_12775.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = tcenv; FStar_SMTEncoding_Env.warn = uu___97_12775.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___97_12775.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___97_12775.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___97_12775.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___97_12775.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu____12776; FStar_SMTEncoding_Env.encoding_quantifier = uu___97_12775.FStar_SMTEncoding_Env.encoding_quantifier}))
end)))


let set_env : FStar_SMTEncoding_Env.env_t  ->  unit = (fun env -> (

let uu____12782 = (FStar_ST.op_Bang last_env)
in (match (uu____12782) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____12818)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : unit  ->  unit = (fun uu____12859 -> (

let uu____12860 = (FStar_ST.op_Bang last_env)
in (match (uu____12860) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.FStar_SMTEncoding_Env.cache)
in (

let top = (

let uu___98_12904 = hd1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___98_12904.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___98_12904.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___98_12904.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___98_12904.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___98_12904.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = refs; FStar_SMTEncoding_Env.nolabels = uu___98_12904.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___98_12904.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___98_12904.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___98_12904.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___98_12904.FStar_SMTEncoding_Env.encoding_quantifier})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : unit  ->  unit = (fun uu____12942 -> (

let uu____12943 = (FStar_ST.op_Bang last_env)
in (match (uu____12943) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____12979)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let init : FStar_TypeChecker_Env.env  ->  unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[]));
))


let push : Prims.string  ->  unit = (fun msg -> ((push_env ());
(FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.push ());
(FStar_SMTEncoding_Z3.push msg);
))


let pop : Prims.string  ->  unit = (fun msg -> ((pop_env ());
(FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.pop ());
(FStar_SMTEncoding_Z3.pop msg);
))


let open_fact_db_tags : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____13067)::uu____13068, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___99_13076 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___99_13076.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___99_13076.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___99_13076.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____13077 -> begin
d
end))


let fact_dbs_for_lid : FStar_SMTEncoding_Env.env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____13096 = (

let uu____13099 = (

let uu____13100 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____13100))
in (

let uu____13101 = (open_fact_db_tags env)
in (uu____13099)::uu____13101))
in (FStar_SMTEncoding_Term.Name (lid))::uu____13096))


let encode_top_level_facts : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Env.env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____13127 = (encode_sigelt env se)
in (match (uu____13127) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____13169 = (FStar_Options.log_queries ())
in (match (uu____13169) with
| true -> begin
(

let uu____13172 = (

let uu____13173 = (

let uu____13174 = (

let uu____13175 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____13175 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____13174))
in FStar_SMTEncoding_Term.Caption (uu____13173))
in (uu____13172)::decls)
end
| uu____13184 -> begin
decls
end)))
in ((

let uu____13186 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____13186) with
| true -> begin
(

let uu____13187 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____13187))
end
| uu____13188 -> begin
()
end));
(

let env = (

let uu____13190 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____13190 tcenv))
in (

let uu____13191 = (encode_top_level_facts env se)
in (match (uu____13191) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____13205 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____13205));
)
end)));
)))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____13219 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____13221 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____13221) with
| true -> begin
(

let uu____13222 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____13222))
end
| uu____13223 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____13261 se -> (match (uu____13261) with
| (g, env2) -> begin
(

let uu____13281 = (encode_top_level_facts env2 se)
in (match (uu____13281) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____13304 = (encode_signature (

let uu___100_13313 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___100_13313.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___100_13313.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___100_13313.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___100_13313.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = false; FStar_SMTEncoding_Env.cache = uu___100_13313.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___100_13313.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___100_13313.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___100_13313.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___100_13313.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___100_13313.FStar_SMTEncoding_Env.encoding_quantifier}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____13304) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____13332 = (FStar_Options.log_queries ())
in (match (uu____13332) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____13336 -> begin
decls1
end)))
in ((set_env (

let uu___101_13340 = env1
in {FStar_SMTEncoding_Env.bvar_bindings = uu___101_13340.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___101_13340.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___101_13340.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___101_13340.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = true; FStar_SMTEncoding_Env.cache = uu___101_13340.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___101_13340.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___101_13340.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___101_13340.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___101_13340.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___101_13340.FStar_SMTEncoding_Env.encoding_quantifier}));
(

let uu____13342 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____13342) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____13343 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____13400 = (

let uu____13401 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____13401.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____13400));
(

let env = (

let uu____13403 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____13403 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____13415 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____13452 = (aux rest)
in (match (uu____13452) with
| (out, rest1) -> begin
(

let t = (

let uu____13482 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____13482) with
| FStar_Pervasives_Native.Some (uu____13487) -> begin
(

let uu____13488 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____13488 x.FStar_Syntax_Syntax.sort))
end
| uu____13489 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t)
in (

let uu____13493 = (

let uu____13496 = (FStar_Syntax_Syntax.mk_binder (

let uu___102_13499 = x
in {FStar_Syntax_Syntax.ppname = uu___102_13499.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___102_13499.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____13496)::out)
in ((uu____13493), (rest1)))))
end))
end
| uu____13504 -> begin
(([]), (bindings1))
end))
in (

let uu____13511 = (aux bindings)
in (match (uu____13511) with
| (closing, bindings1) -> begin
(

let uu____13536 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____13536), (bindings1)))
end)))
in (match (uu____13415) with
| (q1, bindings1) -> begin
(

let uu____13559 = (

let uu____13564 = (FStar_List.filter (fun uu___84_13569 -> (match (uu___84_13569) with
| FStar_TypeChecker_Env.Binding_sig (uu____13570) -> begin
false
end
| uu____13577 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____13564))
in (match (uu____13559) with
| (env_decls, env1) -> begin
((

let uu____13595 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____13595) with
| true -> begin
(

let uu____13596 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____13596))
end
| uu____13597 -> begin
()
end));
(

let uu____13598 = (FStar_SMTEncoding_EncodeTerm.encode_formula q1 env1)
in (match (uu____13598) with
| (phi, qdecls) -> begin
(

let uu____13619 = (

let uu____13624 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____13624 phi))
in (match (uu____13619) with
| (labels, phi1) -> begin
(

let uu____13641 = (encode_labels labels)
in (match (uu____13641) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____13678 = (

let uu____13685 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____13686 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "@query")
in ((uu____13685), (FStar_Pervasives_Native.Some ("query")), (uu____13686))))
in (FStar_SMTEncoding_Util.mkAssume uu____13678))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))





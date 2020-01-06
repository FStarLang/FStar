
open Prims
open FStar_Pervasives

type norm_cb =
(FStar_Ident.lid, FStar_Syntax_Syntax.term) FStar_Util.either  ->  FStar_Syntax_Syntax.term


let id_norm_cb : norm_cb = (fun uu___0_16 -> (match (uu___0_16) with
| FStar_Util.Inr (x) -> begin
x
end
| FStar_Util.Inl (l) -> begin
(

let uu____23 = (FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____23))
end))

exception Embedding_failure


let uu___is_Embedding_failure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Embedding_failure -> begin
true
end
| uu____33 -> begin
false
end))

exception Unembedding_failure


let uu___is_Unembedding_failure : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unembedding_failure -> begin
true
end
| uu____44 -> begin
false
end))


type shadow_term =
FStar_Syntax_Syntax.term FStar_Thunk.t FStar_Pervasives_Native.option


let map_shadow : shadow_term  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  shadow_term = (fun s f -> (FStar_Util.map_opt s (FStar_Thunk.map f)))


let force_shadow : shadow_term  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun s -> (FStar_Util.map_opt s FStar_Thunk.force))


type embed_t =
FStar_Range.range  ->  shadow_term  ->  norm_cb  ->  FStar_Syntax_Syntax.term


type 'a unembed_t =
Prims.bool  ->  norm_cb  ->  'a FStar_Pervasives_Native.option


type 'a raw_embedder =
'a  ->  embed_t


type 'a raw_unembedder =
FStar_Syntax_Syntax.term  ->  'a unembed_t


type 'a printer =
'a  ->  Prims.string

type 'a embedding =
{em : 'a  ->  embed_t; un : FStar_Syntax_Syntax.term  ->  'a unembed_t; typ : FStar_Syntax_Syntax.typ; print : 'a printer; emb_typ : FStar_Syntax_Syntax.emb_typ}


let __proj__Mkembedding__item__em : 'a . 'a embedding  ->  'a  ->  embed_t = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; print = print7; emb_typ = emb_typ} -> begin
em
end))


let __proj__Mkembedding__item__un : 'a . 'a embedding  ->  FStar_Syntax_Syntax.term  ->  'a unembed_t = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; print = print7; emb_typ = emb_typ} -> begin
un
end))


let __proj__Mkembedding__item__typ : 'a . 'a embedding  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; print = print7; emb_typ = emb_typ} -> begin
typ
end))


let __proj__Mkembedding__item__print : 'a . 'a embedding  ->  'a printer = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; print = print7; emb_typ = emb_typ} -> begin
print7
end))


let __proj__Mkembedding__item__emb_typ : 'a . 'a embedding  ->  FStar_Syntax_Syntax.emb_typ = (fun projectee -> (match (projectee) with
| {em = em; un = un; typ = typ; print = print7; emb_typ = emb_typ} -> begin
emb_typ
end))


let emb_typ_of : 'a . 'a embedding  ->  FStar_Syntax_Syntax.emb_typ = (fun e -> e.emb_typ)


let unknown_printer : 'Auu____431 . FStar_Syntax_Syntax.term  ->  'Auu____431  ->  Prims.string = (fun typ uu____442 -> (

let uu____443 = (FStar_Syntax_Print.term_to_string typ)
in (FStar_Util.format1 "unknown %s" uu____443)))


let term_as_fv : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.fv = (fun t -> (

let uu____452 = (

let uu____453 = (FStar_Syntax_Subst.compress t)
in uu____453.FStar_Syntax_Syntax.n)
in (match (uu____452) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____457 -> begin
(

let uu____458 = (

let uu____460 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Embeddings not defined for type %s" uu____460))
in (failwith uu____458))
end)))


let mk_emb : 'a . 'a raw_embedder  ->  'a raw_unembedder  ->  FStar_Syntax_Syntax.fv  ->  'a embedding = (fun em un fv -> (

let typ = (FStar_Syntax_Syntax.fv_to_tm fv)
in (

let uu____503 = (

let uu____504 = (

let uu____512 = (

let uu____514 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_All.pipe_right uu____514 FStar_Ident.string_of_lid))
in ((uu____512), ([])))
in FStar_Syntax_Syntax.ET_app (uu____504))
in {em = em; un = un; typ = typ; print = (unknown_printer typ); emb_typ = uu____503})))


let mk_emb_full : 'a . 'a raw_embedder  ->  'a raw_unembedder  ->  FStar_Syntax_Syntax.typ  ->  ('a  ->  Prims.string)  ->  FStar_Syntax_Syntax.emb_typ  ->  'a embedding = (fun em un typ printer emb_typ -> {em = em; un = un; typ = typ; print = printer; emb_typ = emb_typ})


let embed : 'a . 'a embedding  ->  'a  ->  embed_t = (fun e x -> (e.em x))


let unembed : 'a . 'a embedding  ->  FStar_Syntax_Syntax.term  ->  'a unembed_t = (fun e t -> (e.un t))


let warn_unembed : 'a . 'a embedding  ->  FStar_Syntax_Syntax.term  ->  norm_cb  ->  'a FStar_Pervasives_Native.option = (fun e t n1 -> (

let uu____663 = (unembed e t)
in (uu____663 true n1)))


let try_unembed : 'a . 'a embedding  ->  FStar_Syntax_Syntax.term  ->  norm_cb  ->  'a FStar_Pervasives_Native.option = (fun e t n1 -> (

let uu____704 = (unembed e t)
in (uu____704 false n1)))


let type_of : 'a . 'a embedding  ->  FStar_Syntax_Syntax.typ = (fun e -> e.typ)


let set_type : 'a . FStar_Syntax_Syntax.typ  ->  'a embedding  ->  'a embedding = (fun ty e -> (

let uu___77_751 = e
in {em = uu___77_751.em; un = uu___77_751.un; typ = ty; print = uu___77_751.print; emb_typ = uu___77_751.emb_typ}))


let lazy_embed : 'a . 'a printer  ->  FStar_Syntax_Syntax.emb_typ  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term  ->  'a  ->  (unit  ->  FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun pa et rng ta x f -> ((

let uu____814 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____814) with
| true -> begin
(

let uu____838 = (FStar_Syntax_Print.term_to_string ta)
in (

let uu____840 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____842 = (pa x)
in (FStar_Util.print3 "Embedding a %s\n\temb_typ=%s\n\tvalue is %s\n" uu____838 uu____840 uu____842))))
end
| uu____845 -> begin
()
end));
(

let uu____847 = (FStar_ST.op_Bang FStar_Options.eager_embedding)
in (match (uu____847) with
| true -> begin
(f ())
end
| uu____873 -> begin
(

let thunk1 = (FStar_Thunk.mk f)
in (

let uu____882 = (

let uu____889 = (

let uu____890 = (

let uu____891 = (FStar_Dyn.mkdyn x)
in {FStar_Syntax_Syntax.blob = uu____891; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (((et), (thunk1))); FStar_Syntax_Syntax.ltyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.rng = rng})
in FStar_Syntax_Syntax.Tm_lazy (uu____890))
in (FStar_Syntax_Syntax.mk uu____889))
in (uu____882 FStar_Pervasives_Native.None rng)))
end));
))


let lazy_unembed : 'a . 'a printer  ->  FStar_Syntax_Syntax.emb_typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term  ->  'a FStar_Pervasives_Native.option)  ->  'a FStar_Pervasives_Native.option = (fun pa et x ta f -> (

let x1 = (FStar_Syntax_Subst.compress x)
in (match (x1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (et', t); FStar_Syntax_Syntax.ltyp = uu____958; FStar_Syntax_Syntax.rng = uu____959}) -> begin
(

let uu____970 = ((Prims.op_disEquality et et') || (FStar_ST.op_Bang FStar_Options.eager_embedding))
in (match (uu____970) with
| true -> begin
(

let res = (

let uu____999 = (FStar_Thunk.force t)
in (f uu____999))
in ((

let uu____1003 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____1003) with
| true -> begin
(

let uu____1027 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____1029 = (FStar_Syntax_Print.emb_typ_to_string et')
in (

let uu____1031 = (match (res) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x2) -> begin
(

let uu____1036 = (pa x2)
in (Prims.op_Hat "Some " uu____1036))
end)
in (FStar_Util.print3 "Unembed cancellation failed\n\t%s <> %s\nvalue is %s\n" uu____1027 uu____1029 uu____1031))))
end
| uu____1040 -> begin
()
end));
res;
))
end
| uu____1042 -> begin
(

let a = (FStar_Dyn.undyn b)
in ((

let uu____1046 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____1046) with
| true -> begin
(

let uu____1070 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____1072 = (pa a)
in (FStar_Util.print2 "Unembed cancelled for %s\n\tvalue is %s\n" uu____1070 uu____1072)))
end
| uu____1075 -> begin
()
end));
FStar_Pervasives_Native.Some (a);
))
end))
end
| uu____1077 -> begin
(

let aopt = (f x1)
in ((

let uu____1082 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____1082) with
| true -> begin
(

let uu____1106 = (FStar_Syntax_Print.emb_typ_to_string et)
in (

let uu____1108 = (FStar_Syntax_Print.term_to_string x1)
in (

let uu____1110 = (match (aopt) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (a) -> begin
(

let uu____1115 = (pa a)
in (Prims.op_Hat "Some " uu____1115))
end)
in (FStar_Util.print3 "Unembedding:\n\temb_typ=%s\n\tterm is %s\n\tvalue is %s\n" uu____1106 uu____1108 uu____1110))))
end
| uu____1119 -> begin
()
end));
aopt;
))
end)))


let mk_any_emb : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term embedding = (fun typ -> (

let em = (fun t _r _topt _norm -> ((

let uu____1153 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____1153) with
| true -> begin
(

let uu____1177 = (unknown_printer typ t)
in (FStar_Util.print1 "Embedding abstract: %s\n" uu____1177))
end
| uu____1180 -> begin
()
end));
t;
))
in (

let un = (fun t _w _n -> ((

let uu____1205 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____1205) with
| true -> begin
(

let uu____1229 = (unknown_printer typ t)
in (FStar_Util.print1 "Unembedding abstract: %s\n" uu____1229))
end
| uu____1232 -> begin
()
end));
FStar_Pervasives_Native.Some (t);
))
in (mk_emb_full em un typ (unknown_printer typ) FStar_Syntax_Syntax.ET_abstract))))


let e_any : FStar_Syntax_Syntax.term embedding = (

let em = (fun t _r _topt _norm -> t)
in (

let un = (fun t _w _n -> FStar_Pervasives_Native.Some (t))
in (

let uu____1282 = (

let uu____1283 = (

let uu____1291 = (FStar_All.pipe_right FStar_Parser_Const.term_lid FStar_Ident.string_of_lid)
in ((uu____1291), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1283))
in (mk_emb_full em un FStar_Syntax_Syntax.t_term FStar_Syntax_Print.term_to_string uu____1282))))


let e_unit : unit embedding = (

let em = (fun u rng _topt _norm -> (

let uu___151_1323 = FStar_Syntax_Util.exp_unit
in {FStar_Syntax_Syntax.n = uu___151_1323.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___151_1323.FStar_Syntax_Syntax.vars}))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unascribe t0)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____1351 -> begin
((match (w) with
| true -> begin
(

let uu____1354 = (

let uu____1360 = (

let uu____1362 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format1 "Not an embedded unit: %s" uu____1362))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1360)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1354))
end
| uu____1366 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (

let uu____1368 = (

let uu____1369 = (

let uu____1377 = (FStar_All.pipe_right FStar_Parser_Const.unit_lid FStar_Ident.string_of_lid)
in ((uu____1377), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1369))
in (mk_emb_full em un FStar_Syntax_Syntax.t_unit (fun uu____1384 -> "()") uu____1368))))


let e_bool : Prims.bool embedding = (

let em = (fun b rng _topt _norm -> (

let t = (match (b) with
| true -> begin
FStar_Syntax_Util.exp_true_bool
end
| uu____1421 -> begin
FStar_Syntax_Util.exp_false_bool
end)
in (

let uu___171_1423 = t
in {FStar_Syntax_Syntax.n = uu___171_1423.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___171_1423.FStar_Syntax_Syntax.vars})))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (b)) -> begin
FStar_Pervasives_Native.Some (b)
end
| uu____1459 -> begin
((match (w) with
| true -> begin
(

let uu____1462 = (

let uu____1468 = (

let uu____1470 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded bool: %s" uu____1470))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1468)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1462))
end
| uu____1474 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (

let uu____1477 = (

let uu____1478 = (

let uu____1486 = (FStar_All.pipe_right FStar_Parser_Const.bool_lid FStar_Ident.string_of_lid)
in ((uu____1486), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1478))
in (mk_emb_full em un FStar_Syntax_Syntax.t_bool FStar_Util.string_of_bool uu____1477))))


let e_char : FStar_Char.char embedding = (

let em = (fun c rng _topt _norm -> (

let t = (FStar_Syntax_Util.exp_char c)
in (

let uu___190_1523 = t
in {FStar_Syntax_Syntax.n = uu___190_1523.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = rng; FStar_Syntax_Syntax.vars = uu___190_1523.FStar_Syntax_Syntax.vars})))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char (c)) -> begin
FStar_Pervasives_Native.Some (c)
end
| uu____1557 -> begin
((match (w) with
| true -> begin
(

let uu____1560 = (

let uu____1566 = (

let uu____1568 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded char: %s" uu____1568))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1566)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1560))
end
| uu____1572 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (

let uu____1575 = (

let uu____1576 = (

let uu____1584 = (FStar_All.pipe_right FStar_Parser_Const.char_lid FStar_Ident.string_of_lid)
in ((uu____1584), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1576))
in (mk_emb_full em un FStar_Syntax_Syntax.t_char FStar_Util.string_of_char uu____1575))))


let e_int : FStar_BigInt.t embedding = (

let t_int1 = (FStar_Syntax_Util.fvar_const FStar_Parser_Const.int_lid)
in (

let emb_t_int = (

let uu____1596 = (

let uu____1604 = (FStar_All.pipe_right FStar_Parser_Const.int_lid FStar_Ident.string_of_lid)
in ((uu____1604), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1596))
in (

let em = (fun i rng _topt _norm -> (lazy_embed FStar_BigInt.string_of_big_int emb_t_int rng t_int1 i (fun uu____1635 -> (

let uu____1636 = (FStar_BigInt.string_of_big_int i)
in (FStar_Syntax_Util.exp_int uu____1636)))))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed FStar_BigInt.string_of_big_int emb_t_int t t_int1 (fun t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, uu____1671)) -> begin
(

let uu____1686 = (FStar_BigInt.big_int_of_string s)
in FStar_Pervasives_Native.Some (uu____1686))
end
| uu____1687 -> begin
((match (w) with
| true -> begin
(

let uu____1690 = (

let uu____1696 = (

let uu____1698 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded int: %s" uu____1698))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1696)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1690))
end
| uu____1702 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))))
in (mk_emb_full em un FStar_Syntax_Syntax.t_int FStar_BigInt.string_of_big_int emb_t_int)))))


let e_string : Prims.string embedding = (

let emb_t_string = (

let uu____1709 = (

let uu____1717 = (FStar_All.pipe_right FStar_Parser_Const.string_lid FStar_Ident.string_of_lid)
in ((uu____1717), ([])))
in FStar_Syntax_Syntax.ET_app (uu____1709))
in (

let em = (fun s rng _topt _norm -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (((s), (rng))))) FStar_Pervasives_Native.None rng))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____1780)) -> begin
FStar_Pervasives_Native.Some (s)
end
| uu____1784 -> begin
((match (w) with
| true -> begin
(

let uu____1787 = (

let uu____1793 = (

let uu____1795 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded string: %s" uu____1795))
in ((FStar_Errors.Warning_NotEmbedded), (uu____1793)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____1787))
end
| uu____1799 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (mk_emb_full em un FStar_Syntax_Syntax.t_string (fun x -> (Prims.op_Hat "\"" (Prims.op_Hat x "\""))) emb_t_string))))


let e_option : 'a . 'a embedding  ->  'a FStar_Pervasives_Native.option embedding = (fun ea -> (

let t_option_a = (

let t_opt = (FStar_Syntax_Util.fvar_const FStar_Parser_Const.option_lid)
in (

let uu____1831 = (

let uu____1836 = (

let uu____1837 = (FStar_Syntax_Syntax.as_arg ea.typ)
in (uu____1837)::[])
in (FStar_Syntax_Syntax.mk_Tm_app t_opt uu____1836))
in (uu____1831 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let emb_t_option_a = (

let uu____1863 = (

let uu____1871 = (FStar_All.pipe_right FStar_Parser_Const.option_lid FStar_Ident.string_of_lid)
in ((uu____1871), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____1863))
in (

let printer = (fun uu___1_1885 -> (match (uu___1_1885) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____1891 = (

let uu____1893 = (ea.print x)
in (Prims.op_Hat uu____1893 ")"))
in (Prims.op_Hat "(Some " uu____1891))
end))
in (

let em = (fun o rng topt norm1 -> (lazy_embed printer emb_t_option_a rng t_option_a o (fun uu____1928 -> (match (o) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1929 = (

let uu____1934 = (

let uu____1935 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.none_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____1935 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____1936 = (

let uu____1937 = (

let uu____1946 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____1946))
in (uu____1937)::[])
in (FStar_Syntax_Syntax.mk_Tm_app uu____1934 uu____1936)))
in (uu____1929 FStar_Pervasives_Native.None rng))
end
| FStar_Pervasives_Native.Some (a) -> begin
(

let shadow_a = (map_shadow topt (fun t -> (

let v1 = (FStar_Ident.mk_ident (("v"), (rng)))
in (

let some_v = (FStar_Syntax_Util.mk_field_projector_name_from_ident FStar_Parser_Const.some_lid v1)
in (

let some_v_tm = (

let uu____1976 = (FStar_Syntax_Syntax.lid_as_fv some_v FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1976))
in (

let uu____1977 = (

let uu____1982 = (FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____1983 = (

let uu____1984 = (

let uu____1993 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____1993))
in (

let uu____1994 = (

let uu____2005 = (FStar_Syntax_Syntax.as_arg t)
in (uu____2005)::[])
in (uu____1984)::uu____1994))
in (FStar_Syntax_Syntax.mk_Tm_app uu____1982 uu____1983)))
in (uu____1977 FStar_Pervasives_Native.None rng)))))))
in (

let uu____2038 = (

let uu____2043 = (

let uu____2044 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.some_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2044 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____2045 = (

let uu____2046 = (

let uu____2055 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____2055))
in (

let uu____2056 = (

let uu____2067 = (

let uu____2076 = (

let uu____2077 = (embed ea a)
in (uu____2077 rng shadow_a norm1))
in (FStar_Syntax_Syntax.as_arg uu____2076))
in (uu____2067)::[])
in (uu____2046)::uu____2056))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2043 uu____2045)))
in (uu____2038 FStar_Pervasives_Native.None rng)))
end))))
in (

let un = (fun t0 w norm1 -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed printer emb_t_option_a t t_option_a (fun t1 -> (

let uu____2147 = (FStar_Syntax_Util.head_and_args' t1)
in (match (uu____2147) with
| (hd1, args) -> begin
(

let uu____2188 = (

let uu____2203 = (

let uu____2204 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2204.FStar_Syntax_Syntax.n)
in ((uu____2203), (args)))
in (match (uu____2188) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____2222) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.none_lid) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2246)::((a, uu____2248))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.some_lid) -> begin
(

let uu____2299 = (

let uu____2302 = (unembed ea a)
in (uu____2302 w norm1))
in (FStar_Util.bind_opt uu____2299 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (a1)))))
end
| uu____2315 -> begin
((match (w) with
| true -> begin
(

let uu____2332 = (

let uu____2338 = (

let uu____2340 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded option: %s" uu____2340))
in ((FStar_Errors.Warning_NotEmbedded), (uu____2338)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____2332))
end
| uu____2344 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))))
in (

let uu____2348 = (

let uu____2349 = (type_of ea)
in (FStar_Syntax_Syntax.t_option_of uu____2349))
in (mk_emb_full em un uu____2348 printer emb_t_option_a))))))))


let e_tuple2 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a * 'b) embedding = (fun ea eb -> (

let t_pair_a_b = (

let t_tup2 = (FStar_Syntax_Util.fvar_const FStar_Parser_Const.lid_tuple2)
in (

let uu____2391 = (

let uu____2396 = (

let uu____2397 = (FStar_Syntax_Syntax.as_arg ea.typ)
in (

let uu____2406 = (

let uu____2417 = (FStar_Syntax_Syntax.as_arg eb.typ)
in (uu____2417)::[])
in (uu____2397)::uu____2406))
in (FStar_Syntax_Syntax.mk_Tm_app t_tup2 uu____2396))
in (uu____2391 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let emb_t_pair_a_b = (

let uu____2451 = (

let uu____2459 = (FStar_All.pipe_right FStar_Parser_Const.lid_tuple2 FStar_Ident.string_of_lid)
in ((uu____2459), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____2451))
in (

let printer = (fun uu____2475 -> (match (uu____2475) with
| (x, y) -> begin
(

let uu____2483 = (ea.print x)
in (

let uu____2485 = (eb.print y)
in (FStar_Util.format2 "(%s, %s)" uu____2483 uu____2485)))
end))
in (

let em = (fun x rng topt norm1 -> (lazy_embed printer emb_t_pair_a_b rng t_pair_a_b x (fun uu____2528 -> (

let proj = (fun i ab -> (

let uu____2544 = (

let uu____2549 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") rng)
in (

let uu____2551 = (FStar_Syntax_Syntax.null_bv FStar_Syntax_Syntax.tun)
in (FStar_Syntax_Util.mk_field_projector_name uu____2549 uu____2551 i)))
in (match (uu____2544) with
| (proj_1, uu____2555) -> begin
(

let proj_1_tm = (

let uu____2557 = (FStar_Syntax_Syntax.lid_as_fv proj_1 FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2557))
in (

let uu____2558 = (

let uu____2563 = (FStar_Syntax_Syntax.mk_Tm_uinst proj_1_tm ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____2564 = (

let uu____2565 = (

let uu____2574 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____2574))
in (

let uu____2575 = (

let uu____2586 = (

let uu____2595 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____2595))
in (

let uu____2596 = (

let uu____2607 = (FStar_Syntax_Syntax.as_arg ab)
in (uu____2607)::[])
in (uu____2586)::uu____2596))
in (uu____2565)::uu____2575))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2563 uu____2564)))
in (uu____2558 FStar_Pervasives_Native.None rng)))
end)))
in (

let shadow_a = (map_shadow topt (proj (Prims.parse_int "1")))
in (

let shadow_b = (map_shadow topt (proj (Prims.parse_int "2")))
in (

let uu____2652 = (

let uu____2657 = (

let uu____2658 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.lid_Mktuple2)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____2658 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____2659 = (

let uu____2660 = (

let uu____2669 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____2669))
in (

let uu____2670 = (

let uu____2681 = (

let uu____2690 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____2690))
in (

let uu____2691 = (

let uu____2702 = (

let uu____2711 = (

let uu____2712 = (embed ea (FStar_Pervasives_Native.fst x))
in (uu____2712 rng shadow_a norm1))
in (FStar_Syntax_Syntax.as_arg uu____2711))
in (

let uu____2719 = (

let uu____2730 = (

let uu____2739 = (

let uu____2740 = (embed eb (FStar_Pervasives_Native.snd x))
in (uu____2740 rng shadow_b norm1))
in (FStar_Syntax_Syntax.as_arg uu____2739))
in (uu____2730)::[])
in (uu____2702)::uu____2719))
in (uu____2681)::uu____2691))
in (uu____2660)::uu____2670))
in (FStar_Syntax_Syntax.mk_Tm_app uu____2657 uu____2659)))
in (uu____2652 FStar_Pervasives_Native.None rng))))))))
in (

let un = (fun t0 w norm1 -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed printer emb_t_pair_a_b t t_pair_a_b (fun t1 -> (

let uu____2838 = (FStar_Syntax_Util.head_and_args' t1)
in (match (uu____2838) with
| (hd1, args) -> begin
(

let uu____2881 = (

let uu____2894 = (

let uu____2895 = (FStar_Syntax_Util.un_uinst hd1)
in uu____2895.FStar_Syntax_Syntax.n)
in ((uu____2894), (args)))
in (match (uu____2881) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2913)::(uu____2914)::((a, uu____2916))::((b, uu____2918))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lid_Mktuple2) -> begin
(

let uu____2977 = (

let uu____2980 = (unembed ea a)
in (uu____2980 w norm1))
in (FStar_Util.bind_opt uu____2977 (fun a1 -> (

let uu____2994 = (

let uu____2997 = (unembed eb b)
in (uu____2997 w norm1))
in (FStar_Util.bind_opt uu____2994 (fun b1 -> FStar_Pervasives_Native.Some (((a1), (b1)))))))))
end
| uu____3014 -> begin
((match (w) with
| true -> begin
(

let uu____3029 = (

let uu____3035 = (

let uu____3037 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded pair: %s" uu____3037))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3035)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____3029))
end
| uu____3041 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))))
in (

let uu____3047 = (

let uu____3048 = (type_of ea)
in (

let uu____3049 = (type_of eb)
in (FStar_Syntax_Syntax.t_tuple2_of uu____3048 uu____3049)))
in (mk_emb_full em un uu____3047 printer emb_t_pair_a_b))))))))


let e_either : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a, 'b) FStar_Util.either embedding = (fun ea eb -> (

let t_sum_a_b = (

let t_either = (FStar_Syntax_Util.fvar_const FStar_Parser_Const.either_lid)
in (

let uu____3093 = (

let uu____3098 = (

let uu____3099 = (FStar_Syntax_Syntax.as_arg ea.typ)
in (

let uu____3108 = (

let uu____3119 = (FStar_Syntax_Syntax.as_arg eb.typ)
in (uu____3119)::[])
in (uu____3099)::uu____3108))
in (FStar_Syntax_Syntax.mk_Tm_app t_either uu____3098))
in (uu____3093 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let emb_t_sum_a_b = (

let uu____3153 = (

let uu____3161 = (FStar_All.pipe_right FStar_Parser_Const.either_lid FStar_Ident.string_of_lid)
in ((uu____3161), ((ea.emb_typ)::(eb.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____3153))
in (

let printer = (fun s -> (match (s) with
| FStar_Util.Inl (a) -> begin
(

let uu____3184 = (ea.print a)
in (FStar_Util.format1 "Inl %s" uu____3184))
end
| FStar_Util.Inr (b) -> begin
(

let uu____3188 = (eb.print b)
in (FStar_Util.format1 "Inr %s" uu____3188))
end))
in (

let em = (fun s rng topt norm1 -> (lazy_embed printer emb_t_sum_a_b rng t_sum_a_b s (match (s) with
| FStar_Util.Inl (a) -> begin
(fun uu____3234 -> (

let shadow_a = (map_shadow topt (fun t -> (

let v1 = (FStar_Ident.mk_ident (("v"), (rng)))
in (

let some_v = (FStar_Syntax_Util.mk_field_projector_name_from_ident FStar_Parser_Const.inl_lid v1)
in (

let some_v_tm = (

let uu____3247 = (FStar_Syntax_Syntax.lid_as_fv some_v FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3247))
in (

let uu____3248 = (

let uu____3253 = (FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____3254 = (

let uu____3255 = (

let uu____3264 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____3264))
in (

let uu____3265 = (

let uu____3276 = (

let uu____3285 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____3285))
in (

let uu____3286 = (

let uu____3297 = (FStar_Syntax_Syntax.as_arg t)
in (uu____3297)::[])
in (uu____3276)::uu____3286))
in (uu____3255)::uu____3265))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3253 uu____3254)))
in (uu____3248 FStar_Pervasives_Native.None rng)))))))
in (

let uu____3338 = (

let uu____3343 = (

let uu____3344 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.inl_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3344 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____3345 = (

let uu____3346 = (

let uu____3355 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____3355))
in (

let uu____3356 = (

let uu____3367 = (

let uu____3376 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____3376))
in (

let uu____3377 = (

let uu____3388 = (

let uu____3397 = (

let uu____3398 = (embed ea a)
in (uu____3398 rng shadow_a norm1))
in (FStar_Syntax_Syntax.as_arg uu____3397))
in (uu____3388)::[])
in (uu____3367)::uu____3377))
in (uu____3346)::uu____3356))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3343 uu____3345)))
in (uu____3338 FStar_Pervasives_Native.None rng))))
end
| FStar_Util.Inr (b) -> begin
(fun uu____3438 -> (

let shadow_b = (map_shadow topt (fun t -> (

let v1 = (FStar_Ident.mk_ident (("v"), (rng)))
in (

let some_v = (FStar_Syntax_Util.mk_field_projector_name_from_ident FStar_Parser_Const.inr_lid v1)
in (

let some_v_tm = (

let uu____3451 = (FStar_Syntax_Syntax.lid_as_fv some_v FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____3451))
in (

let uu____3452 = (

let uu____3457 = (FStar_Syntax_Syntax.mk_Tm_uinst some_v_tm ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____3458 = (

let uu____3459 = (

let uu____3468 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____3468))
in (

let uu____3469 = (

let uu____3480 = (

let uu____3489 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____3489))
in (

let uu____3490 = (

let uu____3501 = (FStar_Syntax_Syntax.as_arg t)
in (uu____3501)::[])
in (uu____3480)::uu____3490))
in (uu____3459)::uu____3469))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3457 uu____3458)))
in (uu____3452 FStar_Pervasives_Native.None rng)))))))
in (

let uu____3542 = (

let uu____3547 = (

let uu____3548 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.inr_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____3548 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (

let uu____3549 = (

let uu____3550 = (

let uu____3559 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____3559))
in (

let uu____3560 = (

let uu____3571 = (

let uu____3580 = (type_of eb)
in (FStar_Syntax_Syntax.iarg uu____3580))
in (

let uu____3581 = (

let uu____3592 = (

let uu____3601 = (

let uu____3602 = (embed eb b)
in (uu____3602 rng shadow_b norm1))
in (FStar_Syntax_Syntax.as_arg uu____3601))
in (uu____3592)::[])
in (uu____3571)::uu____3581))
in (uu____3550)::uu____3560))
in (FStar_Syntax_Syntax.mk_Tm_app uu____3547 uu____3549)))
in (uu____3542 FStar_Pervasives_Native.None rng))))
end)))
in (

let un = (fun t0 w norm1 -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed printer emb_t_sum_a_b t t_sum_a_b (fun t1 -> (

let uu____3690 = (FStar_Syntax_Util.head_and_args' t1)
in (match (uu____3690) with
| (hd1, args) -> begin
(

let uu____3733 = (

let uu____3748 = (

let uu____3749 = (FStar_Syntax_Util.un_uinst hd1)
in uu____3749.FStar_Syntax_Syntax.n)
in ((uu____3748), (args)))
in (match (uu____3733) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3769)::(uu____3770)::((a, uu____3772))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.inl_lid) -> begin
(

let uu____3839 = (

let uu____3842 = (unembed ea a)
in (uu____3842 w norm1))
in (FStar_Util.bind_opt uu____3839 (fun a1 -> FStar_Pervasives_Native.Some (FStar_Util.Inl (a1)))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3860)::(uu____3861)::((b, uu____3863))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.inr_lid) -> begin
(

let uu____3930 = (

let uu____3933 = (unembed eb b)
in (uu____3933 w norm1))
in (FStar_Util.bind_opt uu____3930 (fun b1 -> FStar_Pervasives_Native.Some (FStar_Util.Inr (b1)))))
end
| uu____3950 -> begin
((match (w) with
| true -> begin
(

let uu____3967 = (

let uu____3973 = (

let uu____3975 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded sum: %s" uu____3975))
in ((FStar_Errors.Warning_NotEmbedded), (uu____3973)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____3967))
end
| uu____3979 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))))
in (

let uu____3985 = (

let uu____3986 = (type_of ea)
in (

let uu____3987 = (type_of eb)
in (FStar_Syntax_Syntax.t_either_of uu____3986 uu____3987)))
in (mk_emb_full em un uu____3985 printer emb_t_sum_a_b))))))))


let e_list : 'a . 'a embedding  ->  'a Prims.list embedding = (fun ea -> (

let t_list_a = (

let t_list = (FStar_Syntax_Util.fvar_const FStar_Parser_Const.list_lid)
in (

let uu____4015 = (

let uu____4020 = (

let uu____4021 = (FStar_Syntax_Syntax.as_arg ea.typ)
in (uu____4021)::[])
in (FStar_Syntax_Syntax.mk_Tm_app t_list uu____4020))
in (uu____4015 FStar_Pervasives_Native.None FStar_Range.dummyRange)))
in (

let emb_t_list_a = (

let uu____4047 = (

let uu____4055 = (FStar_All.pipe_right FStar_Parser_Const.list_lid FStar_Ident.string_of_lid)
in ((uu____4055), ((ea.emb_typ)::[])))
in FStar_Syntax_Syntax.ET_app (uu____4047))
in (

let printer = (fun l -> (

let uu____4072 = (

let uu____4074 = (

let uu____4076 = (FStar_List.map ea.print l)
in (FStar_All.pipe_right uu____4076 (FStar_String.concat "; ")))
in (Prims.op_Hat uu____4074 "]"))
in (Prims.op_Hat "[" uu____4072)))
in (

let rec em = (fun l rng shadow_l norm1 -> (lazy_embed printer emb_t_list_a rng t_list_a l (fun uu____4120 -> (

let t = (

let uu____4122 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____4122))
in (match (l) with
| [] -> begin
(

let uu____4123 = (

let uu____4128 = (

let uu____4129 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.nil_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4129 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4128 ((t)::[])))
in (uu____4123 FStar_Pervasives_Native.None rng))
end
| (hd1)::tl1 -> begin
(

let cons1 = (

let uu____4151 = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.cons_lid)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____4151 ((FStar_Syntax_Syntax.U_zero)::[])))
in (

let proj = (fun f cons_tm -> (

let fid = (FStar_Ident.mk_ident ((f), (rng)))
in (

let proj = (FStar_Syntax_Util.mk_field_projector_name_from_ident FStar_Parser_Const.cons_lid fid)
in (

let proj_tm = (

let uu____4171 = (FStar_Syntax_Syntax.lid_as_fv proj FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____4171))
in (

let uu____4172 = (

let uu____4177 = (FStar_Syntax_Syntax.mk_Tm_uinst proj_tm ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let uu____4178 = (

let uu____4179 = (

let uu____4188 = (type_of ea)
in (FStar_Syntax_Syntax.iarg uu____4188))
in (

let uu____4189 = (

let uu____4200 = (FStar_Syntax_Syntax.as_arg cons_tm)
in (uu____4200)::[])
in (uu____4179)::uu____4189))
in (FStar_Syntax_Syntax.mk_Tm_app uu____4177 uu____4178)))
in (uu____4172 FStar_Pervasives_Native.None rng))))))
in (

let shadow_hd = (map_shadow shadow_l (proj "hd"))
in (

let shadow_tl = (map_shadow shadow_l (proj "tl"))
in (

let uu____4237 = (

let uu____4242 = (

let uu____4243 = (

let uu____4254 = (

let uu____4263 = (

let uu____4264 = (embed ea hd1)
in (uu____4264 rng shadow_hd norm1))
in (FStar_Syntax_Syntax.as_arg uu____4263))
in (

let uu____4271 = (

let uu____4282 = (

let uu____4291 = (em tl1 rng shadow_tl norm1)
in (FStar_Syntax_Syntax.as_arg uu____4291))
in (uu____4282)::[])
in (uu____4254)::uu____4271))
in (t)::uu____4243)
in (FStar_Syntax_Syntax.mk_Tm_app cons1 uu____4242))
in (uu____4237 FStar_Pervasives_Native.None rng))))))
end)))))
in (

let rec un = (fun t0 w norm1 -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed printer emb_t_list_a t t_list_a (fun t1 -> (

let uu____4363 = (FStar_Syntax_Util.head_and_args' t1)
in (match (uu____4363) with
| (hd1, args) -> begin
(

let uu____4404 = (

let uu____4417 = (

let uu____4418 = (FStar_Syntax_Util.un_uinst hd1)
in uu____4418.FStar_Syntax_Syntax.n)
in ((uu____4417), (args)))
in (match (uu____4404) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____4434) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
FStar_Pervasives_Native.Some ([])
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____4454, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____4455))))::((hd2, FStar_Pervasives_Native.None))::((tl1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____4497 = (

let uu____4500 = (unembed ea hd2)
in (uu____4500 w norm1))
in (FStar_Util.bind_opt uu____4497 (fun hd3 -> (

let uu____4512 = (un tl1 w norm1)
in (FStar_Util.bind_opt uu____4512 (fun tl2 -> FStar_Pervasives_Native.Some ((hd3)::tl2)))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((hd2, FStar_Pervasives_Native.None))::((tl1, FStar_Pervasives_Native.None))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid) -> begin
(

let uu____4560 = (

let uu____4563 = (unembed ea hd2)
in (uu____4563 w norm1))
in (FStar_Util.bind_opt uu____4560 (fun hd3 -> (

let uu____4575 = (un tl1 w norm1)
in (FStar_Util.bind_opt uu____4575 (fun tl2 -> FStar_Pervasives_Native.Some ((hd3)::tl2)))))))
end
| uu____4590 -> begin
((match (w) with
| true -> begin
(

let uu____4605 = (

let uu____4611 = (

let uu____4613 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded list: %s" uu____4613))
in ((FStar_Errors.Warning_NotEmbedded), (uu____4611)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____4605))
end
| uu____4617 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))))
in (

let uu____4621 = (

let uu____4622 = (type_of ea)
in (FStar_Syntax_Syntax.t_list_of uu____4622))
in (mk_emb_full em un uu____4621 printer emb_t_list_a))))))))


let e_string_list : Prims.string Prims.list embedding = (e_list e_string)

type norm_step =
| Simpl
| Weak
| HNF
| Primops
| Delta
| Zeta
| Iota
| Reify
| UnfoldOnly of Prims.string Prims.list
| UnfoldFully of Prims.string Prims.list
| UnfoldAttr of Prims.string Prims.list
| NBE


let uu___is_Simpl : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Simpl -> begin
true
end
| uu____4665 -> begin
false
end))


let uu___is_Weak : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Weak -> begin
true
end
| uu____4676 -> begin
false
end))


let uu___is_HNF : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| HNF -> begin
true
end
| uu____4687 -> begin
false
end))


let uu___is_Primops : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Primops -> begin
true
end
| uu____4698 -> begin
false
end))


let uu___is_Delta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Delta -> begin
true
end
| uu____4709 -> begin
false
end))


let uu___is_Zeta : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Zeta -> begin
true
end
| uu____4720 -> begin
false
end))


let uu___is_Iota : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Iota -> begin
true
end
| uu____4731 -> begin
false
end))


let uu___is_Reify : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Reify -> begin
true
end
| uu____4742 -> begin
false
end))


let uu___is_UnfoldOnly : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
true
end
| uu____4757 -> begin
false
end))


let __proj__UnfoldOnly__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldOnly (_0) -> begin
_0
end))


let uu___is_UnfoldFully : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
true
end
| uu____4788 -> begin
false
end))


let __proj__UnfoldFully__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldFully (_0) -> begin
_0
end))


let uu___is_UnfoldAttr : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
true
end
| uu____4819 -> begin
false
end))


let __proj__UnfoldAttr__item___0 : norm_step  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| UnfoldAttr (_0) -> begin
_0
end))


let uu___is_NBE : norm_step  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NBE -> begin
true
end
| uu____4846 -> begin
false
end))


let steps_Simpl : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_simpl)


let steps_Weak : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_weak)


let steps_HNF : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_hnf)


let steps_Primops : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_primops)


let steps_Delta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_delta)


let steps_Zeta : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_zeta)


let steps_Iota : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_iota)


let steps_Reify : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_reify)


let steps_UnfoldOnly : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly)


let steps_UnfoldFully : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldonly)


let steps_UnfoldAttr : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_unfoldattr)


let steps_NBE : FStar_Syntax_Syntax.term = (FStar_Syntax_Syntax.tdataconstr FStar_Parser_Const.steps_nbe)


let e_norm_step : norm_step embedding = (

let t_norm_step1 = (

let uu____4864 = (FStar_Ident.lid_of_str "FStar.Syntax.Embeddings.norm_step")
in (FStar_Syntax_Util.fvar_const uu____4864))
in (

let emb_t_norm_step = (

let uu____4867 = (

let uu____4875 = (FStar_All.pipe_right FStar_Parser_Const.norm_step_lid FStar_Ident.string_of_lid)
in ((uu____4875), ([])))
in FStar_Syntax_Syntax.ET_app (uu____4867))
in (

let printer = (fun uu____4887 -> "norm_step")
in (

let em = (fun n1 rng _topt norm1 -> (lazy_embed printer emb_t_norm_step rng t_norm_step1 n1 (fun uu____4913 -> (match (n1) with
| Simpl -> begin
steps_Simpl
end
| Weak -> begin
steps_Weak
end
| HNF -> begin
steps_HNF
end
| Primops -> begin
steps_Primops
end
| Delta -> begin
steps_Delta
end
| Zeta -> begin
steps_Zeta
end
| Iota -> begin
steps_Iota
end
| NBE -> begin
steps_NBE
end
| Reify -> begin
steps_Reify
end
| UnfoldOnly (l) -> begin
(

let uu____4918 = (

let uu____4923 = (

let uu____4924 = (

let uu____4933 = (

let uu____4934 = (

let uu____4941 = (e_list e_string)
in (embed uu____4941 l))
in (uu____4934 rng FStar_Pervasives_Native.None norm1))
in (FStar_Syntax_Syntax.as_arg uu____4933))
in (uu____4924)::[])
in (FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldOnly uu____4923))
in (uu____4918 FStar_Pervasives_Native.None rng))
end
| UnfoldFully (l) -> begin
(

let uu____4973 = (

let uu____4978 = (

let uu____4979 = (

let uu____4988 = (

let uu____4989 = (

let uu____4996 = (e_list e_string)
in (embed uu____4996 l))
in (uu____4989 rng FStar_Pervasives_Native.None norm1))
in (FStar_Syntax_Syntax.as_arg uu____4988))
in (uu____4979)::[])
in (FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldFully uu____4978))
in (uu____4973 FStar_Pervasives_Native.None rng))
end
| UnfoldAttr (l) -> begin
(

let uu____5028 = (

let uu____5033 = (

let uu____5034 = (

let uu____5043 = (

let uu____5044 = (

let uu____5051 = (e_list e_string)
in (embed uu____5051 l))
in (uu____5044 rng FStar_Pervasives_Native.None norm1))
in (FStar_Syntax_Syntax.as_arg uu____5043))
in (uu____5034)::[])
in (FStar_Syntax_Syntax.mk_Tm_app steps_UnfoldAttr uu____5033))
in (uu____5028 FStar_Pervasives_Native.None rng))
end))))
in (

let un = (fun t0 w norm1 -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (lazy_unembed printer emb_t_norm_step t t_norm_step1 (fun t1 -> (

let uu____5111 = (FStar_Syntax_Util.head_and_args t1)
in (match (uu____5111) with
| (hd1, args) -> begin
(

let uu____5156 = (

let uu____5171 = (

let uu____5172 = (FStar_Syntax_Util.un_uinst hd1)
in uu____5172.FStar_Syntax_Syntax.n)
in ((uu____5171), (args)))
in (match (uu____5156) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl) -> begin
FStar_Pervasives_Native.Some (Simpl)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak) -> begin
FStar_Pervasives_Native.Some (Weak)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf) -> begin
FStar_Pervasives_Native.Some (HNF)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops) -> begin
FStar_Pervasives_Native.Some (Primops)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta) -> begin
FStar_Pervasives_Native.Some (Delta)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta) -> begin
FStar_Pervasives_Native.Some (Zeta)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota) -> begin
FStar_Pervasives_Native.Some (Iota)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe) -> begin
FStar_Pervasives_Native.Some (NBE)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify) -> begin
FStar_Pervasives_Native.Some (Reify)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____5360))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly) -> begin
(

let uu____5395 = (

let uu____5401 = (

let uu____5411 = (e_list e_string)
in (unembed uu____5411 l))
in (uu____5401 w norm1))
in (FStar_Util.bind_opt uu____5395 (fun ss -> (FStar_All.pipe_left (fun _5431 -> FStar_Pervasives_Native.Some (_5431)) (UnfoldOnly (ss))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____5434))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully) -> begin
(

let uu____5469 = (

let uu____5475 = (

let uu____5485 = (e_list e_string)
in (unembed uu____5485 l))
in (uu____5475 w norm1))
in (FStar_Util.bind_opt uu____5469 (fun ss -> (FStar_All.pipe_left (fun _5505 -> FStar_Pervasives_Native.Some (_5505)) (UnfoldFully (ss))))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((l, uu____5508))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr) -> begin
(

let uu____5543 = (

let uu____5549 = (

let uu____5559 = (e_list e_string)
in (unembed uu____5559 l))
in (uu____5549 w norm1))
in (FStar_Util.bind_opt uu____5543 (fun ss -> (FStar_All.pipe_left (fun _5579 -> FStar_Pervasives_Native.Some (_5579)) (UnfoldAttr (ss))))))
end
| uu____5580 -> begin
((match (w) with
| true -> begin
(

let uu____5597 = (

let uu____5603 = (

let uu____5605 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded norm_step: %s" uu____5605))
in ((FStar_Errors.Warning_NotEmbedded), (uu____5603)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5597))
end
| uu____5609 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end))))))
in (mk_emb_full em un FStar_Syntax_Syntax.t_norm_step printer emb_t_norm_step))))))


let e_range : FStar_Range.range embedding = (

let em = (fun r rng _shadow _norm -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r))) FStar_Pervasives_Native.None rng))
in (

let un = (fun t0 w _norm -> (

let t = (FStar_Syntax_Util.unmeta_safe t0)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)) -> begin
FStar_Pervasives_Native.Some (r)
end
| uu____5665 -> begin
((match (w) with
| true -> begin
(

let uu____5668 = (

let uu____5674 = (

let uu____5676 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Not an embedded range: %s" uu____5676))
in ((FStar_Errors.Warning_NotEmbedded), (uu____5674)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____5668))
end
| uu____5680 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end)))
in (

let uu____5682 = (

let uu____5683 = (

let uu____5691 = (FStar_All.pipe_right FStar_Parser_Const.range_lid FStar_Ident.string_of_lid)
in ((uu____5691), ([])))
in FStar_Syntax_Syntax.ET_app (uu____5683))
in (mk_emb_full em un FStar_Syntax_Syntax.t_range FStar_Range.string_of_range uu____5682))))


let or_else : 'a . 'a FStar_Pervasives_Native.option  ->  (unit  ->  'a)  ->  'a = (fun f g -> (match (f) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(g ())
end))


let e_arrow : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b) embedding = (fun ea eb -> (

let t_arrow = (

let uu____5762 = (

let uu____5769 = (

let uu____5770 = (

let uu____5785 = (

let uu____5794 = (

let uu____5801 = (FStar_Syntax_Syntax.null_bv ea.typ)
in ((uu____5801), (FStar_Pervasives_Native.None)))
in (uu____5794)::[])
in (

let uu____5816 = (FStar_Syntax_Syntax.mk_Total eb.typ)
in ((uu____5785), (uu____5816))))
in FStar_Syntax_Syntax.Tm_arrow (uu____5770))
in (FStar_Syntax_Syntax.mk uu____5769))
in (uu____5762 FStar_Pervasives_Native.None FStar_Range.dummyRange))
in (

let emb_t_arr_a_b = FStar_Syntax_Syntax.ET_fun (((ea.emb_typ), (eb.emb_typ)))
in (

let printer = (fun f -> "<fun>")
in (

let em = (fun f rng shadow_f norm1 -> (lazy_embed (fun uu____5888 -> "<fun>") emb_t_arr_a_b rng t_arrow f (fun uu____5894 -> (

let uu____5895 = (force_shadow shadow_f)
in (match (uu____5895) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise Embedding_failure)
end
| FStar_Pervasives_Native.Some (repr_f) -> begin
((

let uu____5900 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____5900) with
| true -> begin
(

let uu____5924 = (FStar_Syntax_Print.term_to_string repr_f)
in (

let uu____5926 = (FStar_Util.stack_dump ())
in (FStar_Util.print2 "e_arrow forced back to term using shadow %s; repr=%s\n" uu____5924 uu____5926)))
end
| uu____5929 -> begin
()
end));
(

let res = (norm1 (FStar_Util.Inr (repr_f)))
in ((

let uu____5933 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____5933) with
| true -> begin
(

let uu____5957 = (FStar_Syntax_Print.term_to_string repr_f)
in (

let uu____5959 = (FStar_Syntax_Print.term_to_string res)
in (

let uu____5961 = (FStar_Util.stack_dump ())
in (FStar_Util.print3 "e_arrow forced back to term using shadow %s; repr=%s\n\t%s\n" uu____5957 uu____5959 uu____5961))))
end
| uu____5964 -> begin
()
end));
res;
));
)
end)))))
in (

let un = (fun f w norm1 -> (lazy_unembed printer emb_t_arr_a_b f t_arrow (fun f1 -> (

let f_wrapped = (fun a -> ((

let uu____6020 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____6020) with
| true -> begin
(

let uu____6044 = (FStar_Syntax_Print.term_to_string f1)
in (

let uu____6046 = (FStar_Util.stack_dump ())
in (FStar_Util.print2 "Calling back into normalizer for %s\n%s\n" uu____6044 uu____6046)))
end
| uu____6049 -> begin
()
end));
(

let a_tm = (

let uu____6052 = (embed ea a)
in (uu____6052 f1.FStar_Syntax_Syntax.pos FStar_Pervasives_Native.None norm1))
in (

let b_tm = (

let uu____6062 = (

let uu____6067 = (

let uu____6068 = (

let uu____6073 = (

let uu____6074 = (FStar_Syntax_Syntax.as_arg a_tm)
in (uu____6074)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f1 uu____6073))
in (uu____6068 FStar_Pervasives_Native.None f1.FStar_Syntax_Syntax.pos))
in FStar_Util.Inr (uu____6067))
in (norm1 uu____6062))
in (

let uu____6099 = (

let uu____6102 = (unembed eb b_tm)
in (uu____6102 w norm1))
in (match (uu____6099) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise Unembedding_failure)
end
| FStar_Pervasives_Native.Some (b) -> begin
b
end))));
))
in FStar_Pervasives_Native.Some (f_wrapped)))))
in (mk_emb_full em un t_arrow printer emb_t_arr_a_b)))))))


let arrow_as_prim_step_1 : 'a 'b . 'a embedding  ->  'b embedding  ->  ('a  ->  'b)  ->  Prims.int  ->  FStar_Ident.lid  ->  norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ea eb f n_tvars fv_lid1 norm1 -> (

let rng = (FStar_Ident.range_of_lid fv_lid1)
in (

let f_wrapped = (fun args -> (

let uu____6196 = (FStar_List.splitAt n_tvars args)
in (match (uu____6196) with
| (_tvar_args, rest_args) -> begin
(

let uu____6273 = (FStar_List.hd rest_args)
in (match (uu____6273) with
| (x, uu____6293) -> begin
(

let shadow_app = (

let uu____6307 = (FStar_Thunk.mk (fun uu____6314 -> (

let uu____6315 = (

let uu____6320 = (norm1 (FStar_Util.Inl (fv_lid1)))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6320 args))
in (uu____6315 FStar_Pervasives_Native.None rng))))
in FStar_Pervasives_Native.Some (uu____6307))
in (

let uu____6323 = (

let uu____6326 = (

let uu____6329 = (unembed ea x)
in (uu____6329 true norm1))
in (FStar_Util.map_opt uu____6326 (fun x1 -> (

let uu____6340 = (

let uu____6347 = (f x1)
in (embed eb uu____6347))
in (uu____6340 rng shadow_app norm1)))))
in (match (uu____6323) with
| FStar_Pervasives_Native.Some (x1) -> begin
FStar_Pervasives_Native.Some (x1)
end
| FStar_Pervasives_Native.None -> begin
(force_shadow shadow_app)
end)))
end))
end)))
in f_wrapped)))


let arrow_as_prim_step_2 : 'a 'b 'c . 'a embedding  ->  'b embedding  ->  'c embedding  ->  ('a  ->  'b  ->  'c)  ->  Prims.int  ->  FStar_Ident.lid  ->  norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ea eb ec f n_tvars fv_lid1 norm1 -> (

let rng = (FStar_Ident.range_of_lid fv_lid1)
in (

let f_wrapped = (fun args -> (

let uu____6450 = (FStar_List.splitAt n_tvars args)
in (match (uu____6450) with
| (_tvar_args, rest_args) -> begin
(

let uu____6513 = (FStar_List.hd rest_args)
in (match (uu____6513) with
| (x, uu____6529) -> begin
(

let uu____6534 = (

let uu____6541 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____6541))
in (match (uu____6534) with
| (y, uu____6565) -> begin
(

let shadow_app = (

let uu____6575 = (FStar_Thunk.mk (fun uu____6582 -> (

let uu____6583 = (

let uu____6588 = (norm1 (FStar_Util.Inl (fv_lid1)))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6588 args))
in (uu____6583 FStar_Pervasives_Native.None rng))))
in FStar_Pervasives_Native.Some (uu____6575))
in (

let uu____6591 = (

let uu____6594 = (

let uu____6597 = (unembed ea x)
in (uu____6597 true norm1))
in (FStar_Util.bind_opt uu____6594 (fun x1 -> (

let uu____6608 = (

let uu____6611 = (unembed eb y)
in (uu____6611 true norm1))
in (FStar_Util.bind_opt uu____6608 (fun y1 -> (

let uu____6622 = (

let uu____6623 = (

let uu____6630 = (f x1 y1)
in (embed ec uu____6630))
in (uu____6623 rng shadow_app norm1))
in FStar_Pervasives_Native.Some (uu____6622))))))))
in (match (uu____6591) with
| FStar_Pervasives_Native.Some (x1) -> begin
FStar_Pervasives_Native.Some (x1)
end
| FStar_Pervasives_Native.None -> begin
(force_shadow shadow_app)
end)))
end))
end))
end)))
in f_wrapped)))


let arrow_as_prim_step_3 : 'a 'b 'c 'd . 'a embedding  ->  'b embedding  ->  'c embedding  ->  'd embedding  ->  ('a  ->  'b  ->  'c  ->  'd)  ->  Prims.int  ->  FStar_Ident.lid  ->  norm_cb  ->  FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun ea eb ec ed f n_tvars fv_lid1 norm1 -> (

let rng = (FStar_Ident.range_of_lid fv_lid1)
in (

let f_wrapped = (fun args -> (

let uu____6752 = (FStar_List.splitAt n_tvars args)
in (match (uu____6752) with
| (_tvar_args, rest_args) -> begin
(

let uu____6815 = (FStar_List.hd rest_args)
in (match (uu____6815) with
| (x, uu____6831) -> begin
(

let uu____6836 = (

let uu____6843 = (FStar_List.tl rest_args)
in (FStar_List.hd uu____6843))
in (match (uu____6836) with
| (y, uu____6867) -> begin
(

let uu____6872 = (

let uu____6879 = (

let uu____6888 = (FStar_List.tl rest_args)
in (FStar_List.tl uu____6888))
in (FStar_List.hd uu____6879))
in (match (uu____6872) with
| (z, uu____6918) -> begin
(

let shadow_app = (

let uu____6928 = (FStar_Thunk.mk (fun uu____6935 -> (

let uu____6936 = (

let uu____6941 = (norm1 (FStar_Util.Inl (fv_lid1)))
in (FStar_Syntax_Syntax.mk_Tm_app uu____6941 args))
in (uu____6936 FStar_Pervasives_Native.None rng))))
in FStar_Pervasives_Native.Some (uu____6928))
in (

let uu____6944 = (

let uu____6947 = (

let uu____6950 = (unembed ea x)
in (uu____6950 true norm1))
in (FStar_Util.bind_opt uu____6947 (fun x1 -> (

let uu____6961 = (

let uu____6964 = (unembed eb y)
in (uu____6964 true norm1))
in (FStar_Util.bind_opt uu____6961 (fun y1 -> (

let uu____6975 = (

let uu____6978 = (unembed ec z)
in (uu____6978 true norm1))
in (FStar_Util.bind_opt uu____6975 (fun z1 -> (

let uu____6989 = (

let uu____6990 = (

let uu____6997 = (f x1 y1 z1)
in (embed ed uu____6997))
in (uu____6990 rng shadow_app norm1))
in FStar_Pervasives_Native.Some (uu____6989)))))))))))
in (match (uu____6944) with
| FStar_Pervasives_Native.Some (x1) -> begin
FStar_Pervasives_Native.Some (x1)
end
| FStar_Pervasives_Native.None -> begin
(force_shadow shadow_app)
end)))
end))
end))
end))
end)))
in f_wrapped)))


let debug_wrap : 'a . Prims.string  ->  (unit  ->  'a)  ->  'a = (fun s f -> ((

let uu____7027 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____7027) with
| true -> begin
(FStar_Util.print1 "++++starting %s\n" s)
end
| uu____7052 -> begin
()
end));
(

let res = (f ())
in ((

let uu____7056 = (FStar_ST.op_Bang FStar_Options.debug_embedding)
in (match (uu____7056) with
| true -> begin
(FStar_Util.print1 "------ending %s\n" s)
end
| uu____7081 -> begin
()
end));
res;
));
))





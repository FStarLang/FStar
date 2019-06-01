
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___0_5 -> (match (uu___0_5) with
| FStar_Syntax_Syntax.Delta_constant_at_level (i) -> begin
(

let uu____9 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "Delta_constant_at_level " uu____9))
end
| FStar_Syntax_Syntax.Delta_equational_at_level (i) -> begin
(

let uu____14 = (FStar_Util.string_of_int i)
in (Prims.op_Hat "Delta_equational_at_level " uu____14))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(

let uu____18 = (

let uu____20 = (delta_depth_to_string d)
in (Prims.op_Hat uu____20 ")"))
in (Prims.op_Hat "Delta_abstract (" uu____18))
end))


let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____32 = (FStar_Options.print_real_names ())
in (match (uu____32) with
| true -> begin
l.FStar_Ident.str
end
| uu____36 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____59 = (

let uu____61 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.op_Hat "#" uu____61))
in (Prims.op_Hat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____59)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____71 = (FStar_Options.print_real_names ())
in (match (uu____71) with
| true -> begin
(bv_to_string bv)
end
| uu____75 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____84 = (

let uu____86 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.op_Hat "@" uu____86))
in (Prims.op_Hat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____84)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____308 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____321 -> begin
(failwith "get_lid")
end))


let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e))


let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e))


let quants : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::[]


type exp =
FStar_Syntax_Syntax.term


let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Parser_Const.b2t_lid)::[]) t))


let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t))


let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Parser_Const.ite_lid)::[]) t))


let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Parser_Const.lexcons_lid)::[]) f))


let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Parser_Const.lextop_lid)::[]) f))


let is_inr : 'Auu____424 'Auu____425 . ('Auu____424, 'Auu____425) FStar_Util.either  ->  Prims.bool = (fun uu___1_435 -> (match (uu___1_435) with
| FStar_Util.Inl (uu____440) -> begin
false
end
| FStar_Util.Inr (uu____442) -> begin
true
end))


let filter_imp : 'Auu____449 . ('Auu____449 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____449 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___2_504 -> (match (uu___2_504) with
| (uu____512, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t))) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
true
end
| (uu____519, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____520))) -> begin
false
end
| (uu____525, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____526))) -> begin
false
end
| uu____532 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  exp Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____550 = (

let uu____551 = (FStar_Syntax_Subst.compress e)
in uu____551.FStar_Syntax_Syntax.n)
in (match (uu____550) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____612 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____612) with
| true -> begin
(

let uu____621 = (

let uu____626 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____626))
in (match (uu____621) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____637 = (

let uu____640 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____640)::xs)
in FStar_Pervasives_Native.Some (uu____637))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____648 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____652 -> begin
(

let uu____653 = (is_lex_top e)
in (match (uu____653) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____662 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____701 = (f hd1)
in (match (uu____701) with
| true -> begin
hd1
end
| uu____704 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____733 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____733)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____764 = (get_lid e)
in (find_lid uu____764 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____776 = (get_lid e)
in (find_lid uu____776 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____788 = (get_lid t)
in (find_lid uu____788 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___3_802 -> (match (uu___3_802) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____813 = (FStar_Options.hide_uvar_nums ())
in (match (uu____813) with
| true -> begin
"?"
end
| uu____818 -> begin
(

let uu____820 = (

let uu____822 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____822 FStar_Util.string_of_int))
in (Prims.op_Hat "?" uu____820))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____834 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____836 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____834 uu____836))))


let univ_uvar_to_string : (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version)  ->  Prims.string = (fun u -> (

let uu____862 = (FStar_Options.hide_uvar_nums ())
in (match (uu____862) with
| true -> begin
"?"
end
| uu____867 -> begin
(

let uu____869 = (

let uu____871 = (

let uu____873 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____873 FStar_Util.string_of_int))
in (

let uu____877 = (

let uu____879 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.op_Hat ":" uu____879))
in (Prims.op_Hat uu____871 uu____877)))
in (Prims.op_Hat "?" uu____869))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____907 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____907) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____920 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____931 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____931) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(

let uu____942 = (univ_uvar_to_string u1)
in (Prims.op_Hat "U_unif " uu____942))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.op_Hat "U_name " x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____949 = (FStar_Util.string_of_int x)
in (Prims.op_Hat "@" uu____949))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____954 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____954) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____975 = (univ_to_string u2)
in (

let uu____977 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____975 uu____977)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____983 = (

let uu____985 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____985 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____983))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universes  ->  Prims.string = (fun us -> (

let uu____1004 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____1004 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____1021 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____1021 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___4_1039 -> (match (uu___4_1039) with
| FStar_Syntax_Syntax.Assumption -> begin
"assume"
end
| FStar_Syntax_Syntax.New -> begin
"new"
end
| FStar_Syntax_Syntax.Private -> begin
"private"
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
"unfold"
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
"inline"
end
| FStar_Syntax_Syntax.NoExtract -> begin
"noextract"
end
| FStar_Syntax_Syntax.Visible_default -> begin
"visible"
end
| FStar_Syntax_Syntax.Irreducible -> begin
"irreducible"
end
| FStar_Syntax_Syntax.Abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.Noeq -> begin
"noeq"
end
| FStar_Syntax_Syntax.Unopteq -> begin
"unopteq"
end
| FStar_Syntax_Syntax.Logic -> begin
"logic"
end
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(

let uu____1055 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____1055))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____1060 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____1060 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____1073 = (

let uu____1075 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1075))
in (

let uu____1076 = (

let uu____1078 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1078 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____1073 uu____1076)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____1104 = (

let uu____1106 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1106))
in (

let uu____1107 = (

let uu____1109 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1109 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____1104 uu____1107)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____1126 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____1126))
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
"ExceptionConstructor"
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
"HasMaskedEffect"
end
| FStar_Syntax_Syntax.Effect -> begin
"Effect"
end
| FStar_Syntax_Syntax.Reifiable -> begin
"reify"
end
| FStar_Syntax_Syntax.Reflectable (l) -> begin
(FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str)
end
| FStar_Syntax_Syntax.OnlyName -> begin
"OnlyName"
end))


let quals_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____1149 -> begin
(

let uu____1152 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____1152 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____1180 -> begin
(

let uu____1183 = (quals_to_string quals)
in (Prims.op_Hat uu____1183 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.op_Hat "(" (Prims.op_Hat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1379 = (db_to_string x)
in (Prims.op_Hat "Tm_bvar: " uu____1379))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____1383 = (nm_to_string x)
in (Prims.op_Hat "Tm_name: " uu____1383))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____1387 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.op_Hat "Tm_fvar: " uu____1387))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1390) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____1398) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____1400) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1402, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1403}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1417, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1418}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1432) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1452) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1468) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1476) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1494) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1518) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1546) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1561) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1575, m) -> begin
(

let uu____1613 = (FStar_ST.op_Bang m)
in (match (uu____1613) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1649) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1655, m) -> begin
(

let uu____1661 = (metadata_to_string m)
in (Prims.op_Hat "Tm_meta:" uu____1661))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1665) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1668 = (

let uu____1670 = (FStar_Options.ugly ())
in (not (uu____1670)))
in (match (uu____1668) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1678 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1684 = (FStar_Options.print_implicits ())
in (match (uu____1684) with
| true -> begin
x1
end
| uu____1689 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1692) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1717, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____1743, thunk1); FStar_Syntax_Syntax.ltyp = uu____1745; FStar_Syntax_Syntax.rng = uu____1746}) -> begin
(

let uu____1757 = (

let uu____1759 = (

let uu____1761 = (FStar_Common.force_thunk thunk1)
in (term_to_string uu____1761))
in (Prims.op_Hat uu____1759 "]"))
in (Prims.op_Hat "[LAZYEMB:" uu____1757))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1767 = (

let uu____1769 = (

let uu____1771 = (

let uu____1772 = (

let uu____1781 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1781))
in (uu____1772 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1771))
in (Prims.op_Hat uu____1769 "]"))
in (Prims.op_Hat "[lazy:" uu____1767))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
(

let print_aq = (fun uu____1850 -> (match (uu____1850) with
| (bv, t) -> begin
(

let uu____1858 = (bv_to_string bv)
in (

let uu____1860 = (term_to_string t)
in (FStar_Util.format2 "%s -> %s" uu____1858 uu____1860)))
end))
in (

let uu____1863 = (term_to_string tm)
in (

let uu____1865 = (FStar_Common.string_of_list print_aq qi.FStar_Syntax_Syntax.antiquotes)
in (FStar_Util.format2 "`(%s)%s" uu____1863 uu____1865))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____1874 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1874))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (uu____1878, ps)) -> begin
(

let pats = (

let uu____1918 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1955 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1980 -> (match (uu____1980) with
| (t1, uu____1989) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1955 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1918 (FStar_String.concat "\\/")))
in (

let uu____2004 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____2004)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____2018 = (tag_of_term t)
in (

let uu____2020 = (sli m)
in (

let uu____2022 = (term_to_string t')
in (

let uu____2024 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2018 uu____2020 uu____2022 uu____2024)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____2039 = (tag_of_term t)
in (

let uu____2041 = (term_to_string t')
in (

let uu____2043 = (sli m0)
in (

let uu____2045 = (sli m1)
in (

let uu____2047 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2039 uu____2041 uu____2043 uu____2045 uu____2047))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____2062 = (FStar_Range.string_of_range r)
in (

let uu____2064 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2062 uu____2064)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____2073 = (lid_to_string l)
in (

let uu____2075 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2077 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2073 uu____2075 uu____2077))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____2081)) -> begin
(

let uu____2086 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____2086))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____2090 = (db_to_string x3)
in (

let uu____2092 = (

let uu____2094 = (

let uu____2096 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.op_Hat uu____2096 ")"))
in (Prims.op_Hat ":(" uu____2094))
in (Prims.op_Hat uu____2090 uu____2092)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____2103)) -> begin
(

let uu____2118 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____2118) with
| true -> begin
(ctx_uvar_to_string u)
end
| uu____2122 -> begin
(

let uu____2124 = (

let uu____2126 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2126))
in (Prims.op_Hat "?" uu____2124))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____2149 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____2149) with
| true -> begin
(

let uu____2153 = (ctx_uvar_to_string u)
in (

let uu____2155 = (

let uu____2157 = (FStar_List.map subst_to_string (FStar_Pervasives_Native.fst s))
in (FStar_All.pipe_right uu____2157 (FStar_String.concat "; ")))
in (FStar_Util.format2 "(%s @ %s)" uu____2153 uu____2155)))
end
| uu____2174 -> begin
(

let uu____2176 = (

let uu____2178 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2178))
in (Prims.op_Hat "?" uu____2176))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____2185 = (FStar_Options.print_universes ())
in (match (uu____2185) with
| true -> begin
(

let uu____2189 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____2189))
end
| uu____2192 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2217 = (binders_to_string " -> " bs)
in (

let uu____2220 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____2217 uu____2220)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____2252 = (binders_to_string " " bs)
in (

let uu____2255 = (term_to_string t2)
in (

let uu____2257 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____2264 -> begin
(

let uu____2266 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____2266))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____2252 uu____2255 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____2257))))
end
| uu____2270 -> begin
(

let uu____2273 = (binders_to_string " " bs)
in (

let uu____2276 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____2273 uu____2276)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____2285 = (bv_to_string xt)
in (

let uu____2287 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____2290 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____2285 uu____2287 uu____2290))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____2322 = (term_to_string t)
in (

let uu____2324 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____2322 uu____2324)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____2347 = (lbs_to_string [] lbs)
in (

let uu____2349 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____2347 uu____2349)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____2414 = (

let uu____2416 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____2416 (FStar_Util.dflt "default")))
in (

let uu____2427 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____2414 uu____2427)))
end
| FStar_Util.Inr (c) -> begin
(comp_to_string c)
end)
in (

let topt1 = (match (topt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let uu____2448 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____2448))
end)
in (

let uu____2451 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2451 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____2492 = (term_to_string head1)
in (

let uu____2494 = (

let uu____2496 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____2529 -> (match (uu____2529) with
| (p, wopt, e) -> begin
(

let uu____2546 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____2549 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2554 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____2554))
end)
in (

let uu____2558 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____2546 uu____2549 uu____2558))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____2496))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____2492 uu____2494)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____2570 = (FStar_Options.print_universes ())
in (match (uu____2570) with
| true -> begin
(

let uu____2574 = (term_to_string t)
in (

let uu____2576 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____2574 uu____2576)))
end
| uu____2579 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____2583 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____2586 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____2588 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)" ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2583 uu____2586 uu____2588)))))
and subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___5_2591 -> (match (uu___5_2591) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2597 = (FStar_Util.string_of_int i)
in (

let uu____2599 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2597 uu____2599)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2606 = (bv_to_string x)
in (

let uu____2608 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2606 uu____2608)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2617 = (bv_to_string x)
in (

let uu____2619 = (term_to_string t)
in (FStar_Util.format2 "NT (%s, %s)" uu____2617 uu____2619)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2626 = (FStar_Util.string_of_int i)
in (

let uu____2628 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2626 uu____2628)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2635 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2635))
end))
and subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2639 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2639 (FStar_String.concat "; "))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____2655 = (

let uu____2657 = (FStar_Options.ugly ())
in (not (uu____2657)))
in (match (uu____2655) with
| true -> begin
(

let e = (

let uu____2662 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____2662))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2668 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____2691 = (fv_to_string l)
in (

let uu____2693 = (

let uu____2695 = (FStar_List.map (fun uu____2709 -> (match (uu____2709) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.op_Hat "#" p)
end
| uu____2725 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____2695 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____2691 uu____2693)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2734) -> begin
(

let uu____2739 = (FStar_Options.print_bound_var_types ())
in (match (uu____2739) with
| true -> begin
(

let uu____2743 = (bv_to_string x1)
in (

let uu____2745 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2743 uu____2745)))
end
| uu____2748 -> begin
(

let uu____2750 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2750))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2754 = (FStar_Options.print_bound_var_types ())
in (match (uu____2754) with
| true -> begin
(

let uu____2758 = (bv_to_string x1)
in (

let uu____2760 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2758 uu____2760)))
end
| uu____2763 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2767 = (FStar_Options.print_bound_var_types ())
in (match (uu____2767) with
| true -> begin
(

let uu____2771 = (bv_to_string x1)
in (

let uu____2773 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "_wild_%s:%s" uu____2771 uu____2773)))
end
| uu____2776 -> begin
(bv_to_string x1)
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let uu____2782 = (quals_to_string' quals)
in (

let uu____2784 = (

let uu____2786 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2806 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2808 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2810 = (

let uu____2812 = (FStar_Options.print_universes ())
in (match (uu____2812) with
| true -> begin
(

let uu____2816 = (

let uu____2818 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.op_Hat uu____2818 ">"))
in (Prims.op_Hat "<" uu____2816))
end
| uu____2822 -> begin
""
end))
in (

let uu____2825 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2827 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2806 uu____2808 uu____2810 uu____2825 uu____2827)))))))))
in (FStar_Util.concat_l "\n and " uu____2786))
in (FStar_Util.format3 "%slet %s %s" uu____2782 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2839 -> begin
""
end) uu____2784))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___6_2842 -> (match (uu___6_2842) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2850 = (

let uu____2852 = (FStar_List.map (fun t -> (

let uu____2860 = (term_to_string t)
in (paren uu____2860))) tms)
in (FStar_All.pipe_right uu____2852 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2850))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2869 = (FStar_Options.print_effect_args ())
in (match (uu____2869) with
| true -> begin
(

let uu____2873 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2873))
end
| uu____2874 -> begin
(

let uu____2876 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2878 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2876 uu____2878)))
end)))
and aqual_to_string' : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___7_2882 -> (match (uu___7_2882) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.op_Hat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.op_Hat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.op_Hat "$" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
(Prims.op_Hat "[|" (Prims.op_Hat s "|]"))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____2900 = (

let uu____2902 = (term_to_string t)
in (Prims.op_Hat uu____2902 (Prims.op_Hat "]" s)))
in (Prims.op_Hat "#[" uu____2900))
end
| FStar_Pervasives_Native.None -> begin
s
end))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun aq -> (aqual_to_string' "" aq))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s aq -> (aqual_to_string' s aq))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun is_arrow b -> (

let uu____2922 = (

let uu____2924 = (FStar_Options.ugly ())
in (not (uu____2924)))
in (match (uu____2922) with
| true -> begin
(

let uu____2928 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2928) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2937 -> begin
(

let uu____2939 = b
in (match (uu____2939) with
| (a, imp) -> begin
(

let uu____2953 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2953) with
| true -> begin
(

let uu____2957 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.op_Hat "_:" uu____2957))
end
| uu____2960 -> begin
(

let uu____2962 = ((not (is_arrow)) && (

let uu____2965 = (FStar_Options.print_bound_var_types ())
in (not (uu____2965))))
in (match (uu____2962) with
| true -> begin
(

let uu____2969 = (nm_to_string a)
in (imp_to_string uu____2969 imp))
end
| uu____2971 -> begin
(

let uu____2973 = (

let uu____2975 = (nm_to_string a)
in (

let uu____2977 = (

let uu____2979 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.op_Hat ":" uu____2979))
in (Prims.op_Hat uu____2975 uu____2977)))
in (imp_to_string uu____2973 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2998 = (FStar_Options.print_implicits ())
in (match (uu____2998) with
| true -> begin
bs
end
| uu____3003 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____3009 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____3009 (FStar_String.concat sep)))
end
| uu____3035 -> begin
(

let uu____3037 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____3037 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___8_3051 -> (match (uu___8_3051) with
| (a, imp) -> begin
(

let uu____3065 = (term_to_string a)
in (imp_to_string uu____3065 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____3077 = (FStar_Options.print_implicits ())
in (match (uu____3077) with
| true -> begin
args
end
| uu____3088 -> begin
(filter_imp args)
end))
in (

let uu____3092 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3092 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____3121 = (FStar_Options.ugly ())
in (match (uu____3121) with
| true -> begin
(comp_to_string c)
end
| uu____3125 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____3132 = (

let uu____3134 = (FStar_Options.ugly ())
in (not (uu____3134)))
in (match (uu____3132) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____3142 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____3155 = (

let uu____3156 = (FStar_Syntax_Subst.compress t)
in uu____3156.FStar_Syntax_Syntax.n)
in (match (uu____3155) with
| FStar_Syntax_Syntax.Tm_type (uu____3160) when (

let uu____3161 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____3161))) -> begin
(term_to_string t)
end
| uu____3163 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____3166 = (univ_to_string u)
in (

let uu____3168 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____3166 uu____3168)))
end
| uu____3171 -> begin
(

let uu____3174 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____3174))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____3187 = (

let uu____3188 = (FStar_Syntax_Subst.compress t)
in uu____3188.FStar_Syntax_Syntax.n)
in (match (uu____3187) with
| FStar_Syntax_Syntax.Tm_type (uu____3192) when (

let uu____3193 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____3193))) -> begin
(term_to_string t)
end
| uu____3195 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____3198 = (univ_to_string u)
in (

let uu____3200 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____3198 uu____3200)))
end
| uu____3203 -> begin
(

let uu____3206 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____3206))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____3212 = (FStar_Options.print_effect_args ())
in (match (uu____3212) with
| true -> begin
(

let uu____3216 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3218 = (

let uu____3220 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____3220 (FStar_String.concat ", ")))
in (

let uu____3235 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____3237 = (

let uu____3239 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3239 (FStar_String.concat ", ")))
in (

let uu____3266 = (cflags_to_string c1.FStar_Syntax_Syntax.flags)
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3216 uu____3218 uu____3235 uu____3237 uu____3266))))))
end
| uu____3269 -> begin
(

let uu____3271 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___9_3277 -> (match (uu___9_3277) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3280 -> begin
false
end)))) && (

let uu____3283 = (FStar_Options.print_effect_args ())
in (not (uu____3283))))
in (match (uu____3271) with
| true -> begin
(

let uu____3287 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____3287))
end
| uu____3290 -> begin
(

let uu____3292 = (((

let uu____3296 = (FStar_Options.print_effect_args ())
in (not (uu____3296))) && (

let uu____3299 = (FStar_Options.print_implicits ())
in (not (uu____3299)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____3292) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____3303 -> begin
(

let uu____3305 = ((

let uu____3309 = (FStar_Options.print_effect_args ())
in (not (uu____3309))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___10_3315 -> (match (uu___10_3315) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____3318 -> begin
false
end)))))
in (match (uu____3305) with
| true -> begin
(

let uu____3322 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____3322))
end
| uu____3325 -> begin
(

let uu____3327 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3329 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____3327 uu____3329)))
end))
end))
end))
end))
in (

let dec = (

let uu____3334 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___11_3347 -> (match (uu___11_3347) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3354 = (

let uu____3356 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____3356))
in (uu____3354)::[])
end
| uu____3361 -> begin
[]
end))))
in (FStar_All.pipe_right uu____3334 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end)
end)))
and cflag_to_string : FStar_Syntax_Syntax.cflag  ->  Prims.string = (fun c -> (match (c) with
| FStar_Syntax_Syntax.TOTAL -> begin
"total"
end
| FStar_Syntax_Syntax.MLEFFECT -> begin
"ml"
end
| FStar_Syntax_Syntax.RETURN -> begin
"return"
end
| FStar_Syntax_Syntax.PARTIAL_RETURN -> begin
"partial_return"
end
| FStar_Syntax_Syntax.SOMETRIVIAL -> begin
"sometrivial"
end
| FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> begin
"trivial_postcondition"
end
| FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> begin
"should_not_inline"
end
| FStar_Syntax_Syntax.LEMMA -> begin
"lemma"
end
| FStar_Syntax_Syntax.CPS -> begin
"cps"
end
| FStar_Syntax_Syntax.DECREASES (uu____3380) -> begin
""
end))
and cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list  ->  Prims.string = (fun fs -> (FStar_Common.string_of_list cflag_to_string fs))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___12_3390 -> (match (uu___12_3390) with
| FStar_Syntax_Syntax.Meta_pattern (uu____3392, ps) -> begin
(

let pats = (

let uu____3428 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____3465 = (FStar_All.pipe_right args (FStar_List.map (fun uu____3490 -> (match (uu____3490) with
| (t, uu____3499) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____3465 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____3428 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____3516 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____3516))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____3521) -> begin
(

let uu____3526 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3526))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____3537 = (sli m)
in (

let uu____3539 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3537 uu____3539)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____3549 = (sli m)
in (

let uu____3551 = (sli m')
in (

let uu____3553 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3549 uu____3551 uu____3553))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____3568 = (FStar_Options.ugly ())
in (match (uu____3568) with
| true -> begin
(term_to_string x)
end
| uu____3572 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____3589 = b
in (match (uu____3589) with
| (a, imp) -> begin
(

let n1 = (

let uu____3597 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____3597) with
| true -> begin
FStar_Util.JsonNull
end
| uu____3600 -> begin
(

let uu____3602 = (

let uu____3604 = (nm_to_string a)
in (imp_to_string uu____3604 imp))
in FStar_Util.JsonStr (uu____3602))
end))
in (

let t = (

let uu____3607 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____3607))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____3639 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____3639)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____3657 = (FStar_Options.print_universes ())
in (match (uu____3657) with
| true -> begin
(Prims.op_Hat "<" (Prims.op_Hat s ">"))
end
| uu____3663 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____3673 = (

let uu____3675 = (FStar_Options.ugly ())
in (not (uu____3675)))
in (match (uu____3673) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____3683 -> begin
(

let uu____3685 = s
in (match (uu____3685) with
| (us, t) -> begin
(

let uu____3697 = (

let uu____3699 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____3699))
in (

let uu____3703 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____3697 uu____3703)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____3713 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____3715 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____3718 = (

let uu____3720 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____3720))
in (

let uu____3724 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____3726 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____3713 uu____3715 uu____3718 uu____3724 uu____3726)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____3757 = (

let uu____3759 = (FStar_Options.ugly ())
in (not (uu____3759)))
in (match (uu____3757) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____3767 -> begin
(

let actions_to_string = (fun actions -> (

let uu____3780 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____3780 (FStar_String.concat ",\n\t"))))
in (

let uu____3795 = (

let uu____3799 = (

let uu____3803 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____3805 = (

let uu____3809 = (

let uu____3811 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____3811))
in (

let uu____3815 = (

let uu____3819 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____3822 = (

let uu____3826 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____3828 = (

let uu____3832 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3834 = (

let uu____3838 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____3840 = (

let uu____3844 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3846 = (

let uu____3850 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3852 = (

let uu____3856 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____3858 = (

let uu____3862 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____3864 = (

let uu____3868 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____3870 = (

let uu____3874 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____3876 = (

let uu____3880 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____3882 = (

let uu____3886 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____3888 = (

let uu____3892 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____3894 = (

let uu____3898 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____3900 = (

let uu____3904 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____3906 = (

let uu____3910 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____3910)::[])
in (uu____3904)::uu____3906))
in (uu____3898)::uu____3900))
in (uu____3892)::uu____3894))
in (uu____3886)::uu____3888))
in (uu____3880)::uu____3882))
in (uu____3874)::uu____3876))
in (uu____3868)::uu____3870))
in (uu____3862)::uu____3864))
in (uu____3856)::uu____3858))
in (uu____3850)::uu____3852))
in (uu____3844)::uu____3846))
in (uu____3838)::uu____3840))
in (uu____3832)::uu____3834))
in (uu____3826)::uu____3828))
in (uu____3819)::uu____3822))
in (uu____3809)::uu____3815))
in (uu____3803)::uu____3805))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____3935 -> begin
""
end))::uu____3799)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____3795)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let basic = (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff) -> begin
"#light \"off\""
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.None)) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (FStar_Pervasives_Native.Some (s))) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s)) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.None)) -> begin
"#push-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions (FStar_Pervasives_Native.Some (s))) -> begin
(FStar_Util.format1 "#push-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions) -> begin
"#pop-options"
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____3984, uu____3985) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____4001 = (FStar_Options.print_universes ())
in (match (uu____4001) with
| true -> begin
(

let uu____4005 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____4005 binders_str term_str))
end
| uu____4008 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____4014, uu____4015, uu____4016) -> begin
(

let uu____4023 = (FStar_Options.print_universes ())
in (match (uu____4023) with
| true -> begin
(

let uu____4027 = (univ_names_to_string univs1)
in (

let uu____4029 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____4027 lid.FStar_Ident.str uu____4029)))
end
| uu____4032 -> begin
(

let uu____4034 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____4034))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____4040 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____4042 = (

let uu____4044 = (FStar_Options.print_universes ())
in (match (uu____4044) with
| true -> begin
(

let uu____4048 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____4048))
end
| uu____4051 -> begin
""
end))
in (

let uu____4054 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____4040 lid.FStar_Ident.str uu____4042 uu____4054))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, f) -> begin
(

let uu____4060 = (FStar_Options.print_universes ())
in (match (uu____4060) with
| true -> begin
(

let uu____4064 = (univ_names_to_string us)
in (

let uu____4066 = (term_to_string f)
in (FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str uu____4064 uu____4066)))
end
| uu____4069 -> begin
(

let uu____4071 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4071))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____4075) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____4081 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____4081))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4085) -> begin
(

let uu____4094 = (

let uu____4096 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____4096 (FStar_String.concat "\n")))
in (Prims.op_Hat "(* Sig_bundle *)" uu____4094))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(eff_decl_to_string' false x.FStar_Syntax_Syntax.sigrng x.FStar_Syntax_Syntax.sigquals ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(eff_decl_to_string' true x.FStar_Syntax_Syntax.sigrng x.FStar_Syntax_Syntax.sigquals ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "impossible")
end
| (FStar_Pervasives_Native.Some (lift_wp), uu____4141) -> begin
lift_wp
end
| (uu____4148, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____4156 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____4156) with
| (us, t) -> begin
(

let uu____4168 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____4170 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____4172 = (univ_names_to_string us)
in (

let uu____4174 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4168 uu____4170 uu____4172 uu____4174)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____4186 = (FStar_Options.print_universes ())
in (match (uu____4186) with
| true -> begin
(

let uu____4190 = (

let uu____4195 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____4195))
in (match (uu____4190) with
| (univs2, t) -> begin
(

let uu____4209 = (

let uu____4214 = (

let uu____4215 = (FStar_Syntax_Subst.compress t)
in uu____4215.FStar_Syntax_Syntax.n)
in (match (uu____4214) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____4244 -> begin
(failwith "impossible")
end))
in (match (uu____4209) with
| (tps1, c1) -> begin
(

let uu____4253 = (sli l)
in (

let uu____4255 = (univ_names_to_string univs2)
in (

let uu____4257 = (binders_to_string " " tps1)
in (

let uu____4260 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____4253 uu____4255 uu____4257 uu____4260)))))
end))
end))
end
| uu____4263 -> begin
(

let uu____4265 = (sli l)
in (

let uu____4267 = (binders_to_string " " tps)
in (

let uu____4270 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____4265 uu____4267 uu____4270))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____4279 = (

let uu____4281 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____4281))
in (

let uu____4291 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____4279 uu____4291)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____4295 -> begin
(

let uu____4298 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.op_Hat uu____4298 (Prims.op_Hat "\n" basic)))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____4315 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____4315 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____4326, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____4328; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____4330; FStar_Syntax_Syntax.lbdef = uu____4331; FStar_Syntax_Syntax.lbattrs = uu____4332; FStar_Syntax_Syntax.lbpos = uu____4333})::[]), uu____4334) -> begin
(

let uu____4357 = (lbname_to_string lb)
in (

let uu____4359 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____4357 uu____4359)))
end
| uu____4362 -> begin
(

let uu____4363 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____4363 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____4387 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____4389 = (

let uu____4391 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____4391 (FStar_String.concat "\n")))
in (

let uu____4401 = (

let uu____4403 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____4403 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4387 uu____4389 uu____4401)))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____4447 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____4447));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____4456 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____4456));
)
end);
(FStar_Util.string_of_string_builder strb);
)))


let list_to_string : 'a . ('a  ->  Prims.string)  ->  'a Prims.list  ->  Prims.string = (fun f elts -> (match (elts) with
| [] -> begin
"[]"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "[");
(

let uu____4497 = (f x)
in (FStar_Util.string_builder_append strb uu____4497));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____4506 = (f x1)
in (FStar_Util.string_builder_append strb uu____4506));
)) xs);
(FStar_Util.string_builder_append strb "]");
(FStar_Util.string_of_string_builder strb);
))
end))


let set_to_string : 'a . ('a  ->  Prims.string)  ->  'a FStar_Util.set  ->  Prims.string = (fun f s -> (

let elts = (FStar_Util.set_elements s)
in (match (elts) with
| [] -> begin
"{}"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "{");
(

let uu____4553 = (f x)
in (FStar_Util.string_builder_append strb uu____4553));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____4562 = (f x1)
in (FStar_Util.string_builder_append strb uu____4562));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____4584 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____4584)))


let rec emb_typ_to_string : FStar_Syntax_Syntax.emb_typ  ->  Prims.string = (fun uu___13_4597 -> (match (uu___13_4597) with
| FStar_Syntax_Syntax.ET_abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.ET_app (h, []) -> begin
h
end
| FStar_Syntax_Syntax.ET_app (h, args) -> begin
(

let uu____4613 = (

let uu____4615 = (

let uu____4617 = (

let uu____4619 = (

let uu____4621 = (FStar_List.map emb_typ_to_string args)
in (FStar_All.pipe_right uu____4621 (FStar_String.concat " ")))
in (Prims.op_Hat uu____4619 ")"))
in (Prims.op_Hat " " uu____4617))
in (Prims.op_Hat h uu____4615))
in (Prims.op_Hat "(" uu____4613))
end
| FStar_Syntax_Syntax.ET_fun (a, b) -> begin
(

let uu____4636 = (

let uu____4638 = (emb_typ_to_string a)
in (

let uu____4640 = (

let uu____4642 = (emb_typ_to_string b)
in (Prims.op_Hat ") -> " uu____4642))
in (Prims.op_Hat uu____4638 uu____4640)))
in (Prims.op_Hat "(" uu____4636))
end))





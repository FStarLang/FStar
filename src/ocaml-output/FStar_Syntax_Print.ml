
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___201_4 -> (match (uu___201_4) with
| FStar_Syntax_Syntax.Delta_constant -> begin
"Delta_constant"
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
(

let uu____6 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_defined_at_level " uu____6))
end
| FStar_Syntax_Syntax.Delta_equational -> begin
"Delta_equational"
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(

let uu____8 = (

let uu____9 = (delta_depth_to_string d)
in (Prims.strcat uu____9 ")"))
in (Prims.strcat "Delta_abstract (" uu____8))
end))


let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____14 = (FStar_Options.print_real_names ())
in (match (uu____14) with
| true -> begin
l.FStar_Ident.str
end
| uu____15 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____28 = (

let uu____29 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____29))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____28)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____34 = (FStar_Options.print_real_names ())
in (match (uu____34) with
| true -> begin
(bv_to_string bv)
end
| uu____35 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____40 = (

let uu____41 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____41))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____40)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____177 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____187 -> begin
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


let is_inr : 'Auu____252 'Auu____253 . ('Auu____253, 'Auu____252) FStar_Util.either  ->  Prims.bool = (fun uu___202_261 -> (match (uu___202_261) with
| FStar_Util.Inl (uu____266) -> begin
false
end
| FStar_Util.Inr (uu____267) -> begin
true
end))


let filter_imp : 'Auu____272 . ('Auu____272 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____272 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___203_326 -> (match (uu___203_326) with
| (uu____333, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____334))) -> begin
false
end
| uu____337 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____354 = (

let uu____355 = (FStar_Syntax_Subst.compress e)
in uu____355.FStar_Syntax_Syntax.n)
in (match (uu____354) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____418 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____418) with
| true -> begin
(

let uu____427 = (

let uu____434 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____434))
in (match (uu____427) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____452 = (

let uu____457 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____457)::xs)
in FStar_Pervasives_Native.Some (uu____452))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____476 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____481 -> begin
(

let uu____482 = (is_lex_top e)
in (match (uu____482) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____495 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____528 = (f hd1)
in (match (uu____528) with
| true -> begin
hd1
end
| uu____529 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____550 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____550)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____573 = (get_lid e)
in (find_lid uu____573 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____582 = (get_lid e)
in (find_lid uu____582 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____591 = (get_lid t)
in (find_lid uu____591 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
"Effect"
end
| FStar_Const.Const_unit -> begin
"()"
end
| FStar_Const.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| uu____597 -> begin
"false"
end)
end
| FStar_Const.Const_float (x1) -> begin
(FStar_Util.string_of_float x1)
end
| FStar_Const.Const_string (s, uu____600) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| FStar_Const.Const_bytearray (uu____601) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x1, uu____609) -> begin
x1
end
| FStar_Const.Const_char (c) -> begin
(Prims.strcat "\'" (Prims.strcat (FStar_Util.string_of_char c) "\'"))
end
| FStar_Const.Const_range (r) -> begin
(FStar_Range.string_of_range r)
end
| FStar_Const.Const_reify -> begin
"reify"
end
| FStar_Const.Const_reflect (l) -> begin
(

let uu____625 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" uu____625))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___204_629 -> (match (uu___204_629) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____637 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____637))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____639 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____639))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____641 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____641))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____642) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____649) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____650) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____651) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____668) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____681) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____688) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____703) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____726) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____753) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____766) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____783, m) -> begin
(

let uu____825 = (FStar_ST.op_Bang m)
in (match (uu____825) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____900) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____905) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____916 = (FStar_Options.hide_uvar_nums ())
in (match (uu____916) with
| true -> begin
"?"
end
| uu____917 -> begin
(

let uu____918 = (

let uu____919 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____919 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____918))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____924 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____925 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____924 uu____925))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____930 = (FStar_Options.hide_uvar_nums ())
in (match (uu____930) with
| true -> begin
"?"
end
| uu____931 -> begin
(

let uu____932 = (

let uu____933 = (

let uu____934 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____934 FStar_Util.string_of_int))
in (

let uu____935 = (

let uu____936 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____936))
in (Prims.strcat uu____933 uu____935)))
in (Prims.strcat "?" uu____932))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____955 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____955) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____965 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____972 = (

let uu____973 = (FStar_Options.ugly ())
in (not (uu____973)))
in (match (uu____972) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____976 -> begin
(

let uu____977 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____977) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____989 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____989))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____991 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____991) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____1005 = (univ_to_string u2)
in (

let uu____1006 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____1005 uu____1006)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____1010 = (

let uu____1011 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____1011 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____1010))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____1024 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____1024 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____1037 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____1037 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___205_1047 -> (match (uu___205_1047) with
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

let uu____1049 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____1049))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____1052 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____1052 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____1063 = (

let uu____1064 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1064))
in (

let uu____1067 = (

let uu____1068 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1068 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____1063 uu____1067)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____1087 = (

let uu____1088 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1088))
in (

let uu____1091 = (

let uu____1092 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1092 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____1087 uu____1091)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____1102 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____1102))
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
| uu____1112 -> begin
(

let uu____1115 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____1115 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____1132 -> begin
(

let uu____1135 = (quals_to_string quals)
in (Prims.strcat uu____1135 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1191 = (

let uu____1192 = (FStar_Options.ugly ())
in (not (uu____1192)))
in (match (uu____1191) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1195 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1198 = (FStar_Options.print_implicits ())
in (match (uu____1198) with
| true -> begin
x1
end
| uu____1199 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1200) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1225, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1261 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1291 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1309 -> (match (uu____1309) with
| (t1, uu____1315) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1291 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1261 (FStar_String.concat "\\/")))
in (

let uu____1320 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1320)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1332 = (tag_of_term t)
in (

let uu____1333 = (sli m)
in (

let uu____1334 = (term_to_string t')
in (

let uu____1335 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1332 uu____1333 uu____1334 uu____1335)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1348 = (tag_of_term t)
in (

let uu____1349 = (term_to_string t')
in (

let uu____1350 = (sli m0)
in (

let uu____1351 = (sli m1)
in (

let uu____1352 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1348 uu____1349 uu____1350 uu____1351 uu____1352))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_alien (uu____1354, s, uu____1356)) -> begin
(FStar_Util.format1 "(Meta_alien \"%s\")" s)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1373 = (FStar_Range.string_of_range r)
in (

let uu____1374 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1373 uu____1374)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____1376) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1382 = (db_to_string x3)
in (

let uu____1383 = (

let uu____1384 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1384))
in (Prims.strcat uu____1382 uu____1383)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____1388) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1415 = (FStar_Options.print_universes ())
in (match (uu____1415) with
| true -> begin
(

let uu____1416 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1416))
end
| uu____1417 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1436 = (binders_to_string " -> " bs)
in (

let uu____1437 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1436 uu____1437)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1462 = (binders_to_string " " bs)
in (

let uu____1463 = (term_to_string t2)
in (

let uu____1464 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1467 -> begin
(

let uu____1468 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1468))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1462 uu____1463 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1464))))
end
| uu____1471 -> begin
(

let uu____1474 = (binders_to_string " " bs)
in (

let uu____1475 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1474 uu____1475)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1482 = (bv_to_string xt)
in (

let uu____1483 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1486 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1482 uu____1483 uu____1486))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1511 = (term_to_string t)
in (

let uu____1512 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1511 uu____1512)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1531 = (lbs_to_string [] lbs)
in (

let uu____1532 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1531 uu____1532)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1593 = (

let uu____1594 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1594 (FStar_Util.dflt "default")))
in (

let uu____1599 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1593 uu____1599)))
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

let uu____1615 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1615))
end)
in (

let uu____1616 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1616 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1655 = (term_to_string head1)
in (

let uu____1656 = (

let uu____1657 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1693 -> (match (uu____1693) with
| (p, wopt, e) -> begin
(

let uu____1709 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1710 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1712 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1712))
end)
in (

let uu____1713 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1709 uu____1710 uu____1713))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1657))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1655 uu____1656)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1720 = (FStar_Options.print_universes ())
in (match (uu____1720) with
| true -> begin
(

let uu____1721 = (term_to_string t)
in (

let uu____1722 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1721 uu____1722)))
end
| uu____1723 -> begin
(term_to_string t)
end))
end
| uu____1724 -> begin
(tag_of_term x2)
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1726 = (

let uu____1727 = (FStar_Options.ugly ())
in (not (uu____1727)))
in (match (uu____1726) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_pat x)
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1730 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1749 = (fv_to_string l)
in (

let uu____1750 = (

let uu____1751 = (FStar_List.map (fun uu____1762 -> (match (uu____1762) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1770 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1751 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1749 uu____1750)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1774) -> begin
(

let uu____1779 = (FStar_Options.print_bound_var_types ())
in (match (uu____1779) with
| true -> begin
(

let uu____1780 = (bv_to_string x1)
in (

let uu____1781 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1780 uu____1781)))
end
| uu____1782 -> begin
(

let uu____1783 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1783))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1785 = (FStar_Options.print_bound_var_types ())
in (match (uu____1785) with
| true -> begin
(

let uu____1786 = (bv_to_string x1)
in (

let uu____1787 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1786 uu____1787)))
end
| uu____1788 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1791 = (FStar_Options.print_real_names ())
in (match (uu____1791) with
| true -> begin
(

let uu____1792 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1792))
end
| uu____1793 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1811 = (FStar_Options.print_universes ())
in (match (uu____1811) with
| true -> begin
(

let uu____1818 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1836 = (

let uu____1841 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1841))
in (match (uu____1836) with
| (us, td) -> begin
(

let uu____1844 = (

let uu____1853 = (

let uu____1854 = (FStar_Syntax_Subst.compress td)
in uu____1854.FStar_Syntax_Syntax.n)
in (match (uu____1853) with
| FStar_Syntax_Syntax.Tm_app (uu____1865, ((t, uu____1867))::((d, uu____1869))::[]) -> begin
((t), (d))
end
| uu____1912 -> begin
(failwith "Impossibe")
end))
in (match (uu____1844) with
| (t, d) -> begin
(

let uu___212_1931 = lb
in {FStar_Syntax_Syntax.lbname = uu___212_1931.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___212_1931.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____1818)))
end
| uu____1936 -> begin
lbs
end))
in (

let uu____1937 = (quals_to_string' quals)
in (

let uu____1938 = (

let uu____1939 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1954 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1955 = (

let uu____1956 = (FStar_Options.print_universes ())
in (match (uu____1956) with
| true -> begin
(

let uu____1957 = (

let uu____1958 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1958 ">"))
in (Prims.strcat "<" uu____1957))
end
| uu____1959 -> begin
""
end))
in (

let uu____1960 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1961 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1954 uu____1955 uu____1960 uu____1961))))))))
in (FStar_Util.concat_l "\n and " uu____1939))
in (FStar_Util.format3 "%slet %s %s" uu____1937 (match ((FStar_Pervasives_Native.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1966 -> begin
""
end) uu____1938)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1968 = (FStar_Options.print_effect_args ())
in (match (uu____1968) with
| true -> begin
(

let uu____1969 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1969))
end
| uu____1970 -> begin
(

let uu____1971 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1972 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1971 uu____1972)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___206_1974 -> (match (uu___206_1974) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1977 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____1982 = (

let uu____1983 = (FStar_Options.ugly ())
in (not (uu____1983)))
in (match (uu____1982) with
| true -> begin
(

let uu____1984 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1984) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1989 -> begin
(

let uu____1990 = b
in (match (uu____1990) with
| (a, imp) -> begin
(

let uu____1993 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1993) with
| true -> begin
(

let uu____1994 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1994))
end
| uu____1995 -> begin
(

let uu____1996 = ((not (is_arrow)) && (

let uu____1998 = (FStar_Options.print_bound_var_types ())
in (not (uu____1998))))
in (match (uu____1996) with
| true -> begin
(

let uu____1999 = (nm_to_string a)
in (imp_to_string uu____1999 imp))
end
| uu____2000 -> begin
(

let uu____2001 = (

let uu____2002 = (nm_to_string a)
in (

let uu____2003 = (

let uu____2004 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2004))
in (Prims.strcat uu____2002 uu____2003)))
in (imp_to_string uu____2001 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2010 = (FStar_Options.print_implicits ())
in (match (uu____2010) with
| true -> begin
bs
end
| uu____2011 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2012 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2012 (FStar_String.concat sep)))
end
| uu____2019 -> begin
(

let uu____2020 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2020 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___207_2027 -> (match (uu___207_2027) with
| (a, imp) -> begin
(

let uu____2040 = (term_to_string a)
in (imp_to_string uu____2040 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2043 = (FStar_Options.print_implicits ())
in (match (uu____2043) with
| true -> begin
args
end
| uu____2044 -> begin
(filter_imp args)
end))
in (

let uu____2047 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2047 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2061 = (

let uu____2062 = (FStar_Options.ugly ())
in (not (uu____2062)))
in (match (uu____2061) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2065 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2076 = (

let uu____2077 = (FStar_Syntax_Subst.compress t)
in uu____2077.FStar_Syntax_Syntax.n)
in (match (uu____2076) with
| FStar_Syntax_Syntax.Tm_type (uu____2080) when (

let uu____2081 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2081))) -> begin
(term_to_string t)
end
| uu____2082 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2084 = (univ_to_string u)
in (

let uu____2085 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2084 uu____2085)))
end
| uu____2086 -> begin
(

let uu____2089 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2089))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2100 = (

let uu____2101 = (FStar_Syntax_Subst.compress t)
in uu____2101.FStar_Syntax_Syntax.n)
in (match (uu____2100) with
| FStar_Syntax_Syntax.Tm_type (uu____2104) when (

let uu____2105 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2105))) -> begin
(term_to_string t)
end
| uu____2106 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2108 = (univ_to_string u)
in (

let uu____2109 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2108 uu____2109)))
end
| uu____2110 -> begin
(

let uu____2113 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2113))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2116 = (FStar_Options.print_effect_args ())
in (match (uu____2116) with
| true -> begin
(

let uu____2117 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2118 = (

let uu____2119 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2119 (FStar_String.concat ", ")))
in (

let uu____2126 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2127 = (

let uu____2128 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2128 (FStar_String.concat ", ")))
in (

let uu____2149 = (

let uu____2150 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2150 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2117 uu____2118 uu____2126 uu____2127 uu____2149))))))
end
| uu____2159 -> begin
(

let uu____2160 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___208_2164 -> (match (uu___208_2164) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2165 -> begin
false
end)))) && (

let uu____2167 = (FStar_Options.print_effect_args ())
in (not (uu____2167))))
in (match (uu____2160) with
| true -> begin
(

let uu____2168 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2168))
end
| uu____2169 -> begin
(

let uu____2170 = (((

let uu____2173 = (FStar_Options.print_effect_args ())
in (not (uu____2173))) && (

let uu____2175 = (FStar_Options.print_implicits ())
in (not (uu____2175)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2170) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2176 -> begin
(

let uu____2177 = ((

let uu____2180 = (FStar_Options.print_effect_args ())
in (not (uu____2180))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___209_2184 -> (match (uu___209_2184) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2185 -> begin
false
end)))))
in (match (uu____2177) with
| true -> begin
(

let uu____2186 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2186))
end
| uu____2187 -> begin
(

let uu____2188 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2189 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2188 uu____2189)))
end))
end))
end))
end))
in (

let dec = (

let uu____2191 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___210_2201 -> (match (uu___210_2201) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2207 = (

let uu____2208 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2208))
in (uu____2207)::[])
end
| uu____2209 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2191 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end)
end)))
and cflags_to_string : FStar_Syntax_Syntax.cflags  ->  Prims.string = (fun c -> (match (c) with
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
| FStar_Syntax_Syntax.LEMMA -> begin
"lemma"
end
| FStar_Syntax_Syntax.CPS -> begin
"cps"
end
| FStar_Syntax_Syntax.DECREASES (uu____2213) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let binder_to_json : FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun b -> (

let uu____2223 = b
in (match (uu____2223) with
| (a, imp) -> begin
(

let n1 = (

let uu____2227 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2227) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2228 -> begin
(

let uu____2229 = (

let uu____2230 = (nm_to_string a)
in (imp_to_string uu____2230 imp))
in FStar_Util.JsonStr (uu____2229))
end))
in (

let t = (

let uu____2232 = (term_to_string a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2232))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun bs -> (

let uu____2249 = (FStar_List.map binder_to_json bs)
in FStar_Util.JsonList (uu____2249)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2256 = (FStar_Options.print_universes ())
in (match (uu____2256) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2257 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2262 = (

let uu____2263 = (FStar_Options.ugly ())
in (not (uu____2263)))
in (match (uu____2262) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2266 -> begin
(

let uu____2267 = s
in (match (uu____2267) with
| (us, t) -> begin
(

let uu____2274 = (

let uu____2275 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2275))
in (

let uu____2276 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2274 uu____2276)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2281 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2282 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2283 = (

let uu____2284 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2284))
in (

let uu____2285 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2286 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2281 uu____2282 uu____2283 uu____2285 uu____2286)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2307 = (

let uu____2308 = (FStar_Options.ugly ())
in (not (uu____2308)))
in (match (uu____2307) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2311 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2320 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2320 (FStar_String.concat ",\n\t"))))
in (

let uu____2329 = (

let uu____2332 = (

let uu____2335 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2336 = (

let uu____2339 = (

let uu____2340 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2340))
in (

let uu____2341 = (

let uu____2344 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2345 = (

let uu____2348 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2349 = (

let uu____2352 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2353 = (

let uu____2356 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2357 = (

let uu____2360 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2361 = (

let uu____2364 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2365 = (

let uu____2368 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2369 = (

let uu____2372 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2373 = (

let uu____2376 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2377 = (

let uu____2380 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2381 = (

let uu____2384 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2385 = (

let uu____2388 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2389 = (

let uu____2392 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2393 = (

let uu____2396 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2397 = (

let uu____2400 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2401 = (

let uu____2404 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2404)::[])
in (uu____2400)::uu____2401))
in (uu____2396)::uu____2397))
in (uu____2392)::uu____2393))
in (uu____2388)::uu____2389))
in (uu____2384)::uu____2385))
in (uu____2380)::uu____2381))
in (uu____2376)::uu____2377))
in (uu____2372)::uu____2373))
in (uu____2368)::uu____2369))
in (uu____2364)::uu____2365))
in (uu____2360)::uu____2361))
in (uu____2356)::uu____2357))
in (uu____2352)::uu____2353))
in (uu____2348)::uu____2349))
in (uu____2344)::uu____2345))
in (uu____2339)::uu____2341))
in (uu____2335)::uu____2336))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2405 -> begin
""
end))::uu____2332)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2329)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2418 = (

let uu____2419 = (FStar_Options.ugly ())
in (not (uu____2419)))
in (match (uu____2418) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2425 -> begin
""
end))
end
| uu____2428 -> begin
(match (x.FStar_Syntax_Syntax.sigel) with
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2435, uu____2436) -> begin
(

let uu____2445 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2446 = (binders_to_string " " tps)
in (

let uu____2447 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____2445 lid.FStar_Ident.str uu____2446 uu____2447))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2451, uu____2452, uu____2453) -> begin
(

let uu____2458 = (FStar_Options.print_universes ())
in (match (uu____2458) with
| true -> begin
(

let uu____2459 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____2459) with
| (univs2, t1) -> begin
(

let uu____2466 = (univ_names_to_string univs2)
in (

let uu____2467 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2466 lid.FStar_Ident.str uu____2467)))
end))
end
| uu____2468 -> begin
(

let uu____2469 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2469))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2473 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____2473) with
| (univs2, t1) -> begin
(

let uu____2480 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2481 = (

let uu____2482 = (FStar_Options.print_universes ())
in (match (uu____2482) with
| true -> begin
(

let uu____2483 = (univ_names_to_string univs2)
in (FStar_Util.format1 "<%s>" uu____2483))
end
| uu____2484 -> begin
""
end))
in (

let uu____2485 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2480 lid.FStar_Ident.str uu____2481 uu____2485))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2487, f) -> begin
(

let uu____2489 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2489))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2491) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2497 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2497))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2499) -> begin
(

let uu____2508 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2508 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2526) -> begin
lift_wp
end
| (uu____2533, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2541 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2541) with
| (us, t) -> begin
(

let uu____2552 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2553 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2554 = (univ_names_to_string us)
in (

let uu____2555 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2552 uu____2553 uu____2554 uu____2555)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____2565 = (FStar_Options.print_universes ())
in (match (uu____2565) with
| true -> begin
(

let uu____2566 = (

let uu____2571 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2571))
in (match (uu____2566) with
| (univs2, t) -> begin
(

let uu____2574 = (

let uu____2587 = (

let uu____2588 = (FStar_Syntax_Subst.compress t)
in uu____2588.FStar_Syntax_Syntax.n)
in (match (uu____2587) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2629 -> begin
(failwith "impossible")
end))
in (match (uu____2574) with
| (tps1, c1) -> begin
(

let uu____2660 = (sli l)
in (

let uu____2661 = (univ_names_to_string univs2)
in (

let uu____2662 = (binders_to_string " " tps1)
in (

let uu____2663 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2660 uu____2661 uu____2662 uu____2663)))))
end))
end))
end
| uu____2664 -> begin
(

let uu____2665 = (sli l)
in (

let uu____2666 = (binders_to_string " " tps)
in (

let uu____2667 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2665 uu____2666 uu____2667))))
end))
end)
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2676 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2676 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2681, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2683; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2685; FStar_Syntax_Syntax.lbdef = uu____2686})::[]), uu____2687) -> begin
(

let uu____2710 = (lbname_to_string lb)
in (

let uu____2711 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2710 uu____2711)))
end
| uu____2712 -> begin
(

let uu____2713 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2713 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____2728 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____2729 = (

let uu____2730 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____2730 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____2728 uu____2729))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___211_2738 -> (match (uu___211_2738) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2741 = (FStar_Util.string_of_int i)
in (

let uu____2742 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2741 uu____2742)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2745 = (bv_to_string x)
in (

let uu____2746 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2745 uu____2746)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2753 = (bv_to_string x)
in (

let uu____2754 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____2753 uu____2754)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2757 = (FStar_Util.string_of_int i)
in (

let uu____2758 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2757 uu____2758)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2761 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2761))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2766 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2766 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid));
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

let uu____2838 = (f x)
in (FStar_Util.string_builder_append strb uu____2838));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2845 = (f x1)
in (FStar_Util.string_builder_append strb uu____2845));
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

let uu____2881 = (f x)
in (FStar_Util.string_builder_append strb uu____2881));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2888 = (f x1)
in (FStar_Util.string_builder_append strb uu____2888));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))






open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___199_4 -> (match (uu___199_4) with
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


let is_inr : 'Auu____252 'Auu____253 . ('Auu____253, 'Auu____252) FStar_Util.either  ->  Prims.bool = (fun uu___200_261 -> (match (uu___200_261) with
| FStar_Util.Inl (uu____266) -> begin
false
end
| FStar_Util.Inr (uu____267) -> begin
true
end))


let filter_imp : 'Auu____272 . ('Auu____272 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____272 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___201_326 -> (match (uu___201_326) with
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

let uu____418 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
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
| FStar_Const.Const_string (bytes, uu____600) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____605) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x1, uu____613) -> begin
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

let uu____629 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" uu____629))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___202_633 -> (match (uu___202_633) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____641 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____641))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____643 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____643))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____645 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____645))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____646) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____653) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____654) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____655) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____672) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____685) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____692) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____707) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____730) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____757) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____770) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____787, m) -> begin
(

let uu____829 = (FStar_ST.read m)
in (match (uu____829) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____842) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____847) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____858 = (FStar_Options.hide_uvar_nums ())
in (match (uu____858) with
| true -> begin
"?"
end
| uu____859 -> begin
(

let uu____860 = (

let uu____861 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____861 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____860))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____866 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____867 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____866 uu____867))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____872 = (FStar_Options.hide_uvar_nums ())
in (match (uu____872) with
| true -> begin
"?"
end
| uu____873 -> begin
(

let uu____874 = (

let uu____875 = (

let uu____876 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____876 FStar_Util.string_of_int))
in (

let uu____877 = (

let uu____878 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____878))
in (Prims.strcat uu____875 uu____877)))
in (Prims.strcat "?" uu____874))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____897 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____897) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____907 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____914 = (

let uu____915 = (FStar_Options.ugly ())
in (not (uu____915)))
in (match (uu____914) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____918 -> begin
(

let uu____919 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____919) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____931 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____931))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____933 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____933) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____947 = (univ_to_string u2)
in (

let uu____948 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____947 uu____948)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____952 = (

let uu____953 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____953 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____952))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____966 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____966 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____979 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____979 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___203_989 -> (match (uu___203_989) with
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

let uu____991 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____991))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____994 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____994 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____1005 = (

let uu____1006 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1006))
in (

let uu____1009 = (

let uu____1010 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1010 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____1005 uu____1009)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____1029 = (

let uu____1030 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1030))
in (

let uu____1033 = (

let uu____1034 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1034 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____1029 uu____1033)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____1044 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____1044))
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
| uu____1054 -> begin
(

let uu____1057 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____1057 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____1074 -> begin
(

let uu____1077 = (quals_to_string quals)
in (Prims.strcat uu____1077 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1133 = (

let uu____1134 = (FStar_Options.ugly ())
in (not (uu____1134)))
in (match (uu____1133) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1137 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1140 = (FStar_Options.print_implicits ())
in (match (uu____1140) with
| true -> begin
x1
end
| uu____1141 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1142) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1167, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1203 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1233 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1251 -> (match (uu____1251) with
| (t1, uu____1257) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1233 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1203 (FStar_String.concat "\\/")))
in (

let uu____1262 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1262)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1274 = (tag_of_term t)
in (

let uu____1275 = (sli m)
in (

let uu____1276 = (term_to_string t')
in (

let uu____1277 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1274 uu____1275 uu____1276 uu____1277)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1290 = (tag_of_term t)
in (

let uu____1291 = (term_to_string t')
in (

let uu____1292 = (sli m0)
in (

let uu____1293 = (sli m1)
in (

let uu____1294 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1290 uu____1291 uu____1292 uu____1293 uu____1294))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_alien (uu____1296, s)) -> begin
(FStar_Util.format1 "(Meta_alien \"%s\")" s)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1310 = (FStar_Range.string_of_range r)
in (

let uu____1311 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1310 uu____1311)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____1313) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1319 = (db_to_string x3)
in (

let uu____1320 = (

let uu____1321 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1321))
in (Prims.strcat uu____1319 uu____1320)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____1325) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1352 = (FStar_Options.print_universes ())
in (match (uu____1352) with
| true -> begin
(

let uu____1353 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1353))
end
| uu____1354 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1373 = (binders_to_string " -> " bs)
in (

let uu____1374 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1373 uu____1374)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1399 = (binders_to_string " " bs)
in (

let uu____1400 = (term_to_string t2)
in (

let uu____1401 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1404 -> begin
(

let uu____1405 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1405))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1399 uu____1400 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1401))))
end
| uu____1408 -> begin
(

let uu____1411 = (binders_to_string " " bs)
in (

let uu____1412 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1411 uu____1412)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1419 = (bv_to_string xt)
in (

let uu____1420 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1423 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1419 uu____1420 uu____1423))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1448 = (term_to_string t)
in (

let uu____1449 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1448 uu____1449)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1468 = (lbs_to_string [] lbs)
in (

let uu____1469 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1468 uu____1469)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1530 = (

let uu____1531 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1531 (FStar_Util.dflt "default")))
in (

let uu____1536 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1530 uu____1536)))
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

let uu____1552 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1552))
end)
in (

let uu____1553 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1553 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1592 = (term_to_string head1)
in (

let uu____1593 = (

let uu____1594 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1630 -> (match (uu____1630) with
| (p, wopt, e) -> begin
(

let uu____1646 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1647 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1649 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1649))
end)
in (

let uu____1650 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1646 uu____1647 uu____1650))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1594))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1592 uu____1593)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1657 = (FStar_Options.print_universes ())
in (match (uu____1657) with
| true -> begin
(

let uu____1658 = (term_to_string t)
in (

let uu____1659 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1658 uu____1659)))
end
| uu____1660 -> begin
(term_to_string t)
end))
end
| uu____1661 -> begin
(tag_of_term x2)
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1663 = (

let uu____1664 = (FStar_Options.ugly ())
in (not (uu____1664)))
in (match (uu____1663) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_pat x)
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1667 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1686 = (fv_to_string l)
in (

let uu____1687 = (

let uu____1688 = (FStar_List.map (fun uu____1699 -> (match (uu____1699) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1707 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1688 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1686 uu____1687)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1711) -> begin
(

let uu____1716 = (FStar_Options.print_bound_var_types ())
in (match (uu____1716) with
| true -> begin
(

let uu____1717 = (bv_to_string x1)
in (

let uu____1718 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1717 uu____1718)))
end
| uu____1719 -> begin
(

let uu____1720 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1720))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1722 = (FStar_Options.print_bound_var_types ())
in (match (uu____1722) with
| true -> begin
(

let uu____1723 = (bv_to_string x1)
in (

let uu____1724 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1723 uu____1724)))
end
| uu____1725 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1728 = (FStar_Options.print_real_names ())
in (match (uu____1728) with
| true -> begin
(

let uu____1729 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1729))
end
| uu____1730 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1748 = (FStar_Options.print_universes ())
in (match (uu____1748) with
| true -> begin
(

let uu____1755 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1773 = (

let uu____1778 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1778))
in (match (uu____1773) with
| (us, td) -> begin
(

let uu____1781 = (

let uu____1790 = (

let uu____1791 = (FStar_Syntax_Subst.compress td)
in uu____1791.FStar_Syntax_Syntax.n)
in (match (uu____1790) with
| FStar_Syntax_Syntax.Tm_app (uu____1802, ((t, uu____1804))::((d, uu____1806))::[]) -> begin
((t), (d))
end
| uu____1849 -> begin
(failwith "Impossibe")
end))
in (match (uu____1781) with
| (t, d) -> begin
(

let uu___210_1868 = lb
in {FStar_Syntax_Syntax.lbname = uu___210_1868.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___210_1868.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____1755)))
end
| uu____1873 -> begin
lbs
end))
in (

let uu____1874 = (quals_to_string' quals)
in (

let uu____1875 = (

let uu____1876 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1891 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1892 = (

let uu____1893 = (FStar_Options.print_universes ())
in (match (uu____1893) with
| true -> begin
(

let uu____1894 = (

let uu____1895 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1895 ">"))
in (Prims.strcat "<" uu____1894))
end
| uu____1896 -> begin
""
end))
in (

let uu____1897 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1898 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1891 uu____1892 uu____1897 uu____1898))))))))
in (FStar_Util.concat_l "\n and " uu____1876))
in (FStar_Util.format3 "%slet %s %s" uu____1874 (match ((FStar_Pervasives_Native.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1903 -> begin
""
end) uu____1875)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1905 = (FStar_Options.print_effect_args ())
in (match (uu____1905) with
| true -> begin
(

let uu____1906 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1906))
end
| uu____1907 -> begin
(

let uu____1908 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1909 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1908 uu____1909)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___204_1911 -> (match (uu___204_1911) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1914 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____1919 = (

let uu____1920 = (FStar_Options.ugly ())
in (not (uu____1920)))
in (match (uu____1919) with
| true -> begin
(

let uu____1921 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1921) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1926 -> begin
(

let uu____1927 = b
in (match (uu____1927) with
| (a, imp) -> begin
(

let uu____1930 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1930) with
| true -> begin
(

let uu____1931 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1931))
end
| uu____1932 -> begin
(

let uu____1933 = ((not (is_arrow)) && (

let uu____1935 = (FStar_Options.print_bound_var_types ())
in (not (uu____1935))))
in (match (uu____1933) with
| true -> begin
(

let uu____1936 = (nm_to_string a)
in (imp_to_string uu____1936 imp))
end
| uu____1937 -> begin
(

let uu____1938 = (

let uu____1939 = (nm_to_string a)
in (

let uu____1940 = (

let uu____1941 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1941))
in (Prims.strcat uu____1939 uu____1940)))
in (imp_to_string uu____1938 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____1947 = (FStar_Options.print_implicits ())
in (match (uu____1947) with
| true -> begin
bs
end
| uu____1948 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(

let uu____1949 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____1949 (FStar_String.concat sep)))
end
| uu____1956 -> begin
(

let uu____1957 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1957 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___205_1964 -> (match (uu___205_1964) with
| (a, imp) -> begin
(

let uu____1977 = (term_to_string a)
in (imp_to_string uu____1977 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____1980 = (FStar_Options.print_implicits ())
in (match (uu____1980) with
| true -> begin
args
end
| uu____1981 -> begin
(filter_imp args)
end))
in (

let uu____1984 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1984 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____1998 = (

let uu____1999 = (FStar_Options.ugly ())
in (not (uu____1999)))
in (match (uu____1998) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2002 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2013 = (

let uu____2014 = (FStar_Syntax_Subst.compress t)
in uu____2014.FStar_Syntax_Syntax.n)
in (match (uu____2013) with
| FStar_Syntax_Syntax.Tm_type (uu____2017) when (

let uu____2018 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2018))) -> begin
(term_to_string t)
end
| uu____2019 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2021 = (univ_to_string u)
in (

let uu____2022 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2021 uu____2022)))
end
| uu____2023 -> begin
(

let uu____2026 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2026))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2037 = (

let uu____2038 = (FStar_Syntax_Subst.compress t)
in uu____2038.FStar_Syntax_Syntax.n)
in (match (uu____2037) with
| FStar_Syntax_Syntax.Tm_type (uu____2041) when (

let uu____2042 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2042))) -> begin
(term_to_string t)
end
| uu____2043 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2045 = (univ_to_string u)
in (

let uu____2046 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2045 uu____2046)))
end
| uu____2047 -> begin
(

let uu____2050 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2050))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2053 = (FStar_Options.print_effect_args ())
in (match (uu____2053) with
| true -> begin
(

let uu____2054 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2055 = (

let uu____2056 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2056 (FStar_String.concat ", ")))
in (

let uu____2063 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2064 = (

let uu____2065 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2065 (FStar_String.concat ", ")))
in (

let uu____2086 = (

let uu____2087 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2087 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2054 uu____2055 uu____2063 uu____2064 uu____2086))))))
end
| uu____2096 -> begin
(

let uu____2097 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___206_2101 -> (match (uu___206_2101) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2102 -> begin
false
end)))) && (

let uu____2104 = (FStar_Options.print_effect_args ())
in (not (uu____2104))))
in (match (uu____2097) with
| true -> begin
(

let uu____2105 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2105))
end
| uu____2106 -> begin
(

let uu____2107 = (((

let uu____2110 = (FStar_Options.print_effect_args ())
in (not (uu____2110))) && (

let uu____2112 = (FStar_Options.print_implicits ())
in (not (uu____2112)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2107) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2113 -> begin
(

let uu____2114 = ((

let uu____2117 = (FStar_Options.print_effect_args ())
in (not (uu____2117))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___207_2121 -> (match (uu___207_2121) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2122 -> begin
false
end)))))
in (match (uu____2114) with
| true -> begin
(

let uu____2123 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2123))
end
| uu____2124 -> begin
(

let uu____2125 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2126 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2125 uu____2126)))
end))
end))
end))
end))
in (

let dec = (

let uu____2128 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___208_2138 -> (match (uu___208_2138) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2144 = (

let uu____2145 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2145))
in (uu____2144)::[])
end
| uu____2146 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2128 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2150) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2160 = (FStar_Options.print_universes ())
in (match (uu____2160) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2161 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2166 = (

let uu____2167 = (FStar_Options.ugly ())
in (not (uu____2167)))
in (match (uu____2166) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2170 -> begin
(

let uu____2171 = s
in (match (uu____2171) with
| (us, t) -> begin
(

let uu____2178 = (

let uu____2179 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2179))
in (

let uu____2180 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2178 uu____2180)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2185 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2186 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2187 = (

let uu____2188 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2188))
in (

let uu____2189 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2190 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2185 uu____2186 uu____2187 uu____2189 uu____2190)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2211 = (

let uu____2212 = (FStar_Options.ugly ())
in (not (uu____2212)))
in (match (uu____2211) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2215 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2224 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2224 (FStar_String.concat ",\n\t"))))
in (

let uu____2233 = (

let uu____2236 = (

let uu____2239 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2240 = (

let uu____2243 = (

let uu____2244 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2244))
in (

let uu____2245 = (

let uu____2248 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2249 = (

let uu____2252 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2253 = (

let uu____2256 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2257 = (

let uu____2260 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2261 = (

let uu____2264 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2265 = (

let uu____2268 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2269 = (

let uu____2272 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2273 = (

let uu____2276 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2277 = (

let uu____2280 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2281 = (

let uu____2284 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2285 = (

let uu____2288 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2289 = (

let uu____2292 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2293 = (

let uu____2296 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2297 = (

let uu____2300 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2301 = (

let uu____2304 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2305 = (

let uu____2308 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2308)::[])
in (uu____2304)::uu____2305))
in (uu____2300)::uu____2301))
in (uu____2296)::uu____2297))
in (uu____2292)::uu____2293))
in (uu____2288)::uu____2289))
in (uu____2284)::uu____2285))
in (uu____2280)::uu____2281))
in (uu____2276)::uu____2277))
in (uu____2272)::uu____2273))
in (uu____2268)::uu____2269))
in (uu____2264)::uu____2265))
in (uu____2260)::uu____2261))
in (uu____2256)::uu____2257))
in (uu____2252)::uu____2253))
in (uu____2248)::uu____2249))
in (uu____2243)::uu____2245))
in (uu____2239)::uu____2240))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2309 -> begin
""
end))::uu____2236)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2233)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2322 = (

let uu____2323 = (FStar_Options.ugly ())
in (not (uu____2323)))
in (match (uu____2322) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2329 -> begin
""
end))
end
| uu____2332 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2339, uu____2340) -> begin
(

let uu____2349 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2350 = (binders_to_string " " tps)
in (

let uu____2351 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____2349 lid.FStar_Ident.str uu____2350 uu____2351))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2355, uu____2356, uu____2357) -> begin
(

let uu____2362 = (FStar_Options.print_universes ())
in (match (uu____2362) with
| true -> begin
(

let uu____2363 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____2363) with
| (univs2, t1) -> begin
(

let uu____2370 = (univ_names_to_string univs2)
in (

let uu____2371 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2370 lid.FStar_Ident.str uu____2371)))
end))
end
| uu____2372 -> begin
(

let uu____2373 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2373))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2377 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____2377) with
| (univs2, t1) -> begin
(

let uu____2384 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2385 = (

let uu____2386 = (FStar_Options.print_universes ())
in (match (uu____2386) with
| true -> begin
(

let uu____2387 = (univ_names_to_string univs2)
in (FStar_Util.format1 "<%s>" uu____2387))
end
| uu____2388 -> begin
""
end))
in (

let uu____2389 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2384 lid.FStar_Ident.str uu____2385 uu____2389))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2391, f) -> begin
(

let uu____2393 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2393))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2395) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2401 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2401))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2403) -> begin
(

let uu____2412 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2412 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2430) -> begin
lift_wp
end
| (uu____2437, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2445 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2445) with
| (us, t) -> begin
(

let uu____2456 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2457 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2458 = (univ_names_to_string us)
in (

let uu____2459 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2456 uu____2457 uu____2458 uu____2459)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____2469 = (FStar_Options.print_universes ())
in (match (uu____2469) with
| true -> begin
(

let uu____2470 = (

let uu____2475 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2475))
in (match (uu____2470) with
| (univs2, t) -> begin
(

let uu____2478 = (

let uu____2491 = (

let uu____2492 = (FStar_Syntax_Subst.compress t)
in uu____2492.FStar_Syntax_Syntax.n)
in (match (uu____2491) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2533 -> begin
(failwith "impossible")
end))
in (match (uu____2478) with
| (tps1, c1) -> begin
(

let uu____2564 = (sli l)
in (

let uu____2565 = (univ_names_to_string univs2)
in (

let uu____2566 = (binders_to_string " " tps1)
in (

let uu____2567 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2564 uu____2565 uu____2566 uu____2567)))))
end))
end))
end
| uu____2568 -> begin
(

let uu____2569 = (sli l)
in (

let uu____2570 = (binders_to_string " " tps)
in (

let uu____2571 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2569 uu____2570 uu____2571))))
end))
end)
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2580 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2580 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2585, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2587; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2589; FStar_Syntax_Syntax.lbdef = uu____2590})::[]), uu____2591) -> begin
(

let uu____2614 = (lbname_to_string lb)
in (

let uu____2615 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2614 uu____2615)))
end
| uu____2616 -> begin
(

let uu____2617 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2617 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____2632 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____2633 = (

let uu____2634 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____2634 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____2632 uu____2633))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___209_2642 -> (match (uu___209_2642) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2645 = (FStar_Util.string_of_int i)
in (

let uu____2646 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2645 uu____2646)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2649 = (bv_to_string x)
in (

let uu____2650 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2649 uu____2650)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2657 = (bv_to_string x)
in (

let uu____2658 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____2657 uu____2658)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2661 = (FStar_Util.string_of_int i)
in (

let uu____2662 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2661 uu____2662)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2665 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2665))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2670 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2670 (FStar_String.concat "; "))))


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

let uu____2742 = (f x)
in (FStar_Util.string_builder_append strb uu____2742));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2749 = (f x1)
in (FStar_Util.string_builder_append strb uu____2749));
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

let uu____2785 = (f x)
in (FStar_Util.string_builder_append strb uu____2785));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2792 = (f x1)
in (FStar_Util.string_builder_append strb uu____2792));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





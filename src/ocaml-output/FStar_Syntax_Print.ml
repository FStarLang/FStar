
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___204_4 -> (match (uu___204_4) with
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


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____123 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____138 -> begin
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


let is_inr = (fun uu___205_195 -> (match (uu___205_195) with
| FStar_Util.Inl (uu____198) -> begin
false
end
| FStar_Util.Inr (uu____199) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___206_235 -> (match (uu___206_235) with
| (uu____239, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____240))) -> begin
false
end
| uu____242 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____254 = (

let uu____255 = (FStar_Syntax_Subst.compress e)
in uu____255.FStar_Syntax_Syntax.n)
in (match (uu____254) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____301 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
in (match (uu____301) with
| true -> begin
(

let uu____312 = (

let uu____317 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____317))
in (match (uu____312) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____331 = (

let uu____335 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____335)::xs)
in FStar_Pervasives_Native.Some (uu____331))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____351 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____355 -> begin
(

let uu____356 = (is_lex_top e)
in (match (uu____356) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____366 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____395 = (f hd1)
in (match (uu____395) with
| true -> begin
hd1
end
| uu____396 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____411 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____411)))


let infix_prim_op_to_string = (fun e -> (

let uu____433 = (get_lid e)
in (find_lid uu____433 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (

let uu____447 = (get_lid e)
in (find_lid uu____447 unary_prim_ops)))


let quant_to_string = (fun t -> (

let uu____461 = (get_lid t)
in (find_lid uu____461 quants)))


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
| uu____467 -> begin
"false"
end)
end
| FStar_Const.Const_float (x1) -> begin
(FStar_Util.string_of_float x1)
end
| FStar_Const.Const_string (bytes, uu____470) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____473) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x1, uu____478) -> begin
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

let uu____488 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" uu____488))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___207_492 -> (match (uu___207_492) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____500 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____500))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____502 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____502))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____504 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____504))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____505) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____510) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____511) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____512) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____522) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____530) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____535) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____545) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____560) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____578) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____586) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____597, m) -> begin
(

let uu____623 = (FStar_ST.read m)
in (match (uu____623) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____634) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____639) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____648 = (FStar_Options.hide_uvar_nums ())
in (match (uu____648) with
| true -> begin
"?"
end
| uu____649 -> begin
(

let uu____650 = (

let uu____651 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____651 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____650))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____656 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____657 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____656 uu____657))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____662 = (FStar_Options.hide_uvar_nums ())
in (match (uu____662) with
| true -> begin
"?"
end
| uu____663 -> begin
(

let uu____664 = (

let uu____665 = (

let uu____666 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____666 FStar_Util.string_of_int))
in (

let uu____667 = (

let uu____668 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____668))
in (Prims.strcat uu____665 uu____667)))
in (Prims.strcat "?" uu____664))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____682 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____682) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____688 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____694 = (

let uu____695 = (FStar_Options.ugly ())
in (not (uu____695)))
in (match (uu____694) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____698 -> begin
(

let uu____699 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____699) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____707 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____707))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____709 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____709) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____718 = (univ_to_string u2)
in (

let uu____719 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____718 uu____719)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____722 = (

let uu____723 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____723 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____722))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____732 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____732 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____741 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____741 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___208_749 -> (match (uu___208_749) with
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

let uu____751 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____751))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____754 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____754 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____761 = (

let uu____762 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____762))
in (

let uu____764 = (

let uu____765 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____765 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____761 uu____764)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____776 = (

let uu____777 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____777))
in (

let uu____779 = (

let uu____780 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____780 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____776 uu____779)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____786 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____786))
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
| uu____794 -> begin
(

let uu____796 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____796 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____807 -> begin
(

let uu____809 = (quals_to_string quals)
in (Prims.strcat uu____809 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____857 = (

let uu____858 = (FStar_Options.ugly ())
in (not (uu____858)))
in (match (uu____857) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____861 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____864 = (FStar_Options.print_implicits ())
in (match (uu____864) with
| true -> begin
x1
end
| uu____865 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____866) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____881, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____908 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____926 = (FStar_All.pipe_right args (FStar_List.map (fun uu____937 -> (match (uu____937) with
| (t1, uu____941) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____926 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____908 (FStar_String.concat "\\/")))
in (

let uu____944 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____944)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____956 = (tag_of_term t)
in (

let uu____957 = (sli m)
in (

let uu____958 = (term_to_string t')
in (

let uu____959 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____956 uu____957 uu____958 uu____959)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____972 = (tag_of_term t)
in (

let uu____973 = (term_to_string t')
in (

let uu____974 = (sli m0)
in (

let uu____975 = (sli m1)
in (

let uu____976 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____972 uu____973 uu____974 uu____975 uu____976))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_alien (uu____978, s)) -> begin
(FStar_Util.format1 "(Meta_alien \"%s\")" s)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____992 = (FStar_Range.string_of_range r)
in (

let uu____993 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____992 uu____993)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____995) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1001 = (db_to_string x3)
in (

let uu____1002 = (

let uu____1003 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1003))
in (Prims.strcat uu____1001 uu____1002)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____1007) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1026 = (FStar_Options.print_universes ())
in (match (uu____1026) with
| true -> begin
(

let uu____1027 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1027))
end
| uu____1028 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1041 = (binders_to_string " -> " bs)
in (

let uu____1042 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1041 uu____1042)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1059 = (binders_to_string " " bs)
in (

let uu____1060 = (term_to_string t2)
in (

let uu____1061 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1064 -> begin
(

let uu____1065 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1065))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1059 uu____1060 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1061))))
end
| uu____1068 -> begin
(

let uu____1070 = (binders_to_string " " bs)
in (

let uu____1071 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1070 uu____1071)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1078 = (bv_to_string xt)
in (

let uu____1079 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1082 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1078 uu____1079 uu____1082))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1101 = (term_to_string t)
in (

let uu____1102 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1101 uu____1102)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1115 = (lbs_to_string [] lbs)
in (

let uu____1116 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1115 uu____1116)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1164 = (

let uu____1165 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1165 (FStar_Util.dflt "default")))
in (

let uu____1168 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1164 uu____1168)))
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

let uu____1184 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1184))
end)
in (

let uu____1185 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1185 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1212 = (term_to_string head1)
in (

let uu____1213 = (

let uu____1214 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1238 -> (match (uu____1238) with
| (p, wopt, e) -> begin
(

let uu____1248 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1249 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1251 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1251))
end)
in (

let uu____1252 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1248 uu____1249 uu____1252))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1214))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1212 uu____1213)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1259 = (FStar_Options.print_universes ())
in (match (uu____1259) with
| true -> begin
(

let uu____1260 = (term_to_string t)
in (

let uu____1261 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1260 uu____1261)))
end
| uu____1262 -> begin
(term_to_string t)
end))
end
| uu____1263 -> begin
(tag_of_term x2)
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1265 = (

let uu____1266 = (FStar_Options.ugly ())
in (not (uu____1266)))
in (match (uu____1265) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_pat x)
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1269 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1280 = (fv_to_string l)
in (

let uu____1281 = (

let uu____1282 = (FStar_List.map (fun uu____1290 -> (match (uu____1290) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1296 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1282 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1280 uu____1281)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1299) -> begin
(

let uu____1304 = (FStar_Options.print_bound_var_types ())
in (match (uu____1304) with
| true -> begin
(

let uu____1305 = (bv_to_string x1)
in (

let uu____1306 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1305 uu____1306)))
end
| uu____1307 -> begin
(

let uu____1308 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1308))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1310 = (FStar_Options.print_bound_var_types ())
in (match (uu____1310) with
| true -> begin
(

let uu____1311 = (bv_to_string x1)
in (

let uu____1312 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1311 uu____1312)))
end
| uu____1313 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1316 = (FStar_Options.print_real_names ())
in (match (uu____1316) with
| true -> begin
(

let uu____1317 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1317))
end
| uu____1318 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1329 = (FStar_Options.print_universes ())
in (match (uu____1329) with
| true -> begin
(

let uu____1333 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1347 = (

let uu____1350 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1350))
in (match (uu____1347) with
| (us, td) -> begin
(

let uu____1353 = (

let uu____1360 = (

let uu____1361 = (FStar_Syntax_Subst.compress td)
in uu____1361.FStar_Syntax_Syntax.n)
in (match (uu____1360) with
| FStar_Syntax_Syntax.Tm_app (uu____1370, ((t, uu____1372))::((d, uu____1374))::[]) -> begin
((t), (d))
end
| uu____1408 -> begin
(failwith "Impossibe")
end))
in (match (uu____1353) with
| (t, d) -> begin
(

let uu___215_1425 = lb
in {FStar_Syntax_Syntax.lbname = uu___215_1425.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___215_1425.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____1333)))
end
| uu____1428 -> begin
lbs
end))
in (

let uu____1429 = (quals_to_string' quals)
in (

let uu____1430 = (

let uu____1431 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1442 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1443 = (

let uu____1444 = (FStar_Options.print_universes ())
in (match (uu____1444) with
| true -> begin
(

let uu____1445 = (

let uu____1446 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1446 ">"))
in (Prims.strcat "<" uu____1445))
end
| uu____1447 -> begin
""
end))
in (

let uu____1448 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1449 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1442 uu____1443 uu____1448 uu____1449))))))))
in (FStar_Util.concat_l "\n and " uu____1431))
in (FStar_Util.format3 "%slet %s %s" uu____1429 (match ((FStar_Pervasives_Native.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1453 -> begin
""
end) uu____1430)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1455 = (FStar_Options.print_effect_args ())
in (match (uu____1455) with
| true -> begin
(

let uu____1456 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1456))
end
| uu____1457 -> begin
(

let uu____1458 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1459 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1458 uu____1459)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___209_1461 -> (match (uu___209_1461) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1463 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____1467 = (

let uu____1468 = (FStar_Options.ugly ())
in (not (uu____1468)))
in (match (uu____1467) with
| true -> begin
(

let uu____1469 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1469) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1473 -> begin
(

let uu____1474 = b
in (match (uu____1474) with
| (a, imp) -> begin
(

let uu____1477 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1477) with
| true -> begin
(

let uu____1478 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1478))
end
| uu____1479 -> begin
(

let uu____1480 = ((not (is_arrow)) && (

let uu____1482 = (FStar_Options.print_bound_var_types ())
in (not (uu____1482))))
in (match (uu____1480) with
| true -> begin
(

let uu____1483 = (nm_to_string a)
in (imp_to_string uu____1483 imp))
end
| uu____1484 -> begin
(

let uu____1485 = (

let uu____1486 = (nm_to_string a)
in (

let uu____1487 = (

let uu____1488 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1488))
in (Prims.strcat uu____1486 uu____1487)))
in (imp_to_string uu____1485 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____1494 = (FStar_Options.print_implicits ())
in (match (uu____1494) with
| true -> begin
bs
end
| uu____1495 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(

let uu____1496 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____1496 (FStar_String.concat sep)))
end
| uu____1500 -> begin
(

let uu____1501 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1501 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___210_1505 -> (match (uu___210_1505) with
| (a, imp) -> begin
(

let uu____1513 = (term_to_string a)
in (imp_to_string uu____1513 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____1516 = (FStar_Options.print_implicits ())
in (match (uu____1516) with
| true -> begin
args
end
| uu____1517 -> begin
(filter_imp args)
end))
in (

let uu____1520 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1520 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____1528 = (

let uu____1529 = (FStar_Options.ugly ())
in (not (uu____1529)))
in (match (uu____1528) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1532 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____1541 = (

let uu____1542 = (FStar_Syntax_Subst.compress t)
in uu____1542.FStar_Syntax_Syntax.n)
in (match (uu____1541) with
| FStar_Syntax_Syntax.Tm_type (uu____1545) when (

let uu____1546 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____1546))) -> begin
(term_to_string t)
end
| uu____1547 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____1549 = (univ_to_string u)
in (

let uu____1550 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____1549 uu____1550)))
end
| uu____1551 -> begin
(

let uu____1553 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____1553))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____1562 = (

let uu____1563 = (FStar_Syntax_Subst.compress t)
in uu____1563.FStar_Syntax_Syntax.n)
in (match (uu____1562) with
| FStar_Syntax_Syntax.Tm_type (uu____1566) when (

let uu____1567 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____1567))) -> begin
(term_to_string t)
end
| uu____1568 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____1570 = (univ_to_string u)
in (

let uu____1571 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____1570 uu____1571)))
end
| uu____1572 -> begin
(

let uu____1574 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____1574))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____1577 = (FStar_Options.print_effect_args ())
in (match (uu____1577) with
| true -> begin
(

let uu____1578 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1579 = (

let uu____1580 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____1580 (FStar_String.concat ", ")))
in (

let uu____1584 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____1585 = (

let uu____1586 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1586 (FStar_String.concat ", ")))
in (

let uu____1598 = (

let uu____1599 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____1599 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1578 uu____1579 uu____1584 uu____1585 uu____1598))))))
end
| uu____1604 -> begin
(

let uu____1605 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___211_1608 -> (match (uu___211_1608) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1609 -> begin
false
end)))) && (

let uu____1611 = (FStar_Options.print_effect_args ())
in (not (uu____1611))))
in (match (uu____1605) with
| true -> begin
(

let uu____1612 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____1612))
end
| uu____1613 -> begin
(

let uu____1614 = (((

let uu____1617 = (FStar_Options.print_effect_args ())
in (not (uu____1617))) && (

let uu____1619 = (FStar_Options.print_implicits ())
in (not (uu____1619)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____1614) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____1620 -> begin
(

let uu____1621 = ((

let uu____1624 = (FStar_Options.print_effect_args ())
in (not (uu____1624))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___212_1627 -> (match (uu___212_1627) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1628 -> begin
false
end)))))
in (match (uu____1621) with
| true -> begin
(

let uu____1629 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____1629))
end
| uu____1630 -> begin
(

let uu____1631 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1632 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____1631 uu____1632)))
end))
end))
end))
end))
in (

let dec = (

let uu____1634 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___213_1641 -> (match (uu___213_1641) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____1646 = (

let uu____1647 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____1647))
in (uu____1646)::[])
end
| uu____1648 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1634 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____1651) -> begin
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1661 = (FStar_Options.print_universes ())
in (match (uu____1661) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1662 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____1667 = (

let uu____1668 = (FStar_Options.ugly ())
in (not (uu____1668)))
in (match (uu____1667) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1671 -> begin
(

let uu____1672 = s
in (match (uu____1672) with
| (us, t) -> begin
(

let uu____1677 = (

let uu____1678 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____1678))
in (

let uu____1679 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____1677 uu____1679)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____1684 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____1685 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____1686 = (

let uu____1687 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____1687))
in (

let uu____1688 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1689 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1684 uu____1685 uu____1686 uu____1688 uu____1689)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____1708 = (

let uu____1709 = (FStar_Options.ugly ())
in (not (uu____1709)))
in (match (uu____1708) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1712 -> begin
(

let actions_to_string = (fun actions -> (

let uu____1719 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____1719 (FStar_String.concat ",\n\t"))))
in (

let uu____1724 = (

let uu____1726 = (

let uu____1728 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1729 = (

let uu____1731 = (

let uu____1732 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____1732))
in (

let uu____1733 = (

let uu____1735 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____1736 = (

let uu____1738 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____1739 = (

let uu____1741 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1742 = (

let uu____1744 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____1745 = (

let uu____1747 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____1748 = (

let uu____1750 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____1751 = (

let uu____1753 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____1754 = (

let uu____1756 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____1757 = (

let uu____1759 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____1760 = (

let uu____1762 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____1763 = (

let uu____1765 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____1766 = (

let uu____1768 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____1769 = (

let uu____1771 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____1772 = (

let uu____1774 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____1775 = (

let uu____1777 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____1778 = (

let uu____1780 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____1780)::[])
in (uu____1777)::uu____1778))
in (uu____1774)::uu____1775))
in (uu____1771)::uu____1772))
in (uu____1768)::uu____1769))
in (uu____1765)::uu____1766))
in (uu____1762)::uu____1763))
in (uu____1759)::uu____1760))
in (uu____1756)::uu____1757))
in (uu____1753)::uu____1754))
in (uu____1750)::uu____1751))
in (uu____1747)::uu____1748))
in (uu____1744)::uu____1745))
in (uu____1741)::uu____1742))
in (uu____1738)::uu____1739))
in (uu____1735)::uu____1736))
in (uu____1731)::uu____1733))
in (uu____1728)::uu____1729))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1781 -> begin
""
end))::uu____1726)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____1724)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____1794 = (

let uu____1795 = (FStar_Options.ugly ())
in (not (uu____1795)))
in (match (uu____1794) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____1800 -> begin
""
end))
end
| uu____1802 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____1809, uu____1810) -> begin
(

let uu____1815 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1816 = (binders_to_string " " tps)
in (

let uu____1817 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____1815 lid.FStar_Ident.str uu____1816 uu____1817))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____1821, uu____1822, uu____1823) -> begin
(

let uu____1826 = (FStar_Options.print_universes ())
in (match (uu____1826) with
| true -> begin
(

let uu____1827 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1827) with
| (univs2, t1) -> begin
(

let uu____1832 = (univ_names_to_string univs2)
in (

let uu____1833 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____1832 lid.FStar_Ident.str uu____1833)))
end))
end
| uu____1834 -> begin
(

let uu____1835 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____1835))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____1839 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1839) with
| (univs2, t1) -> begin
(

let uu____1844 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1845 = (

let uu____1846 = (FStar_Options.print_universes ())
in (match (uu____1846) with
| true -> begin
(

let uu____1847 = (univ_names_to_string univs2)
in (FStar_Util.format1 "<%s>" uu____1847))
end
| uu____1848 -> begin
""
end))
in (

let uu____1849 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____1844 lid.FStar_Ident.str uu____1845 uu____1849))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____1851, f) -> begin
(

let uu____1853 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1853))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1855) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1859 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____1859))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1861) -> begin
(

let uu____1866 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____1866 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____1878) -> begin
lift_wp
end
| (uu____1882, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____1887 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____1887) with
| (us, t) -> begin
(

let uu____1894 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____1895 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____1896 = (univ_names_to_string us)
in (

let uu____1897 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1894 uu____1895 uu____1896 uu____1897)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____1905 = (FStar_Options.print_universes ())
in (match (uu____1905) with
| true -> begin
(

let uu____1906 = (

let uu____1909 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____1909))
in (match (uu____1906) with
| (univs2, t) -> begin
(

let uu____1916 = (

let uu____1924 = (

let uu____1925 = (FStar_Syntax_Subst.compress t)
in uu____1925.FStar_Syntax_Syntax.n)
in (match (uu____1924) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____1952 -> begin
(failwith "impossible")
end))
in (match (uu____1916) with
| (tps1, c1) -> begin
(

let uu____1972 = (sli l)
in (

let uu____1973 = (univ_names_to_string univs2)
in (

let uu____1974 = (binders_to_string " " tps1)
in (

let uu____1975 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____1972 uu____1973 uu____1974 uu____1975)))))
end))
end))
end
| uu____1976 -> begin
(

let uu____1977 = (sli l)
in (

let uu____1978 = (binders_to_string " " tps)
in (

let uu____1979 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____1977 uu____1978 uu____1979))))
end))
end)
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____1988 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____1988 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1993, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1995; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1997; FStar_Syntax_Syntax.lbdef = uu____1998})::[]), uu____1999) -> begin
(

let uu____2013 = (lbname_to_string lb)
in (

let uu____2014 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2013 uu____2014)))
end
| uu____2015 -> begin
(

let uu____2016 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2016 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____2027 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____2028 = (

let uu____2029 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____2029 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____2027 uu____2028))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___214_2035 -> (match (uu___214_2035) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2038 = (FStar_Util.string_of_int i)
in (

let uu____2039 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2038 uu____2039)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2042 = (bv_to_string x)
in (

let uu____2043 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2042 uu____2043)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2050 = (bv_to_string x)
in (

let uu____2051 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____2050 uu____2051)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2054 = (FStar_Util.string_of_int i)
in (

let uu____2055 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2054 uu____2055)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2058 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2058))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2063 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2063 (FStar_String.concat "; "))))


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


let list_to_string = (fun f elts -> (match (elts) with
| [] -> begin
"[]"
end
| (x)::xs -> begin
(

let strb = (FStar_Util.new_string_builder ())
in ((FStar_Util.string_builder_append strb "[");
(

let uu____2117 = (f x)
in (FStar_Util.string_builder_append strb uu____2117));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2124 = (f x1)
in (FStar_Util.string_builder_append strb uu____2124));
)) xs);
(FStar_Util.string_builder_append strb "]");
(FStar_Util.string_of_string_builder strb);
))
end))


let set_to_string = (fun f s -> (

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

let uu____2156 = (f x)
in (FStar_Util.string_builder_append strb uu____2156));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2163 = (f x1)
in (FStar_Util.string_builder_append strb uu____2163));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





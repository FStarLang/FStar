
open Prims
open FStar_Pervasives

let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____4 = (FStar_Options.print_real_names ())
in (match (uu____4) with
| true -> begin
l.FStar_Ident.str
end
| uu____5 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____19 = (

let uu____20 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____20))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____19)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____24 = (FStar_Options.print_real_names ())
in (match (uu____24) with
| true -> begin
(bv_to_string bv)
end
| uu____25 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____29 = (

let uu____30 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____30))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____29)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____109 -> begin
false
end))


let get_lid = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____126 -> begin
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


let is_inr = (fun uu___200_173 -> (match (uu___200_173) with
| FStar_Util.Inl (uu____176) -> begin
false
end
| FStar_Util.Inr (uu____177) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___201_208 -> (match (uu___201_208) with
| (uu____212, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____213))) -> begin
false
end
| uu____215 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____226 = (

let uu____227 = (FStar_Syntax_Subst.compress e)
in uu____227.FStar_Syntax_Syntax.n)
in (match (uu____226) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____273 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
in (match (uu____273) with
| true -> begin
(

let uu____282 = (

let uu____287 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____287))
in (match (uu____282) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____301 = (

let uu____305 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____305)::xs)
in FStar_Pervasives_Native.Some (uu____301))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____321 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____325 -> begin
(

let uu____326 = (is_lex_top e)
in (match (uu____326) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____336 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____362 = (f hd1)
in (match (uu____362) with
| true -> begin
hd1
end
| uu____363 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____376 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____376)))


let infix_prim_op_to_string = (fun e -> (

let uu____395 = (get_lid e)
in (find_lid uu____395 infix_prim_ops)))


let unary_prim_op_to_string = (fun e -> (

let uu____407 = (get_lid e)
in (find_lid uu____407 unary_prim_ops)))


let quant_to_string = (fun t -> (

let uu____419 = (get_lid t)
in (find_lid uu____419 quants)))


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
| uu____424 -> begin
"false"
end)
end
| FStar_Const.Const_float (x1) -> begin
(FStar_Util.string_of_float x1)
end
| FStar_Const.Const_string (bytes, uu____427) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____430) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x1, uu____435) -> begin
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

let uu____445 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" uu____445))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___202_448 -> (match (uu___202_448) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____459 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____459))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____461 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____461))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____463 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____463))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____468) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____473) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____474) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____475) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____490) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____498) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____503) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____513) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____529) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____547) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____555) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____564, m) -> begin
(

let uu____602 = (FStar_ST.read m)
in (match (uu____602) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____613) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____618) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> (

let uu____632 = (FStar_Options.hide_uvar_nums ())
in (match (uu____632) with
| true -> begin
"?"
end
| uu____633 -> begin
(

let uu____634 = (

let uu____635 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____635 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____634))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____645 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____645) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____651 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____656 = (

let uu____657 = (FStar_Options.ugly ())
in (not (uu____657)))
in (match (uu____656) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____660 -> begin
(

let uu____661 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____661) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____668 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____668))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____670 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____670) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____679 = (univ_to_string u2)
in (

let uu____680 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____679 uu____680)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____683 = (

let uu____684 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____684 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____683))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____692 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____692 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____700 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____700 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___203_706 -> (match (uu___203_706) with
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

let uu____708 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____708))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____711 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____711 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____718 = (

let uu____719 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____719))
in (

let uu____721 = (

let uu____722 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____722 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____718 uu____721)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____733 = (

let uu____734 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____734))
in (

let uu____736 = (

let uu____737 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____737 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____733 uu____736)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____743 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____743))
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
| uu____750 -> begin
(

let uu____752 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____752 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____762 -> begin
(

let uu____764 = (quals_to_string quals)
in (Prims.strcat uu____764 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____812 = (

let uu____813 = (FStar_Options.ugly ())
in (not (uu____813)))
in (match (uu____812) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____816 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____819 = (FStar_Options.print_implicits ())
in (match (uu____819) with
| true -> begin
x1
end
| uu____820 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____821) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____842, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____869 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____885 = (FStar_All.pipe_right args (FStar_List.map (fun uu____893 -> (match (uu____893) with
| (t1, uu____897) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____885 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____869 (FStar_String.concat "\\/")))
in (

let uu____900 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____900)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____912 = (tag_of_term t)
in (

let uu____913 = (sli m)
in (

let uu____914 = (term_to_string t')
in (

let uu____915 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____912 uu____913 uu____914 uu____915)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____928 = (tag_of_term t)
in (

let uu____929 = (term_to_string t')
in (

let uu____930 = (sli m0)
in (

let uu____931 = (sli m1)
in (

let uu____932 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____928 uu____929 uu____930 uu____931 uu____932))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____941 = (FStar_Range.string_of_range r)
in (

let uu____942 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____941 uu____942)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____944) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(db_to_string x3)
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____953) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____971 = (FStar_Options.print_universes ())
in (match (uu____971) with
| true -> begin
(

let uu____972 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____972))
end
| uu____973 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____986 = (binders_to_string " -> " bs)
in (

let uu____987 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____986 uu____987)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1022 = (binders_to_string " " bs)
in (

let uu____1023 = (term_to_string t2)
in (

let uu____1024 = (

let uu____1025 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string uu____1025))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1022 uu____1023 uu____1024))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1038 = (binders_to_string " " bs)
in (

let uu____1039 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" uu____1038 uu____1039 l.FStar_Ident.str)))
end
| uu____1040 -> begin
(

let uu____1047 = (binders_to_string " " bs)
in (

let uu____1048 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1047 uu____1048)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1055 = (bv_to_string xt)
in (

let uu____1056 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1059 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1055 uu____1056 uu____1059))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1078 = (term_to_string t)
in (

let uu____1079 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1078 uu____1079)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1092 = (lbs_to_string [] lbs)
in (

let uu____1093 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1092 uu____1093)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1141 = (

let uu____1142 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1142 (FStar_Util.dflt "default")))
in (

let uu____1145 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1141 uu____1145)))
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

let uu____1161 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1161))
end)
in (

let uu____1162 = (term_to_string e)
in (FStar_Util.format3 "(%s <: %s %s)" uu____1162 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1191 = (term_to_string head1)
in (

let uu____1192 = (

let uu____1193 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1211 -> (match (uu____1211) with
| (p, wopt, e) -> begin
(

let uu____1221 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1222 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1224 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1224))
end)
in (

let uu____1225 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1221 uu____1222 uu____1225))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1193))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1191 uu____1192)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1232 = (FStar_Options.print_universes ())
in (match (uu____1232) with
| true -> begin
(

let uu____1233 = (term_to_string t)
in (

let uu____1234 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1233 uu____1234)))
end
| uu____1235 -> begin
(term_to_string t)
end))
end
| uu____1236 -> begin
(tag_of_term x2)
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1238 = (

let uu____1239 = (FStar_Options.ugly ())
in (not (uu____1239)))
in (match (uu____1238) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_pat x)
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1242 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1255 = (fv_to_string l)
in (

let uu____1256 = (

let uu____1257 = (FStar_List.map (fun uu____1261 -> (match (uu____1261) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1267 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1257 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1255 uu____1256)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1270) -> begin
(

let uu____1275 = (FStar_Options.print_bound_var_types ())
in (match (uu____1275) with
| true -> begin
(

let uu____1276 = (bv_to_string x1)
in (

let uu____1277 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1276 uu____1277)))
end
| uu____1278 -> begin
(

let uu____1279 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1279))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1281 = (FStar_Options.print_bound_var_types ())
in (match (uu____1281) with
| true -> begin
(

let uu____1282 = (bv_to_string x1)
in (

let uu____1283 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1282 uu____1283)))
end
| uu____1284 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1287 = (FStar_Options.print_real_names ())
in (match (uu____1287) with
| true -> begin
(

let uu____1288 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1288))
end
| uu____1289 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1300 = (FStar_Options.print_universes ())
in (match (uu____1300) with
| true -> begin
(

let uu____1304 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1310 = (

let uu____1313 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1313))
in (match (uu____1310) with
| (us, td) -> begin
(

let uu____1316 = (

let uu____1323 = (

let uu____1324 = (FStar_Syntax_Subst.compress td)
in uu____1324.FStar_Syntax_Syntax.n)
in (match (uu____1323) with
| FStar_Syntax_Syntax.Tm_app (uu____1333, ((t, uu____1335))::((d, uu____1337))::[]) -> begin
((t), (d))
end
| uu____1371 -> begin
(failwith "Impossibe")
end))
in (match (uu____1316) with
| (t, d) -> begin
(

let uu___210_1388 = lb
in {FStar_Syntax_Syntax.lbname = uu___210_1388.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___210_1388.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____1304)))
end
| uu____1391 -> begin
lbs
end))
in (

let uu____1392 = (quals_to_string' quals)
in (

let uu____1393 = (

let uu____1394 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1400 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1401 = (

let uu____1402 = (FStar_Options.print_universes ())
in (match (uu____1402) with
| true -> begin
(

let uu____1403 = (

let uu____1404 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1404 ">"))
in (Prims.strcat "<" uu____1403))
end
| uu____1405 -> begin
""
end))
in (

let uu____1406 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1407 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1400 uu____1401 uu____1406 uu____1407))))))))
in (FStar_Util.concat_l "\n and " uu____1394))
in (FStar_Util.format3 "%slet %s %s" uu____1392 (match ((FStar_Pervasives_Native.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1411 -> begin
""
end) uu____1393)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1413 = (FStar_Options.print_effect_args ())
in (match (uu____1413) with
| true -> begin
(

let uu____1414 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1414))
end
| uu____1415 -> begin
(

let uu____1416 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1417 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1416 uu____1417)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___204_1419 -> (match (uu___204_1419) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1421 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____1425 = (

let uu____1426 = (FStar_Options.ugly ())
in (not (uu____1426)))
in (match (uu____1425) with
| true -> begin
(

let uu____1427 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1427) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1431 -> begin
(

let uu____1432 = b
in (match (uu____1432) with
| (a, imp) -> begin
(

let uu____1435 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1435) with
| true -> begin
(

let uu____1436 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1436))
end
| uu____1437 -> begin
(

let uu____1438 = ((not (is_arrow)) && (

let uu____1439 = (FStar_Options.print_bound_var_types ())
in (not (uu____1439))))
in (match (uu____1438) with
| true -> begin
(

let uu____1440 = (nm_to_string a)
in (imp_to_string uu____1440 imp))
end
| uu____1441 -> begin
(

let uu____1442 = (

let uu____1443 = (nm_to_string a)
in (

let uu____1444 = (

let uu____1445 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1445))
in (Prims.strcat uu____1443 uu____1444)))
in (imp_to_string uu____1442 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____1451 = (FStar_Options.print_implicits ())
in (match (uu____1451) with
| true -> begin
bs
end
| uu____1452 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(

let uu____1453 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____1453 (FStar_String.concat sep)))
end
| uu____1457 -> begin
(

let uu____1458 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1458 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___205_1462 -> (match (uu___205_1462) with
| (a, imp) -> begin
(

let uu____1470 = (term_to_string a)
in (imp_to_string uu____1470 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____1473 = (FStar_Options.print_implicits ())
in (match (uu____1473) with
| true -> begin
args
end
| uu____1474 -> begin
(filter_imp args)
end))
in (

let uu____1477 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1477 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____1485 = (

let uu____1486 = (FStar_Options.ugly ())
in (not (uu____1486)))
in (match (uu____1485) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1489 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1491) -> begin
(

let uu____1498 = (

let uu____1499 = (FStar_Syntax_Subst.compress t)
in uu____1499.FStar_Syntax_Syntax.n)
in (match (uu____1498) with
| FStar_Syntax_Syntax.Tm_type (uu____1502) when (

let uu____1503 = (FStar_Options.print_implicits ())
in (not (uu____1503))) -> begin
(term_to_string t)
end
| uu____1504 -> begin
(

let uu____1505 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____1505))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1507) -> begin
(

let uu____1514 = (

let uu____1515 = (FStar_Syntax_Subst.compress t)
in uu____1515.FStar_Syntax_Syntax.n)
in (match (uu____1514) with
| FStar_Syntax_Syntax.Tm_type (uu____1518) when (

let uu____1519 = (FStar_Options.print_implicits ())
in (not (uu____1519))) -> begin
(term_to_string t)
end
| uu____1520 -> begin
(

let uu____1521 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____1521))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____1524 = (FStar_Options.print_effect_args ())
in (match (uu____1524) with
| true -> begin
(

let uu____1525 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1526 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____1527 = (

let uu____1528 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1528 (FStar_String.concat ", ")))
in (

let uu____1540 = (

let uu____1541 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____1541 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1525 uu____1526 uu____1527 uu____1540)))))
end
| uu____1546 -> begin
(

let uu____1547 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___206_1549 -> (match (uu___206_1549) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1550 -> begin
false
end)))) && (

let uu____1551 = (FStar_Options.print_effect_args ())
in (not (uu____1551))))
in (match (uu____1547) with
| true -> begin
(

let uu____1552 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____1552))
end
| uu____1553 -> begin
(

let uu____1554 = (((

let uu____1555 = (FStar_Options.print_effect_args ())
in (not (uu____1555))) && (

let uu____1556 = (FStar_Options.print_implicits ())
in (not (uu____1556)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____1554) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____1557 -> begin
(

let uu____1558 = ((

let uu____1559 = (FStar_Options.print_effect_args ())
in (not (uu____1559))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___207_1561 -> (match (uu___207_1561) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1562 -> begin
false
end)))))
in (match (uu____1558) with
| true -> begin
(

let uu____1563 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____1563))
end
| uu____1564 -> begin
(

let uu____1565 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1566 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____1565 uu____1566)))
end))
end))
end))
end))
in (

let dec = (

let uu____1568 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___208_1572 -> (match (uu___208_1572) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____1577 = (

let uu____1578 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____1578))
in (uu____1577)::[])
end
| uu____1579 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1568 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____1582) -> begin
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1591 = (FStar_Options.print_universes ())
in (match (uu____1591) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1592 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____1596 = (

let uu____1597 = (FStar_Options.ugly ())
in (not (uu____1597)))
in (match (uu____1596) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1600 -> begin
(

let uu____1601 = s
in (match (uu____1601) with
| (us, t) -> begin
(

let uu____1606 = (

let uu____1607 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____1607))
in (

let uu____1608 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____1606 uu____1608)))
end))
end)))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____1623 = (

let uu____1624 = (FStar_Options.ugly ())
in (not (uu____1624)))
in (match (uu____1623) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1627 -> begin
(

let actions_to_string = (fun actions -> (

let uu____1634 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (

let uu____1639 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____1640 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____1641 = (

let uu____1642 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____1642))
in (

let uu____1643 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1644 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1639 uu____1640 uu____1641 uu____1643 uu____1644)))))))))
in (FStar_All.pipe_right uu____1634 (FStar_String.concat ",\n\t"))))
in (

let uu____1646 = (

let uu____1648 = (

let uu____1650 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1651 = (

let uu____1653 = (

let uu____1654 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____1654))
in (

let uu____1655 = (

let uu____1657 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____1658 = (

let uu____1660 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____1661 = (

let uu____1663 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1664 = (

let uu____1666 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____1667 = (

let uu____1669 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____1670 = (

let uu____1672 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____1673 = (

let uu____1675 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____1676 = (

let uu____1678 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____1679 = (

let uu____1681 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____1682 = (

let uu____1684 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____1685 = (

let uu____1687 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____1688 = (

let uu____1690 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____1691 = (

let uu____1693 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____1694 = (

let uu____1696 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____1697 = (

let uu____1699 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____1700 = (

let uu____1702 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____1702)::[])
in (uu____1699)::uu____1700))
in (uu____1696)::uu____1697))
in (uu____1693)::uu____1694))
in (uu____1690)::uu____1691))
in (uu____1687)::uu____1688))
in (uu____1684)::uu____1685))
in (uu____1681)::uu____1682))
in (uu____1678)::uu____1679))
in (uu____1675)::uu____1676))
in (uu____1672)::uu____1673))
in (uu____1669)::uu____1670))
in (uu____1666)::uu____1667))
in (uu____1663)::uu____1664))
in (uu____1660)::uu____1661))
in (uu____1657)::uu____1658))
in (uu____1653)::uu____1655))
in (uu____1650)::uu____1651))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1703 -> begin
""
end))::uu____1648)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____1646)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____1713 = (

let uu____1714 = (FStar_Options.ugly ())
in (not (uu____1714)))
in (match (uu____1713) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____1719 -> begin
""
end))
end
| uu____1721 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____1728, uu____1729) -> begin
(

let uu____1734 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1735 = (binders_to_string " " tps)
in (

let uu____1736 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____1734 lid.FStar_Ident.str uu____1735 uu____1736))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____1740, uu____1741, uu____1742) -> begin
(

let uu____1745 = (FStar_Options.print_universes ())
in (match (uu____1745) with
| true -> begin
(

let uu____1746 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1746) with
| (univs2, t1) -> begin
(

let uu____1751 = (univ_names_to_string univs2)
in (

let uu____1752 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____1751 lid.FStar_Ident.str uu____1752)))
end))
end
| uu____1753 -> begin
(

let uu____1754 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____1754))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____1758 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1758) with
| (univs2, t1) -> begin
(

let uu____1763 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1764 = (

let uu____1765 = (FStar_Options.print_universes ())
in (match (uu____1765) with
| true -> begin
(

let uu____1766 = (univ_names_to_string univs2)
in (FStar_Util.format1 "<%s>" uu____1766))
end
| uu____1767 -> begin
""
end))
in (

let uu____1768 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____1763 lid.FStar_Ident.str uu____1764 uu____1768))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f) -> begin
(

let uu____1771 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1771))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1773, uu____1774) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1780 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____1780))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1782) -> begin
(

let uu____1787 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____1787 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____1799) -> begin
lift_wp
end
| (uu____1803, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____1808 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____1808) with
| (us, t) -> begin
(

let uu____1815 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____1816 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____1817 = (univ_names_to_string us)
in (

let uu____1818 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1815 uu____1816 uu____1817 uu____1818)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____1826 = (FStar_Options.print_universes ())
in (match (uu____1826) with
| true -> begin
(

let uu____1827 = (

let uu____1830 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____1830))
in (match (uu____1827) with
| (univs2, t) -> begin
(

let uu____1841 = (

let uu____1849 = (

let uu____1850 = (FStar_Syntax_Subst.compress t)
in uu____1850.FStar_Syntax_Syntax.n)
in (match (uu____1849) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____1877 -> begin
(failwith "impossible")
end))
in (match (uu____1841) with
| (tps1, c1) -> begin
(

let uu____1897 = (sli l)
in (

let uu____1898 = (univ_names_to_string univs2)
in (

let uu____1899 = (binders_to_string " " tps1)
in (

let uu____1900 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____1897 uu____1898 uu____1899 uu____1900)))))
end))
end))
end
| uu____1901 -> begin
(

let uu____1902 = (sli l)
in (

let uu____1903 = (binders_to_string " " tps)
in (

let uu____1904 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____1902 uu____1903 uu____1904))))
end))
end)
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____1911 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____1911 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1915, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1917; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1919; FStar_Syntax_Syntax.lbdef = uu____1920})::[]), uu____1921, uu____1922) -> begin
(

let uu____1938 = (lbname_to_string lb)
in (

let uu____1939 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____1938 uu____1939)))
end
| uu____1940 -> begin
(

let uu____1941 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____1941 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____1950 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____1951 = (

let uu____1952 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1952 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____1950 uu____1951))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___209_1957 -> (match (uu___209_1957) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____1960 = (FStar_Util.string_of_int i)
in (

let uu____1961 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____1960 uu____1961)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____1964 = (bv_to_string x)
in (

let uu____1965 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____1964 uu____1965)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____1972 = (bv_to_string x)
in (

let uu____1973 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____1972 uu____1973)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____1976 = (FStar_Util.string_of_int i)
in (

let uu____1977 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____1976 uu____1977)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____1980 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1980))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____1984 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____1984 (FStar_String.concat "; "))))


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

let uu____2034 = (f x)
in (FStar_Util.string_builder_append strb uu____2034));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2038 = (f x1)
in (FStar_Util.string_builder_append strb uu____2038));
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

let uu____2067 = (f x)
in (FStar_Util.string_builder_append strb uu____2067));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2071 = (f x1)
in (FStar_Util.string_builder_append strb uu____2071));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





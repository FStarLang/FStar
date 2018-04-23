
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___68_5 -> (match (uu___68_5) with
| FStar_Syntax_Syntax.Delta_constant -> begin
"Delta_constant"
end
| FStar_Syntax_Syntax.Delta_defined_at_level (i) -> begin
(

let uu____7 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_defined_at_level " uu____7))
end
| FStar_Syntax_Syntax.Delta_equational -> begin
"Delta_equational"
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(

let uu____9 = (

let uu____10 = (delta_depth_to_string d)
in (Prims.strcat uu____10 ")"))
in (Prims.strcat "Delta_abstract (" uu____9))
end))


let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____16 = (FStar_Options.print_real_names ())
in (match (uu____16) with
| true -> begin
l.FStar_Ident.str
end
| uu____17 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____33 = (

let uu____34 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____34))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____33)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____40 = (FStar_Options.print_real_names ())
in (match (uu____40) with
| true -> begin
(bv_to_string bv)
end
| uu____41 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____47 = (

let uu____48 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____48))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____47)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____186 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____197 -> begin
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


let is_inr : 'Auu____269 'Auu____270 . ('Auu____269, 'Auu____270) FStar_Util.either  ->  Prims.bool = (fun uu___69_279 -> (match (uu___69_279) with
| FStar_Util.Inl (uu____284) -> begin
false
end
| FStar_Util.Inr (uu____285) -> begin
true
end))


let filter_imp : 'Auu____290 . ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___70_345 -> (match (uu___70_345) with
| (uu____352, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____353))) -> begin
false
end
| uu____356 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  exp Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____372 = (

let uu____373 = (FStar_Syntax_Subst.compress e)
in uu____373.FStar_Syntax_Syntax.n)
in (match (uu____372) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____430 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____430) with
| true -> begin
(

let uu____435 = (

let uu____440 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____440))
in (match (uu____435) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____450 = (

let uu____453 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____453)::xs)
in FStar_Pervasives_Native.Some (uu____450))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____460 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____463 -> begin
(

let uu____464 = (is_lex_top e)
in (match (uu____464) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____471 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____505 = (f hd1)
in (match (uu____505) with
| true -> begin
hd1
end
| uu____506 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____529 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____529)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____553 = (get_lid e)
in (find_lid uu____553 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____563 = (get_lid e)
in (find_lid uu____563 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____573 = (get_lid t)
in (find_lid uu____573 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___71_583 -> (match (uu___71_583) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____591 = (FStar_Options.hide_uvar_nums ())
in (match (uu____591) with
| true -> begin
"?"
end
| uu____592 -> begin
(

let uu____593 = (

let uu____594 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____594 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____593))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____600 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____601 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____600 uu____601))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____607 = (FStar_Options.hide_uvar_nums ())
in (match (uu____607) with
| true -> begin
"?"
end
| uu____608 -> begin
(

let uu____609 = (

let uu____610 = (

let uu____611 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____611 FStar_Util.string_of_int))
in (

let uu____612 = (

let uu____613 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____613))
in (Prims.strcat uu____610 uu____612)))
in (Prims.strcat "?" uu____609))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____634 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____634) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____644 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____652 = (

let uu____653 = (FStar_Options.ugly ())
in (not (uu____653)))
in (match (uu____652) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____656 -> begin
(

let uu____657 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____657) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____669 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____669))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____671 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____671) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____685 = (univ_to_string u2)
in (

let uu____686 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____685 uu____686)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____690 = (

let uu____691 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____691 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____690))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____705 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____705 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____715 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____715 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___72_726 -> (match (uu___72_726) with
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

let uu____728 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____728))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____731 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____731 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____742 = (

let uu____743 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____743))
in (

let uu____744 = (

let uu____745 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____745 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____742 uu____744)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____764 = (

let uu____765 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____765))
in (

let uu____766 = (

let uu____767 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____767 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____764 uu____766)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____777 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____777))
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
| uu____788 -> begin
(

let uu____791 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____791 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____809 -> begin
(

let uu____812 = (quals_to_string quals)
in (Prims.strcat uu____812 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____940 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____940))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____942 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____942))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____944 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____944))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____945) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____952) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____953) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____954, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____955}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____970, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____971}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____986) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1003) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1016) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1023) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1038) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1061) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1088) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1101) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1102, m) -> begin
(

let uu____1144 = (FStar_ST.op_Bang m)
in (match (uu____1144) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1204) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1209, m) -> begin
(

let uu____1215 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1215))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1216) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1218 = (

let uu____1219 = (FStar_Options.ugly ())
in (not (uu____1219)))
in (match (uu____1218) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1222 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1225 = (FStar_Options.print_implicits ())
in (match (uu____1225) with
| true -> begin
x1
end
| uu____1226 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1227) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1252, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1272 = (

let uu____1273 = (

let uu____1282 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1282))
in (uu____1273 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1272))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1337}) -> begin
(

let uu____1352 = (term_to_string tm)
in (FStar_Util.format1 "`(%s)" uu____1352))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1354}) -> begin
(

let uu____1369 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1369))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1387 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1417 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1435 -> (match (uu____1435) with
| (t1, uu____1441) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1417 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1387 (FStar_String.concat "\\/")))
in (

let uu____1446 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1446)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1458 = (tag_of_term t)
in (

let uu____1459 = (sli m)
in (

let uu____1460 = (term_to_string t')
in (

let uu____1461 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1458 uu____1459 uu____1460 uu____1461)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1474 = (tag_of_term t)
in (

let uu____1475 = (term_to_string t')
in (

let uu____1476 = (sli m0)
in (

let uu____1477 = (sli m1)
in (

let uu____1478 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1474 uu____1475 uu____1476 uu____1477 uu____1478))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1487 = (FStar_Range.string_of_range r)
in (

let uu____1488 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1487 uu____1488)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1495 = (lid_to_string l)
in (

let uu____1496 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1497 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1495 uu____1496 uu____1497))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1499)) -> begin
(

let uu____1504 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1504))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1506 = (db_to_string x3)
in (

let uu____1507 = (

let uu____1508 = (

let uu____1509 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1509 ")"))
in (Prims.strcat ":(" uu____1508))
in (Prims.strcat uu____1506 uu____1507)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u) -> begin
(uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1515 = (FStar_Options.print_universes ())
in (match (uu____1515) with
| true -> begin
(

let uu____1516 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1516))
end
| uu____1517 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1536 = (binders_to_string " -> " bs)
in (

let uu____1537 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1536 uu____1537)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1562 = (binders_to_string " " bs)
in (

let uu____1563 = (term_to_string t2)
in (

let uu____1564 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1567 -> begin
(

let uu____1568 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1568))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1562 uu____1563 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1564))))
end
| uu____1571 -> begin
(

let uu____1574 = (binders_to_string " " bs)
in (

let uu____1575 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1574 uu____1575)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1582 = (bv_to_string xt)
in (

let uu____1583 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1586 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1582 uu____1583 uu____1586))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1611 = (term_to_string t)
in (

let uu____1612 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1611 uu____1612)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1631 = (lbs_to_string [] lbs)
in (

let uu____1632 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1631 uu____1632)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1693 = (

let uu____1694 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1694 (FStar_Util.dflt "default")))
in (

let uu____1699 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1693 uu____1699)))
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

let uu____1715 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1715))
end)
in (

let uu____1716 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1716 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1755 = (term_to_string head1)
in (

let uu____1756 = (

let uu____1757 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1793 -> (match (uu____1793) with
| (p, wopt, e) -> begin
(

let uu____1809 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1810 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1812 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1812))
end)
in (

let uu____1813 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1809 uu____1810 uu____1813))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1757))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1755 uu____1756)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1820 = (FStar_Options.print_universes ())
in (match (uu____1820) with
| true -> begin
(

let uu____1821 = (term_to_string t)
in (

let uu____1822 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1821 uu____1822)))
end
| uu____1823 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1825 = (

let uu____1826 = (FStar_Options.ugly ())
in (not (uu____1826)))
in (match (uu____1825) with
| true -> begin
(

let e = (

let uu____1828 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____1828))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1832 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1851 = (fv_to_string l)
in (

let uu____1852 = (

let uu____1853 = (FStar_List.map (fun uu____1864 -> (match (uu____1864) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1872 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1853 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1851 uu____1852)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1876) -> begin
(

let uu____1881 = (FStar_Options.print_bound_var_types ())
in (match (uu____1881) with
| true -> begin
(

let uu____1882 = (bv_to_string x1)
in (

let uu____1883 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1882 uu____1883)))
end
| uu____1884 -> begin
(

let uu____1885 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1885))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1887 = (FStar_Options.print_bound_var_types ())
in (match (uu____1887) with
| true -> begin
(

let uu____1888 = (bv_to_string x1)
in (

let uu____1889 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1888 uu____1889)))
end
| uu____1890 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1893 = (FStar_Options.print_real_names ())
in (match (uu____1893) with
| true -> begin
(

let uu____1894 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1894))
end
| uu____1895 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____1906 = (quals_to_string' quals)
in (

let uu____1907 = (

let uu____1908 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1924 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____1925 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1926 = (

let uu____1927 = (FStar_Options.print_universes ())
in (match (uu____1927) with
| true -> begin
(

let uu____1928 = (

let uu____1929 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1929 ">"))
in (Prims.strcat "<" uu____1928))
end
| uu____1930 -> begin
""
end))
in (

let uu____1931 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1932 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1924 uu____1925 uu____1926 uu____1931 uu____1932)))))))))
in (FStar_Util.concat_l "\n and " uu____1908))
in (FStar_Util.format3 "%slet %s %s" uu____1906 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____1935 -> begin
""
end) uu____1907))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___73_1936 -> (match (uu___73_1936) with
| [] -> begin
""
end
| tms -> begin
(

let uu____1942 = (

let uu____1943 = (FStar_List.map (fun t -> (

let uu____1949 = (term_to_string t)
in (paren uu____1949))) tms)
in (FStar_All.pipe_right uu____1943 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____1942))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1953 = (FStar_Options.print_effect_args ())
in (match (uu____1953) with
| true -> begin
(

let uu____1954 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____1954))
end
| uu____1955 -> begin
(

let uu____1956 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1957 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1956 uu____1957)))
end)))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun uu___74_1958 -> (match (uu___74_1958) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
"#"
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
"#."
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
"$"
end
| uu____1959 -> begin
""
end))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun s aq -> (

let uu____1962 = (aqual_to_string aq)
in (Prims.strcat uu____1962 s)))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

let uu____1969 = (

let uu____1970 = (FStar_Options.ugly ())
in (not (uu____1970)))
in (match (uu____1969) with
| true -> begin
(

let uu____1971 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1971) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1976 -> begin
(

let uu____1977 = b
in (match (uu____1977) with
| (a, imp) -> begin
(

let uu____1984 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1984) with
| true -> begin
(

let uu____1985 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1985))
end
| uu____1986 -> begin
(

let uu____1987 = ((not (is_arrow)) && (

let uu____1989 = (FStar_Options.print_bound_var_types ())
in (not (uu____1989))))
in (match (uu____1987) with
| true -> begin
(

let uu____1990 = (nm_to_string a)
in (imp_to_string uu____1990 imp))
end
| uu____1991 -> begin
(

let uu____1992 = (

let uu____1993 = (nm_to_string a)
in (

let uu____1994 = (

let uu____1995 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1995))
in (Prims.strcat uu____1993 uu____1994)))
in (imp_to_string uu____1992 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2007 = (FStar_Options.print_implicits ())
in (match (uu____2007) with
| true -> begin
bs
end
| uu____2010 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2011 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2011 (FStar_String.concat sep)))
end
| uu____2028 -> begin
(

let uu____2029 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2029 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun uu___75_2038 -> (match (uu___75_2038) with
| (a, imp) -> begin
(

let uu____2045 = (term_to_string a)
in (imp_to_string uu____2045 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2054 = (FStar_Options.print_implicits ())
in (match (uu____2054) with
| true -> begin
args
end
| uu____2061 -> begin
(filter_imp args)
end))
in (

let uu____2064 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2064 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2083 = (FStar_Options.ugly ())
in (match (uu____2083) with
| true -> begin
(comp_to_string c)
end
| uu____2084 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2088 = (

let uu____2089 = (FStar_Options.ugly ())
in (not (uu____2089)))
in (match (uu____2088) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2092 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2103 = (

let uu____2104 = (FStar_Syntax_Subst.compress t)
in uu____2104.FStar_Syntax_Syntax.n)
in (match (uu____2103) with
| FStar_Syntax_Syntax.Tm_type (uu____2107) when (

let uu____2108 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2108))) -> begin
(term_to_string t)
end
| uu____2109 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2111 = (univ_to_string u)
in (

let uu____2112 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2111 uu____2112)))
end
| uu____2113 -> begin
(

let uu____2116 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2116))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2127 = (

let uu____2128 = (FStar_Syntax_Subst.compress t)
in uu____2128.FStar_Syntax_Syntax.n)
in (match (uu____2127) with
| FStar_Syntax_Syntax.Tm_type (uu____2131) when (

let uu____2132 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2132))) -> begin
(term_to_string t)
end
| uu____2133 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2135 = (univ_to_string u)
in (

let uu____2136 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2135 uu____2136)))
end
| uu____2137 -> begin
(

let uu____2140 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2140))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2143 = (FStar_Options.print_effect_args ())
in (match (uu____2143) with
| true -> begin
(

let uu____2144 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2145 = (

let uu____2146 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2146 (FStar_String.concat ", ")))
in (

let uu____2153 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2154 = (

let uu____2155 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2155 (FStar_String.concat ", ")))
in (

let uu____2174 = (

let uu____2175 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2175 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2144 uu____2145 uu____2153 uu____2154 uu____2174))))))
end
| uu____2184 -> begin
(

let uu____2185 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___76_2189 -> (match (uu___76_2189) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2190 -> begin
false
end)))) && (

let uu____2192 = (FStar_Options.print_effect_args ())
in (not (uu____2192))))
in (match (uu____2185) with
| true -> begin
(

let uu____2193 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2193))
end
| uu____2194 -> begin
(

let uu____2195 = (((

let uu____2198 = (FStar_Options.print_effect_args ())
in (not (uu____2198))) && (

let uu____2200 = (FStar_Options.print_implicits ())
in (not (uu____2200)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2195) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2201 -> begin
(

let uu____2202 = ((

let uu____2205 = (FStar_Options.print_effect_args ())
in (not (uu____2205))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___77_2209 -> (match (uu___77_2209) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2210 -> begin
false
end)))))
in (match (uu____2202) with
| true -> begin
(

let uu____2211 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2211))
end
| uu____2212 -> begin
(

let uu____2213 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2214 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2213 uu____2214)))
end))
end))
end))
end))
in (

let dec = (

let uu____2216 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___78_2226 -> (match (uu___78_2226) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2232 = (

let uu____2233 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2233))
in (uu____2232)::[])
end
| uu____2234 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2216 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2238) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___79_2244 -> (match (uu___79_2244) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2257 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2287 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2305 -> (match (uu____2305) with
| (t, uu____2311) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2287 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2257 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2317 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2317))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2320) -> begin
(

let uu____2321 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2321))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2329 = (sli m)
in (

let uu____2330 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2329 uu____2330)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2338 = (sli m)
in (

let uu____2339 = (sli m')
in (

let uu____2340 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2338 uu____2339 uu____2340))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2351 = (FStar_Options.ugly ())
in (match (uu____2351) with
| true -> begin
(term_to_string x)
end
| uu____2352 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2365 = b
in (match (uu____2365) with
| (a, imp) -> begin
(

let n1 = (

let uu____2369 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2369) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2370 -> begin
(

let uu____2371 = (

let uu____2372 = (nm_to_string a)
in (imp_to_string uu____2372 imp))
in FStar_Util.JsonStr (uu____2371))
end))
in (

let t = (

let uu____2374 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2374))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2397 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2397)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2409 = (FStar_Options.print_universes ())
in (match (uu____2409) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2410 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2416 = (

let uu____2417 = (FStar_Options.ugly ())
in (not (uu____2417)))
in (match (uu____2416) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2420 -> begin
(

let uu____2421 = s
in (match (uu____2421) with
| (us, t) -> begin
(

let uu____2432 = (

let uu____2433 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2433))
in (

let uu____2434 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2432 uu____2434)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2440 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2441 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2442 = (

let uu____2443 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2443))
in (

let uu____2444 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2445 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2440 uu____2441 uu____2442 uu____2444 uu____2445)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2470 = (

let uu____2471 = (FStar_Options.ugly ())
in (not (uu____2471)))
in (match (uu____2470) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2474 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2485 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2485 (FStar_String.concat ",\n\t"))))
in (

let uu____2494 = (

let uu____2497 = (

let uu____2500 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2501 = (

let uu____2504 = (

let uu____2505 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2505))
in (

let uu____2506 = (

let uu____2509 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2510 = (

let uu____2513 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2514 = (

let uu____2517 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2518 = (

let uu____2521 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2522 = (

let uu____2525 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2526 = (

let uu____2529 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2530 = (

let uu____2533 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2534 = (

let uu____2537 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2538 = (

let uu____2541 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2542 = (

let uu____2545 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2546 = (

let uu____2549 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2550 = (

let uu____2553 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2554 = (

let uu____2557 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2558 = (

let uu____2561 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2562 = (

let uu____2565 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2566 = (

let uu____2569 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2569)::[])
in (uu____2565)::uu____2566))
in (uu____2561)::uu____2562))
in (uu____2557)::uu____2558))
in (uu____2553)::uu____2554))
in (uu____2549)::uu____2550))
in (uu____2545)::uu____2546))
in (uu____2541)::uu____2542))
in (uu____2537)::uu____2538))
in (uu____2533)::uu____2534))
in (uu____2529)::uu____2530))
in (uu____2525)::uu____2526))
in (uu____2521)::uu____2522))
in (uu____2517)::uu____2518))
in (uu____2513)::uu____2514))
in (uu____2509)::uu____2510))
in (uu____2504)::uu____2506))
in (uu____2500)::uu____2501))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2570 -> begin
""
end))::uu____2497)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2494)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2586 = (

let uu____2587 = (FStar_Options.ugly ())
in (not (uu____2587)))
in (match (uu____2586) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2593 -> begin
""
end))
end
| uu____2596 -> begin
(

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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2604, uu____2605) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2617 = (FStar_Options.print_universes ())
in (match (uu____2617) with
| true -> begin
(

let uu____2618 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2618 binders_str term_str))
end
| uu____2619 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2623, uu____2624, uu____2625) -> begin
(

let uu____2630 = (FStar_Options.print_universes ())
in (match (uu____2630) with
| true -> begin
(

let uu____2631 = (univ_names_to_string univs1)
in (

let uu____2632 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2631 lid.FStar_Ident.str uu____2632)))
end
| uu____2633 -> begin
(

let uu____2634 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2634))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2638 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2639 = (

let uu____2640 = (FStar_Options.print_universes ())
in (match (uu____2640) with
| true -> begin
(

let uu____2641 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2641))
end
| uu____2642 -> begin
""
end))
in (

let uu____2643 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2638 lid.FStar_Ident.str uu____2639 uu____2643))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2645, f) -> begin
(

let uu____2647 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2647))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2649) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2655 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2655))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2657) -> begin
(

let uu____2666 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2666 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2684) -> begin
lift_wp
end
| (uu____2691, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2699 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2699) with
| (us, t) -> begin
(

let uu____2710 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2711 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2712 = (univ_names_to_string us)
in (

let uu____2713 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2710 uu____2711 uu____2712 uu____2713)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____2723 = (FStar_Options.print_universes ())
in (match (uu____2723) with
| true -> begin
(

let uu____2724 = (

let uu____2729 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2729))
in (match (uu____2724) with
| (univs2, t) -> begin
(

let uu____2740 = (

let uu____2753 = (

let uu____2754 = (FStar_Syntax_Subst.compress t)
in uu____2754.FStar_Syntax_Syntax.n)
in (match (uu____2753) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2795 -> begin
(failwith "impossible")
end))
in (match (uu____2740) with
| (tps1, c1) -> begin
(

let uu____2826 = (sli l)
in (

let uu____2827 = (univ_names_to_string univs2)
in (

let uu____2828 = (binders_to_string " " tps1)
in (

let uu____2829 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2826 uu____2827 uu____2828 uu____2829)))))
end))
end))
end
| uu____2830 -> begin
(

let uu____2831 = (sli l)
in (

let uu____2832 = (binders_to_string " " tps)
in (

let uu____2833 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2831 uu____2832 uu____2833))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____2840 = (

let uu____2841 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____2841))
in (

let uu____2846 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____2840 uu____2846)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____2847 -> begin
(

let uu____2850 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____2850 (Prims.strcat "\n" basic)))
end))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2861 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2861 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2867, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2869; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2871; FStar_Syntax_Syntax.lbdef = uu____2872; FStar_Syntax_Syntax.lbattrs = uu____2873; FStar_Syntax_Syntax.lbpos = uu____2874})::[]), uu____2875) -> begin
(

let uu____2896 = (lbname_to_string lb)
in (

let uu____2897 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2896 uu____2897)))
end
| uu____2898 -> begin
(

let uu____2899 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2899 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____2915 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____2916 = (

let uu____2917 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____2917 (FStar_String.concat "\n")))
in (

let uu____2922 = (

let uu____2923 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____2923 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n" uu____2915 uu____2916 uu____2922)))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___80_2932 -> (match (uu___80_2932) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2935 = (FStar_Util.string_of_int i)
in (

let uu____2936 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2935 uu____2936)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2939 = (bv_to_string x)
in (

let uu____2940 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2939 uu____2940)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2947 = (bv_to_string x)
in (

let uu____2948 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____2947 uu____2948)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2951 = (FStar_Util.string_of_int i)
in (

let uu____2952 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2951 uu____2952)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2955 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2955))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2961 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2961 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____2999 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____2999));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3006 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3006));
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

let uu____3040 = (f x)
in (FStar_Util.string_builder_append strb uu____3040));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3047 = (f x1)
in (FStar_Util.string_builder_append strb uu____3047));
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

let uu____3085 = (f x)
in (FStar_Util.string_builder_append strb uu____3085));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3092 = (f x1)
in (FStar_Util.string_builder_append strb uu____3092));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3108 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3108)))


let ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____3118 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____3119 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____3120 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "(%s |- %s : %s)" uu____3118 uu____3119 uu____3120)))))






open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___71_5 -> (match (uu___71_5) with
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


let is_b2p : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Parser_Const.b2p_lid)::[]) t))


let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t))


let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Parser_Const.ite_lid)::[]) t))


let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Parser_Const.lexcons_lid)::[]) f))


let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Parser_Const.lextop_lid)::[]) f))


let is_inr : 'Auu____269 'Auu____270 . ('Auu____269, 'Auu____270) FStar_Util.either  ->  Prims.bool = (fun uu___72_279 -> (match (uu___72_279) with
| FStar_Util.Inl (uu____284) -> begin
false
end
| FStar_Util.Inr (uu____285) -> begin
true
end))


let filter_imp : 'Auu____290 . ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____290 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___73_345 -> (match (uu___73_345) with
| (uu____352, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____353))) -> begin
false
end
| uu____356 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____374 = (

let uu____375 = (FStar_Syntax_Subst.compress e)
in uu____375.FStar_Syntax_Syntax.n)
in (match (uu____374) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____438 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____438) with
| true -> begin
(

let uu____447 = (

let uu____454 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____454))
in (match (uu____447) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____472 = (

let uu____477 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____477)::xs)
in FStar_Pervasives_Native.Some (uu____472))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____496 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____501 -> begin
(

let uu____502 = (is_lex_top e)
in (match (uu____502) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____515 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____551 = (f hd1)
in (match (uu____551) with
| true -> begin
hd1
end
| uu____552 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____575 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____575)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____599 = (get_lid e)
in (find_lid uu____599 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____609 = (get_lid e)
in (find_lid uu____609 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____619 = (get_lid t)
in (find_lid uu____619 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___74_629 -> (match (uu___74_629) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____637 = (FStar_Options.hide_uvar_nums ())
in (match (uu____637) with
| true -> begin
"?"
end
| uu____638 -> begin
(

let uu____639 = (

let uu____640 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____640 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____639))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____646 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____647 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____646 uu____647))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____653 = (FStar_Options.hide_uvar_nums ())
in (match (uu____653) with
| true -> begin
"?"
end
| uu____654 -> begin
(

let uu____655 = (

let uu____656 = (

let uu____657 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____657 FStar_Util.string_of_int))
in (

let uu____658 = (

let uu____659 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____659))
in (Prims.strcat uu____656 uu____658)))
in (Prims.strcat "?" uu____655))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____680 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____680) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____690 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____698 = (

let uu____699 = (FStar_Options.ugly ())
in (not (uu____699)))
in (match (uu____698) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____702 -> begin
(

let uu____703 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____703) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____715 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____715))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____717 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____717) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____731 = (univ_to_string u2)
in (

let uu____732 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____731 uu____732)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____736 = (

let uu____737 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____737 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____736))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____751 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____751 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____761 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____761 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___75_772 -> (match (uu___75_772) with
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
| FStar_Syntax_Syntax.TotalEffect -> begin
"total"
end
| FStar_Syntax_Syntax.Discriminator (l) -> begin
(

let uu____774 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____774))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____777 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____777 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____788 = (

let uu____789 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____789))
in (

let uu____790 = (

let uu____791 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____791 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____788 uu____790)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____810 = (

let uu____811 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____811))
in (

let uu____812 = (

let uu____813 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____813 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____810 uu____812)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____823 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____823))
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
| uu____834 -> begin
(

let uu____837 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____837 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____855 -> begin
(

let uu____858 = (quals_to_string quals)
in (Prims.strcat uu____858 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____978 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____978))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____980 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____980))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____982 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____982))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____983) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____990) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____991) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____992, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____993}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1008, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1009}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1024) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1041) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1054) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1061) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1076) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1099) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1126) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1139) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1156, m) -> begin
(

let uu____1198 = (FStar_ST.op_Bang m)
in (match (uu____1198) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1312) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1317, m) -> begin
(

let uu____1323 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1323))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1324) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1326 = (

let uu____1327 = (FStar_Options.ugly ())
in (not (uu____1327)))
in (match (uu____1326) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1330 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1333 = (FStar_Options.print_implicits ())
in (match (uu____1333) with
| true -> begin
x1
end
| uu____1334 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1335) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1360, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1380 = (

let uu____1381 = (

let uu____1390 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1390))
in (uu____1381 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1380))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1451}) -> begin
(

let uu____1466 = (term_to_string tm)
in (FStar_Util.format1 "`(%s)" uu____1466))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1468}) -> begin
(

let uu____1483 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1483))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1501 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1531 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1549 -> (match (uu____1549) with
| (t1, uu____1555) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1531 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1501 (FStar_String.concat "\\/")))
in (

let uu____1560 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1560)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1572 = (tag_of_term t)
in (

let uu____1573 = (sli m)
in (

let uu____1574 = (term_to_string t')
in (

let uu____1575 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1572 uu____1573 uu____1574 uu____1575)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1588 = (tag_of_term t)
in (

let uu____1589 = (term_to_string t')
in (

let uu____1590 = (sli m0)
in (

let uu____1591 = (sli m1)
in (

let uu____1592 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1588 uu____1589 uu____1590 uu____1591 uu____1592))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1601 = (FStar_Range.string_of_range r)
in (

let uu____1602 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1601 uu____1602)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1609 = (lid_to_string l)
in (

let uu____1610 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1611 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1609 uu____1610 uu____1611))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1613)) -> begin
(

let uu____1618 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1618))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1620 = (db_to_string x3)
in (

let uu____1621 = (

let uu____1622 = (

let uu____1623 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1623 ")"))
in (Prims.strcat ":(" uu____1622))
in (Prims.strcat uu____1620 uu____1621)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____1627) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1654 = (FStar_Options.print_universes ())
in (match (uu____1654) with
| true -> begin
(

let uu____1655 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1655))
end
| uu____1656 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1675 = (binders_to_string " -> " bs)
in (

let uu____1676 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1675 uu____1676)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1701 = (binders_to_string " " bs)
in (

let uu____1702 = (term_to_string t2)
in (

let uu____1703 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1706 -> begin
(

let uu____1707 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1707))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1701 uu____1702 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1703))))
end
| uu____1710 -> begin
(

let uu____1713 = (binders_to_string " " bs)
in (

let uu____1714 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1713 uu____1714)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1721 = (bv_to_string xt)
in (

let uu____1722 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1725 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1721 uu____1722 uu____1725))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1750 = (term_to_string t)
in (

let uu____1751 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1750 uu____1751)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1770 = (lbs_to_string [] lbs)
in (

let uu____1771 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1770 uu____1771)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1832 = (

let uu____1833 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1833 (FStar_Util.dflt "default")))
in (

let uu____1838 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1832 uu____1838)))
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

let uu____1854 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1854))
end)
in (

let uu____1855 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1855 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1894 = (term_to_string head1)
in (

let uu____1895 = (

let uu____1896 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1932 -> (match (uu____1932) with
| (p, wopt, e) -> begin
(

let uu____1948 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1949 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1951 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1951))
end)
in (

let uu____1952 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1948 uu____1949 uu____1952))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1896))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1894 uu____1895)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1959 = (FStar_Options.print_universes ())
in (match (uu____1959) with
| true -> begin
(

let uu____1960 = (term_to_string t)
in (

let uu____1961 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1960 uu____1961)))
end
| uu____1962 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1964 = (

let uu____1965 = (FStar_Options.ugly ())
in (not (uu____1965)))
in (match (uu____1964) with
| true -> begin
(

let e = (

let uu____1967 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____1967))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1971 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1990 = (fv_to_string l)
in (

let uu____1991 = (

let uu____1992 = (FStar_List.map (fun uu____2003 -> (match (uu____2003) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____2011 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1992 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1990 uu____1991)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2015) -> begin
(

let uu____2020 = (FStar_Options.print_bound_var_types ())
in (match (uu____2020) with
| true -> begin
(

let uu____2021 = (bv_to_string x1)
in (

let uu____2022 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2021 uu____2022)))
end
| uu____2023 -> begin
(

let uu____2024 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2024))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2026 = (FStar_Options.print_bound_var_types ())
in (match (uu____2026) with
| true -> begin
(

let uu____2027 = (bv_to_string x1)
in (

let uu____2028 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2027 uu____2028)))
end
| uu____2029 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2032 = (FStar_Options.print_real_names ())
in (match (uu____2032) with
| true -> begin
(

let uu____2033 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____2033))
end
| uu____2034 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____2045 = (quals_to_string' quals)
in (

let uu____2046 = (

let uu____2047 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2063 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2064 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2065 = (

let uu____2066 = (FStar_Options.print_universes ())
in (match (uu____2066) with
| true -> begin
(

let uu____2067 = (

let uu____2068 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____2068 ">"))
in (Prims.strcat "<" uu____2067))
end
| uu____2069 -> begin
""
end))
in (

let uu____2070 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2071 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2063 uu____2064 uu____2065 uu____2070 uu____2071)))))))))
in (FStar_Util.concat_l "\n and " uu____2047))
in (FStar_Util.format3 "%slet %s %s" uu____2045 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2076 -> begin
""
end) uu____2046))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___76_2077 -> (match (uu___76_2077) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2083 = (

let uu____2084 = (FStar_List.map (fun t -> (

let uu____2090 = (term_to_string t)
in (paren uu____2090))) tms)
in (FStar_All.pipe_right uu____2084 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2083))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2094 = (FStar_Options.print_effect_args ())
in (match (uu____2094) with
| true -> begin
(

let uu____2095 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2095))
end
| uu____2096 -> begin
(

let uu____2097 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2098 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2097 uu____2098)))
end)))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun uu___77_2099 -> (match (uu___77_2099) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
"#"
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
"#."
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
"$"
end
| uu____2100 -> begin
""
end))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun s aq -> (

let uu____2103 = (aqual_to_string aq)
in (Prims.strcat uu____2103 s)))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____2106 = (

let uu____2107 = (FStar_Options.ugly ())
in (not (uu____2107)))
in (match (uu____2106) with
| true -> begin
(

let uu____2108 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2108) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2113 -> begin
(

let uu____2114 = b
in (match (uu____2114) with
| (a, imp) -> begin
(

let uu____2117 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2117) with
| true -> begin
(

let uu____2118 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____2118))
end
| uu____2119 -> begin
(

let uu____2120 = ((not (is_arrow)) && (

let uu____2122 = (FStar_Options.print_bound_var_types ())
in (not (uu____2122))))
in (match (uu____2120) with
| true -> begin
(

let uu____2123 = (nm_to_string a)
in (imp_to_string uu____2123 imp))
end
| uu____2124 -> begin
(

let uu____2125 = (

let uu____2126 = (nm_to_string a)
in (

let uu____2127 = (

let uu____2128 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2128))
in (Prims.strcat uu____2126 uu____2127)))
in (imp_to_string uu____2125 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2134 = (FStar_Options.print_implicits ())
in (match (uu____2134) with
| true -> begin
bs
end
| uu____2135 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2136 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2136 (FStar_String.concat sep)))
end
| uu____2143 -> begin
(

let uu____2144 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2144 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun uu___78_2151 -> (match (uu___78_2151) with
| (a, imp) -> begin
(

let uu____2158 = (term_to_string a)
in (imp_to_string uu____2158 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2161 = (FStar_Options.print_implicits ())
in (match (uu____2161) with
| true -> begin
args
end
| uu____2162 -> begin
(filter_imp args)
end))
in (

let uu____2165 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2165 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2178 = (FStar_Options.ugly ())
in (match (uu____2178) with
| true -> begin
(comp_to_string c)
end
| uu____2179 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2183 = (

let uu____2184 = (FStar_Options.ugly ())
in (not (uu____2184)))
in (match (uu____2183) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2187 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2198 = (

let uu____2199 = (FStar_Syntax_Subst.compress t)
in uu____2199.FStar_Syntax_Syntax.n)
in (match (uu____2198) with
| FStar_Syntax_Syntax.Tm_type (uu____2202) when (

let uu____2203 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2203))) -> begin
(term_to_string t)
end
| uu____2204 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2206 = (univ_to_string u)
in (

let uu____2207 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2206 uu____2207)))
end
| uu____2208 -> begin
(

let uu____2211 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2211))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2222 = (

let uu____2223 = (FStar_Syntax_Subst.compress t)
in uu____2223.FStar_Syntax_Syntax.n)
in (match (uu____2222) with
| FStar_Syntax_Syntax.Tm_type (uu____2226) when (

let uu____2227 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2227))) -> begin
(term_to_string t)
end
| uu____2228 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2230 = (univ_to_string u)
in (

let uu____2231 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2230 uu____2231)))
end
| uu____2232 -> begin
(

let uu____2235 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2235))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2238 = (FStar_Options.print_effect_args ())
in (match (uu____2238) with
| true -> begin
(

let uu____2239 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2240 = (

let uu____2241 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2241 (FStar_String.concat ", ")))
in (

let uu____2248 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2249 = (

let uu____2250 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2250 (FStar_String.concat ", ")))
in (

let uu____2269 = (

let uu____2270 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2270 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2239 uu____2240 uu____2248 uu____2249 uu____2269))))))
end
| uu____2279 -> begin
(

let uu____2280 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___79_2284 -> (match (uu___79_2284) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2285 -> begin
false
end)))) && (

let uu____2287 = (FStar_Options.print_effect_args ())
in (not (uu____2287))))
in (match (uu____2280) with
| true -> begin
(

let uu____2288 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2288))
end
| uu____2289 -> begin
(

let uu____2290 = (((

let uu____2293 = (FStar_Options.print_effect_args ())
in (not (uu____2293))) && (

let uu____2295 = (FStar_Options.print_implicits ())
in (not (uu____2295)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2290) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2296 -> begin
(

let uu____2297 = ((

let uu____2300 = (FStar_Options.print_effect_args ())
in (not (uu____2300))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___80_2304 -> (match (uu___80_2304) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2305 -> begin
false
end)))))
in (match (uu____2297) with
| true -> begin
(

let uu____2306 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2306))
end
| uu____2307 -> begin
(

let uu____2308 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2309 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2308 uu____2309)))
end))
end))
end))
end))
in (

let dec = (

let uu____2311 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___81_2321 -> (match (uu___81_2321) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2327 = (

let uu____2328 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2328))
in (uu____2327)::[])
end
| uu____2329 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2311 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2333) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___82_2339 -> (match (uu___82_2339) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2352 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2382 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2400 -> (match (uu____2400) with
| (t, uu____2406) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2382 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2352 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2412 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2412))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2415) -> begin
(

let uu____2416 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2416))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2424 = (sli m)
in (

let uu____2425 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2424 uu____2425)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2433 = (sli m)
in (

let uu____2434 = (sli m')
in (

let uu____2435 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2433 uu____2434 uu____2435))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2446 = (FStar_Options.ugly ())
in (match (uu____2446) with
| true -> begin
(term_to_string x)
end
| uu____2447 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2460 = b
in (match (uu____2460) with
| (a, imp) -> begin
(

let n1 = (

let uu____2464 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2464) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2465 -> begin
(

let uu____2466 = (

let uu____2467 = (nm_to_string a)
in (imp_to_string uu____2467 imp))
in FStar_Util.JsonStr (uu____2466))
end))
in (

let t = (

let uu____2469 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2469))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2492 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2492)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2500 = (FStar_Options.print_universes ())
in (match (uu____2500) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2501 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2507 = (

let uu____2508 = (FStar_Options.ugly ())
in (not (uu____2508)))
in (match (uu____2507) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2511 -> begin
(

let uu____2512 = s
in (match (uu____2512) with
| (us, t) -> begin
(

let uu____2519 = (

let uu____2520 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2520))
in (

let uu____2521 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2519 uu____2521)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2527 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2528 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2529 = (

let uu____2530 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2530))
in (

let uu____2531 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2532 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2527 uu____2528 uu____2529 uu____2531 uu____2532)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2557 = (

let uu____2558 = (FStar_Options.ugly ())
in (not (uu____2558)))
in (match (uu____2557) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2561 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2572 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2572 (FStar_String.concat ",\n\t"))))
in (

let uu____2581 = (

let uu____2584 = (

let uu____2587 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2588 = (

let uu____2591 = (

let uu____2592 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2592))
in (

let uu____2593 = (

let uu____2596 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2597 = (

let uu____2600 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2601 = (

let uu____2604 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2605 = (

let uu____2608 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2609 = (

let uu____2612 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2613 = (

let uu____2616 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2617 = (

let uu____2620 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2621 = (

let uu____2624 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2625 = (

let uu____2628 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2629 = (

let uu____2632 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2633 = (

let uu____2636 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2637 = (

let uu____2640 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2641 = (

let uu____2644 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2645 = (

let uu____2648 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2649 = (

let uu____2652 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2653 = (

let uu____2656 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2656)::[])
in (uu____2652)::uu____2653))
in (uu____2648)::uu____2649))
in (uu____2644)::uu____2645))
in (uu____2640)::uu____2641))
in (uu____2636)::uu____2637))
in (uu____2632)::uu____2633))
in (uu____2628)::uu____2629))
in (uu____2624)::uu____2625))
in (uu____2620)::uu____2621))
in (uu____2616)::uu____2617))
in (uu____2612)::uu____2613))
in (uu____2608)::uu____2609))
in (uu____2604)::uu____2605))
in (uu____2600)::uu____2601))
in (uu____2596)::uu____2597))
in (uu____2591)::uu____2593))
in (uu____2587)::uu____2588))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2657 -> begin
""
end))::uu____2584)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2581)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2673 = (

let uu____2674 = (FStar_Options.ugly ())
in (not (uu____2674)))
in (match (uu____2673) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2680 -> begin
""
end))
end
| uu____2683 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2691, uu____2692) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2704 = (FStar_Options.print_universes ())
in (match (uu____2704) with
| true -> begin
(

let uu____2705 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2705 binders_str term_str))
end
| uu____2706 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2710, uu____2711, uu____2712) -> begin
(

let uu____2717 = (FStar_Options.print_universes ())
in (match (uu____2717) with
| true -> begin
(

let uu____2718 = (univ_names_to_string univs1)
in (

let uu____2719 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2718 lid.FStar_Ident.str uu____2719)))
end
| uu____2720 -> begin
(

let uu____2721 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2721))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2725 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2726 = (

let uu____2727 = (FStar_Options.print_universes ())
in (match (uu____2727) with
| true -> begin
(

let uu____2728 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2728))
end
| uu____2729 -> begin
""
end))
in (

let uu____2730 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2725 lid.FStar_Ident.str uu____2726 uu____2730))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2732, f) -> begin
(

let uu____2734 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2734))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2736) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2742 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2742))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2744) -> begin
(

let uu____2753 = (

let uu____2754 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2754 (FStar_String.concat "\n")))
in (Prims.strcat "(* Sig_bundle *)" uu____2753))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2772) -> begin
lift_wp
end
| (uu____2779, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2787 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2787) with
| (us, t) -> begin
(

let uu____2798 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2799 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2800 = (univ_names_to_string us)
in (

let uu____2801 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2798 uu____2799 uu____2800 uu____2801)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____2811 = (FStar_Options.print_universes ())
in (match (uu____2811) with
| true -> begin
(

let uu____2812 = (

let uu____2817 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2817))
in (match (uu____2812) with
| (univs2, t) -> begin
(

let uu____2820 = (

let uu____2833 = (

let uu____2834 = (FStar_Syntax_Subst.compress t)
in uu____2834.FStar_Syntax_Syntax.n)
in (match (uu____2833) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2875 -> begin
(failwith "impossible")
end))
in (match (uu____2820) with
| (tps1, c1) -> begin
(

let uu____2906 = (sli l)
in (

let uu____2907 = (univ_names_to_string univs2)
in (

let uu____2908 = (binders_to_string " " tps1)
in (

let uu____2909 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2906 uu____2907 uu____2908 uu____2909)))))
end))
end))
end
| uu____2910 -> begin
(

let uu____2911 = (sli l)
in (

let uu____2912 = (binders_to_string " " tps)
in (

let uu____2913 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2911 uu____2912 uu____2913))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____2920 = (

let uu____2921 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____2921))
in (

let uu____2926 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____2920 uu____2926)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____2927 -> begin
(

let uu____2930 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____2930 (Prims.strcat "\n" basic)))
end))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2941 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2941 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2947, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2949; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2951; FStar_Syntax_Syntax.lbdef = uu____2952; FStar_Syntax_Syntax.lbattrs = uu____2953; FStar_Syntax_Syntax.lbpos = uu____2954})::[]), uu____2955) -> begin
(

let uu____2982 = (lbname_to_string lb)
in (

let uu____2983 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2982 uu____2983)))
end
| uu____2984 -> begin
(

let uu____2985 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2985 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____3001 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____3002 = (

let uu____3003 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3003 (FStar_String.concat "\n")))
in (

let uu____3008 = (

let uu____3009 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____3009 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n" uu____3001 uu____3002 uu____3008)))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___83_3018 -> (match (uu___83_3018) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____3021 = (FStar_Util.string_of_int i)
in (

let uu____3022 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____3021 uu____3022)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____3025 = (bv_to_string x)
in (

let uu____3026 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____3025 uu____3026)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____3033 = (bv_to_string x)
in (

let uu____3034 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____3033 uu____3034)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____3037 = (FStar_Util.string_of_int i)
in (

let uu____3038 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____3037 uu____3038)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____3041 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____3041))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____3047 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____3047 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3083 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____3083));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3090 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3090));
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

let uu____3124 = (f x)
in (FStar_Util.string_builder_append strb uu____3124));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3131 = (f x1)
in (FStar_Util.string_builder_append strb uu____3131));
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

let uu____3169 = (f x)
in (FStar_Util.string_builder_append strb uu____3169));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3176 = (f x1)
in (FStar_Util.string_builder_append strb uu____3176));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3192 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3192)))





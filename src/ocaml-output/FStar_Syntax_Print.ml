
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___71_5 -> (match (uu___71_5) with
| FStar_Syntax_Syntax.Delta_constant_at_level (i) -> begin
(

let uu____7 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_constant_at_level " uu____7))
end
| FStar_Syntax_Syntax.Delta_equational_at_level (i) -> begin
(

let uu____9 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_equational_at_level " uu____9))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(

let uu____11 = (

let uu____12 = (delta_depth_to_string d)
in (Prims.strcat uu____12 ")"))
in (Prims.strcat "Delta_abstract (" uu____11))
end))


let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____18 = (FStar_Options.print_real_names ())
in (match (uu____18) with
| true -> begin
l.FStar_Ident.str
end
| uu____19 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (

let uu____30 = (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____31 = (

let uu____32 = (

let uu____33 = (delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta)
in (Prims.strcat uu____33 ")"))
in (Prims.strcat "(@@" uu____32))
in (Prims.strcat uu____30 uu____31))))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____39 = (

let uu____40 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____40))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____39)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____46 = (FStar_Options.print_real_names ())
in (match (uu____46) with
| true -> begin
(bv_to_string bv)
end
| uu____47 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____53 = (

let uu____54 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____54))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____53)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____192 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____203 -> begin
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


let is_inr : 'Auu____275 'Auu____276 . ('Auu____275, 'Auu____276) FStar_Util.either  ->  Prims.bool = (fun uu___72_285 -> (match (uu___72_285) with
| FStar_Util.Inl (uu____290) -> begin
false
end
| FStar_Util.Inr (uu____291) -> begin
true
end))


let filter_imp : 'Auu____296 . ('Auu____296 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____296 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___73_351 -> (match (uu___73_351) with
| (uu____358, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____359))) -> begin
false
end
| uu____362 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____380 = (

let uu____381 = (FStar_Syntax_Subst.compress e)
in uu____381.FStar_Syntax_Syntax.n)
in (match (uu____380) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____444 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____444) with
| true -> begin
(

let uu____453 = (

let uu____460 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____460))
in (match (uu____453) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____478 = (

let uu____483 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____483)::xs)
in FStar_Pervasives_Native.Some (uu____478))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____502 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____507 -> begin
(

let uu____508 = (is_lex_top e)
in (match (uu____508) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____521 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____557 = (f hd1)
in (match (uu____557) with
| true -> begin
hd1
end
| uu____558 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____581 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____581)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____605 = (get_lid e)
in (find_lid uu____605 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____615 = (get_lid e)
in (find_lid uu____615 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____625 = (get_lid t)
in (find_lid uu____625 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___74_635 -> (match (uu___74_635) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____643 = (FStar_Options.hide_uvar_nums ())
in (match (uu____643) with
| true -> begin
"?"
end
| uu____644 -> begin
(

let uu____645 = (

let uu____646 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____646 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____645))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____652 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____653 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____652 uu____653))))


let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar  ->  Prims.string = (fun u -> (

let uu____659 = (FStar_Options.hide_uvar_nums ())
in (match (uu____659) with
| true -> begin
"?"
end
| uu____660 -> begin
(

let uu____661 = (

let uu____662 = (

let uu____663 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____663 FStar_Util.string_of_int))
in (

let uu____664 = (

let uu____665 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____665))
in (Prims.strcat uu____662 uu____664)))
in (Prims.strcat "?" uu____661))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____686 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____686) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____696 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____704 = (

let uu____705 = (FStar_Options.ugly ())
in (not (uu____705)))
in (match (uu____704) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____708 -> begin
(

let uu____709 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____709) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____721 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____721))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____723 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____723) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____737 = (univ_to_string u2)
in (

let uu____738 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____737 uu____738)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____742 = (

let uu____743 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____743 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____742))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____757 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____757 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____767 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____767 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___75_778 -> (match (uu___75_778) with
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

let uu____780 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____780))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____783 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____783 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____794 = (

let uu____795 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____795))
in (

let uu____796 = (

let uu____797 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____797 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____794 uu____796)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____816 = (

let uu____817 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____817))
in (

let uu____818 = (

let uu____819 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____819 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____816 uu____818)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____829 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____829))
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
| uu____840 -> begin
(

let uu____843 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____843 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____861 -> begin
(

let uu____864 = (quals_to_string quals)
in (Prims.strcat uu____864 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____984 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____984))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____986 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____986))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____988 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____988))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____989) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____996) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____997) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____998, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____999}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1014, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1015}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1030) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1047) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1060) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1067) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1082) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1105) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1132) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1145) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1162, m) -> begin
(

let uu____1204 = (FStar_ST.op_Bang m)
in (match (uu____1204) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1318) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1323, m) -> begin
(

let uu____1329 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1329))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1330) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1332 = (

let uu____1333 = (FStar_Options.ugly ())
in (not (uu____1333)))
in (match (uu____1332) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1336 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1339 = (FStar_Options.print_implicits ())
in (match (uu____1339) with
| true -> begin
x1
end
| uu____1340 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1341) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1366, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1386 = (

let uu____1387 = (

let uu____1396 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1396))
in (uu____1387 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1386))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1457}) -> begin
(

let uu____1472 = (term_to_string tm)
in (FStar_Util.format1 "`(%s)" uu____1472))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1474}) -> begin
(

let uu____1489 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1489))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1507 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1537 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1555 -> (match (uu____1555) with
| (t1, uu____1561) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1537 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1507 (FStar_String.concat "\\/")))
in (

let uu____1566 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1566)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1578 = (tag_of_term t)
in (

let uu____1579 = (sli m)
in (

let uu____1580 = (term_to_string t')
in (

let uu____1581 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1578 uu____1579 uu____1580 uu____1581)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1594 = (tag_of_term t)
in (

let uu____1595 = (term_to_string t')
in (

let uu____1596 = (sli m0)
in (

let uu____1597 = (sli m1)
in (

let uu____1598 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1594 uu____1595 uu____1596 uu____1597 uu____1598))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1607 = (FStar_Range.string_of_range r)
in (

let uu____1608 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1607 uu____1608)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1615 = (lid_to_string l)
in (

let uu____1616 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1617 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1615 uu____1616 uu____1617))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1619)) -> begin
(

let uu____1624 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1624))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1626 = (db_to_string x3)
in (

let uu____1627 = (

let uu____1628 = (

let uu____1629 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1629 ")"))
in (Prims.strcat ":(" uu____1628))
in (Prims.strcat uu____1626 uu____1627)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____1633) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1660 = (FStar_Options.print_universes ())
in (match (uu____1660) with
| true -> begin
(

let uu____1661 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1661))
end
| uu____1662 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1681 = (binders_to_string " -> " bs)
in (

let uu____1682 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1681 uu____1682)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1707 = (binders_to_string " " bs)
in (

let uu____1708 = (term_to_string t2)
in (

let uu____1709 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1712 -> begin
(

let uu____1713 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1713))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1707 uu____1708 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1709))))
end
| uu____1716 -> begin
(

let uu____1719 = (binders_to_string " " bs)
in (

let uu____1720 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1719 uu____1720)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1727 = (bv_to_string xt)
in (

let uu____1728 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1731 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1727 uu____1728 uu____1731))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1756 = (term_to_string t)
in (

let uu____1757 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1756 uu____1757)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1776 = (lbs_to_string [] lbs)
in (

let uu____1777 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1776 uu____1777)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1838 = (

let uu____1839 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1839 (FStar_Util.dflt "default")))
in (

let uu____1844 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1838 uu____1844)))
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

let uu____1860 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1860))
end)
in (

let uu____1861 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1861 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1900 = (term_to_string head1)
in (

let uu____1901 = (

let uu____1902 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1938 -> (match (uu____1938) with
| (p, wopt, e) -> begin
(

let uu____1954 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1955 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1957 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1957))
end)
in (

let uu____1958 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1954 uu____1955 uu____1958))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1902))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1900 uu____1901)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1965 = (FStar_Options.print_universes ())
in (match (uu____1965) with
| true -> begin
(

let uu____1966 = (term_to_string t)
in (

let uu____1967 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1966 uu____1967)))
end
| uu____1968 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1970 = (

let uu____1971 = (FStar_Options.ugly ())
in (not (uu____1971)))
in (match (uu____1970) with
| true -> begin
(

let e = (

let uu____1973 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____1973))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1977 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1996 = (fv_to_string l)
in (

let uu____1997 = (

let uu____1998 = (FStar_List.map (fun uu____2009 -> (match (uu____2009) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____2017 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1998 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1996 uu____1997)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2021) -> begin
(

let uu____2026 = (FStar_Options.print_bound_var_types ())
in (match (uu____2026) with
| true -> begin
(

let uu____2027 = (bv_to_string x1)
in (

let uu____2028 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2027 uu____2028)))
end
| uu____2029 -> begin
(

let uu____2030 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2030))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2032 = (FStar_Options.print_bound_var_types ())
in (match (uu____2032) with
| true -> begin
(

let uu____2033 = (bv_to_string x1)
in (

let uu____2034 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2033 uu____2034)))
end
| uu____2035 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2038 = (FStar_Options.print_real_names ())
in (match (uu____2038) with
| true -> begin
(

let uu____2039 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____2039))
end
| uu____2040 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____2051 = (quals_to_string' quals)
in (

let uu____2052 = (

let uu____2053 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2069 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2070 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2071 = (

let uu____2072 = (FStar_Options.print_universes ())
in (match (uu____2072) with
| true -> begin
(

let uu____2073 = (

let uu____2074 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____2074 ">"))
in (Prims.strcat "<" uu____2073))
end
| uu____2075 -> begin
""
end))
in (

let uu____2076 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2077 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2069 uu____2070 uu____2071 uu____2076 uu____2077)))))))))
in (FStar_Util.concat_l "\n and " uu____2053))
in (FStar_Util.format3 "%slet %s %s" uu____2051 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2082 -> begin
""
end) uu____2052))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___76_2083 -> (match (uu___76_2083) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2089 = (

let uu____2090 = (FStar_List.map (fun t -> (

let uu____2096 = (term_to_string t)
in (paren uu____2096))) tms)
in (FStar_All.pipe_right uu____2090 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2089))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2100 = (FStar_Options.print_effect_args ())
in (match (uu____2100) with
| true -> begin
(

let uu____2101 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2101))
end
| uu____2102 -> begin
(

let uu____2103 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2104 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2103 uu____2104)))
end)))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun uu___77_2105 -> (match (uu___77_2105) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
"#"
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
"#."
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
"$"
end
| uu____2106 -> begin
""
end))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun s aq -> (

let uu____2109 = (aqual_to_string aq)
in (Prims.strcat uu____2109 s)))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____2112 = (

let uu____2113 = (FStar_Options.ugly ())
in (not (uu____2113)))
in (match (uu____2112) with
| true -> begin
(

let uu____2114 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2114) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2119 -> begin
(

let uu____2120 = b
in (match (uu____2120) with
| (a, imp) -> begin
(

let uu____2123 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2123) with
| true -> begin
(

let uu____2124 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____2124))
end
| uu____2125 -> begin
(

let uu____2126 = ((not (is_arrow)) && (

let uu____2128 = (FStar_Options.print_bound_var_types ())
in (not (uu____2128))))
in (match (uu____2126) with
| true -> begin
(

let uu____2129 = (nm_to_string a)
in (imp_to_string uu____2129 imp))
end
| uu____2130 -> begin
(

let uu____2131 = (

let uu____2132 = (nm_to_string a)
in (

let uu____2133 = (

let uu____2134 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2134))
in (Prims.strcat uu____2132 uu____2133)))
in (imp_to_string uu____2131 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2140 = (FStar_Options.print_implicits ())
in (match (uu____2140) with
| true -> begin
bs
end
| uu____2141 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2142 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2142 (FStar_String.concat sep)))
end
| uu____2149 -> begin
(

let uu____2150 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2150 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun uu___78_2157 -> (match (uu___78_2157) with
| (a, imp) -> begin
(

let uu____2164 = (term_to_string a)
in (imp_to_string uu____2164 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2167 = (FStar_Options.print_implicits ())
in (match (uu____2167) with
| true -> begin
args
end
| uu____2168 -> begin
(filter_imp args)
end))
in (

let uu____2171 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2171 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2184 = (FStar_Options.ugly ())
in (match (uu____2184) with
| true -> begin
(comp_to_string c)
end
| uu____2185 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2189 = (

let uu____2190 = (FStar_Options.ugly ())
in (not (uu____2190)))
in (match (uu____2189) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2193 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2204 = (

let uu____2205 = (FStar_Syntax_Subst.compress t)
in uu____2205.FStar_Syntax_Syntax.n)
in (match (uu____2204) with
| FStar_Syntax_Syntax.Tm_type (uu____2208) when (

let uu____2209 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2209))) -> begin
(term_to_string t)
end
| uu____2210 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2212 = (univ_to_string u)
in (

let uu____2213 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2212 uu____2213)))
end
| uu____2214 -> begin
(

let uu____2217 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2217))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2228 = (

let uu____2229 = (FStar_Syntax_Subst.compress t)
in uu____2229.FStar_Syntax_Syntax.n)
in (match (uu____2228) with
| FStar_Syntax_Syntax.Tm_type (uu____2232) when (

let uu____2233 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2233))) -> begin
(term_to_string t)
end
| uu____2234 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2236 = (univ_to_string u)
in (

let uu____2237 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2236 uu____2237)))
end
| uu____2238 -> begin
(

let uu____2241 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2241))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2244 = (FStar_Options.print_effect_args ())
in (match (uu____2244) with
| true -> begin
(

let uu____2245 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2246 = (

let uu____2247 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2247 (FStar_String.concat ", ")))
in (

let uu____2254 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2255 = (

let uu____2256 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2256 (FStar_String.concat ", ")))
in (

let uu____2275 = (

let uu____2276 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2276 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2245 uu____2246 uu____2254 uu____2255 uu____2275))))))
end
| uu____2285 -> begin
(

let uu____2286 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___79_2290 -> (match (uu___79_2290) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2291 -> begin
false
end)))) && (

let uu____2293 = (FStar_Options.print_effect_args ())
in (not (uu____2293))))
in (match (uu____2286) with
| true -> begin
(

let uu____2294 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2294))
end
| uu____2295 -> begin
(

let uu____2296 = (((

let uu____2299 = (FStar_Options.print_effect_args ())
in (not (uu____2299))) && (

let uu____2301 = (FStar_Options.print_implicits ())
in (not (uu____2301)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2296) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2302 -> begin
(

let uu____2303 = ((

let uu____2306 = (FStar_Options.print_effect_args ())
in (not (uu____2306))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___80_2310 -> (match (uu___80_2310) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2311 -> begin
false
end)))))
in (match (uu____2303) with
| true -> begin
(

let uu____2312 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2312))
end
| uu____2313 -> begin
(

let uu____2314 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2315 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2314 uu____2315)))
end))
end))
end))
end))
in (

let dec = (

let uu____2317 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___81_2327 -> (match (uu___81_2327) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2333 = (

let uu____2334 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2334))
in (uu____2333)::[])
end
| uu____2335 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2317 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2339) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___82_2345 -> (match (uu___82_2345) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2358 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2388 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2406 -> (match (uu____2406) with
| (t, uu____2412) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2388 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2358 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2418 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2418))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2421) -> begin
(

let uu____2422 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2422))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2430 = (sli m)
in (

let uu____2431 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2430 uu____2431)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2439 = (sli m)
in (

let uu____2440 = (sli m')
in (

let uu____2441 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2439 uu____2440 uu____2441))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2452 = (FStar_Options.ugly ())
in (match (uu____2452) with
| true -> begin
(term_to_string x)
end
| uu____2453 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2466 = b
in (match (uu____2466) with
| (a, imp) -> begin
(

let n1 = (

let uu____2470 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2470) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2471 -> begin
(

let uu____2472 = (

let uu____2473 = (nm_to_string a)
in (imp_to_string uu____2473 imp))
in FStar_Util.JsonStr (uu____2472))
end))
in (

let t = (

let uu____2475 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2475))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2498 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2498)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2506 = (FStar_Options.print_universes ())
in (match (uu____2506) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2507 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2513 = (

let uu____2514 = (FStar_Options.ugly ())
in (not (uu____2514)))
in (match (uu____2513) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2517 -> begin
(

let uu____2518 = s
in (match (uu____2518) with
| (us, t) -> begin
(

let uu____2525 = (

let uu____2526 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2526))
in (

let uu____2527 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2525 uu____2527)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2533 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2534 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2535 = (

let uu____2536 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2536))
in (

let uu____2537 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2538 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2533 uu____2534 uu____2535 uu____2537 uu____2538)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2563 = (

let uu____2564 = (FStar_Options.ugly ())
in (not (uu____2564)))
in (match (uu____2563) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2567 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2578 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2578 (FStar_String.concat ",\n\t"))))
in (

let uu____2587 = (

let uu____2590 = (

let uu____2593 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2594 = (

let uu____2597 = (

let uu____2598 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2598))
in (

let uu____2599 = (

let uu____2602 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2603 = (

let uu____2606 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2607 = (

let uu____2610 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2611 = (

let uu____2614 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2615 = (

let uu____2618 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2619 = (

let uu____2622 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2623 = (

let uu____2626 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2627 = (

let uu____2630 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2631 = (

let uu____2634 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2635 = (

let uu____2638 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2639 = (

let uu____2642 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2643 = (

let uu____2646 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2647 = (

let uu____2650 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2651 = (

let uu____2654 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2655 = (

let uu____2658 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2659 = (

let uu____2662 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2662)::[])
in (uu____2658)::uu____2659))
in (uu____2654)::uu____2655))
in (uu____2650)::uu____2651))
in (uu____2646)::uu____2647))
in (uu____2642)::uu____2643))
in (uu____2638)::uu____2639))
in (uu____2634)::uu____2635))
in (uu____2630)::uu____2631))
in (uu____2626)::uu____2627))
in (uu____2622)::uu____2623))
in (uu____2618)::uu____2619))
in (uu____2614)::uu____2615))
in (uu____2610)::uu____2611))
in (uu____2606)::uu____2607))
in (uu____2602)::uu____2603))
in (uu____2597)::uu____2599))
in (uu____2593)::uu____2594))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2663 -> begin
""
end))::uu____2590)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2587)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2679 = (

let uu____2680 = (FStar_Options.ugly ())
in (not (uu____2680)))
in (match (uu____2679) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2686 -> begin
""
end))
end
| uu____2689 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2697, uu____2698) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2710 = (FStar_Options.print_universes ())
in (match (uu____2710) with
| true -> begin
(

let uu____2711 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2711 binders_str term_str))
end
| uu____2712 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2716, uu____2717, uu____2718) -> begin
(

let uu____2723 = (FStar_Options.print_universes ())
in (match (uu____2723) with
| true -> begin
(

let uu____2724 = (univ_names_to_string univs1)
in (

let uu____2725 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2724 lid.FStar_Ident.str uu____2725)))
end
| uu____2726 -> begin
(

let uu____2727 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2727))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2731 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2732 = (

let uu____2733 = (FStar_Options.print_universes ())
in (match (uu____2733) with
| true -> begin
(

let uu____2734 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2734))
end
| uu____2735 -> begin
""
end))
in (

let uu____2736 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2731 lid.FStar_Ident.str uu____2732 uu____2736))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2738, f) -> begin
(

let uu____2740 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2740))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2742) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2748 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2748))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2750) -> begin
(

let uu____2759 = (

let uu____2760 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2760 (FStar_String.concat "\n")))
in (Prims.strcat "(* Sig_bundle *)" uu____2759))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2778) -> begin
lift_wp
end
| (uu____2785, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2793 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2793) with
| (us, t) -> begin
(

let uu____2804 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2805 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2806 = (univ_names_to_string us)
in (

let uu____2807 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2804 uu____2805 uu____2806 uu____2807)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____2817 = (FStar_Options.print_universes ())
in (match (uu____2817) with
| true -> begin
(

let uu____2818 = (

let uu____2823 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2823))
in (match (uu____2818) with
| (univs2, t) -> begin
(

let uu____2826 = (

let uu____2839 = (

let uu____2840 = (FStar_Syntax_Subst.compress t)
in uu____2840.FStar_Syntax_Syntax.n)
in (match (uu____2839) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2881 -> begin
(failwith "impossible")
end))
in (match (uu____2826) with
| (tps1, c1) -> begin
(

let uu____2912 = (sli l)
in (

let uu____2913 = (univ_names_to_string univs2)
in (

let uu____2914 = (binders_to_string " " tps1)
in (

let uu____2915 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2912 uu____2913 uu____2914 uu____2915)))))
end))
end))
end
| uu____2916 -> begin
(

let uu____2917 = (sli l)
in (

let uu____2918 = (binders_to_string " " tps)
in (

let uu____2919 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2917 uu____2918 uu____2919))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____2926 = (

let uu____2927 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____2927))
in (

let uu____2932 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____2926 uu____2932)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____2933 -> begin
(

let uu____2936 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____2936 (Prims.strcat "\n" basic)))
end))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2947 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2947 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2953, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2955; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2957; FStar_Syntax_Syntax.lbdef = uu____2958; FStar_Syntax_Syntax.lbattrs = uu____2959; FStar_Syntax_Syntax.lbpos = uu____2960})::[]), uu____2961) -> begin
(

let uu____2988 = (lbname_to_string lb)
in (

let uu____2989 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2988 uu____2989)))
end
| uu____2990 -> begin
(

let uu____2991 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2991 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____3007 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____3008 = (

let uu____3009 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3009 (FStar_String.concat "\n")))
in (

let uu____3014 = (

let uu____3015 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____3015 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n" uu____3007 uu____3008 uu____3014)))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___83_3024 -> (match (uu___83_3024) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____3027 = (FStar_Util.string_of_int i)
in (

let uu____3028 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____3027 uu____3028)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____3031 = (bv_to_string x)
in (

let uu____3032 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____3031 uu____3032)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____3039 = (bv_to_string x)
in (

let uu____3040 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____3039 uu____3040)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____3043 = (FStar_Util.string_of_int i)
in (

let uu____3044 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____3043 uu____3044)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____3047 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____3047))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____3053 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____3053 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3089 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____3089));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3096 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3096));
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

let uu____3130 = (f x)
in (FStar_Util.string_builder_append strb uu____3130));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3137 = (f x1)
in (FStar_Util.string_builder_append strb uu____3137));
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

let uu____3175 = (f x)
in (FStar_Util.string_builder_append strb uu____3175));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3182 = (f x1)
in (FStar_Util.string_builder_append strb uu____3182));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3198 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3198)))





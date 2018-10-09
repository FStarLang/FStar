
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___213_5 -> (match (uu___213_5) with
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


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____35 = (

let uu____36 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____36))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____35)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____42 = (FStar_Options.print_real_names ())
in (match (uu____42) with
| true -> begin
(bv_to_string bv)
end
| uu____43 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____49 = (

let uu____50 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____50))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____49)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____188 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____199 -> begin
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


let is_inr : 'Auu____271 'Auu____272 . ('Auu____271, 'Auu____272) FStar_Util.either  ->  Prims.bool = (fun uu___214_281 -> (match (uu___214_281) with
| FStar_Util.Inl (uu____286) -> begin
false
end
| FStar_Util.Inr (uu____287) -> begin
true
end))


let filter_imp : 'Auu____292 . ('Auu____292 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____292 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___215_347 -> (match (uu___215_347) with
| (uu____354, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t))) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
true
end
| (uu____360, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____361))) -> begin
false
end
| (uu____364, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____365))) -> begin
false
end
| uu____370 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  exp Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____386 = (

let uu____387 = (FStar_Syntax_Subst.compress e)
in uu____387.FStar_Syntax_Syntax.n)
in (match (uu____386) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____448 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____448) with
| true -> begin
(

let uu____453 = (

let uu____458 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____458))
in (match (uu____453) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____468 = (

let uu____471 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____471)::xs)
in FStar_Pervasives_Native.Some (uu____468))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____478 -> begin
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
| uu____489 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____523 = (f hd1)
in (match (uu____523) with
| true -> begin
hd1
end
| uu____524 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____547 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____547)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____571 = (get_lid e)
in (find_lid uu____571 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____581 = (get_lid e)
in (find_lid uu____581 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____591 = (get_lid t)
in (find_lid uu____591 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___216_601 -> (match (uu___216_601) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____609 = (FStar_Options.hide_uvar_nums ())
in (match (uu____609) with
| true -> begin
"?"
end
| uu____610 -> begin
(

let uu____611 = (

let uu____612 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____612 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____611))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____618 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____619 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____618 uu____619))))


let univ_uvar_to_string : (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version)  ->  Prims.string = (fun u -> (

let uu____641 = (FStar_Options.hide_uvar_nums ())
in (match (uu____641) with
| true -> begin
"?"
end
| uu____642 -> begin
(

let uu____643 = (

let uu____644 = (

let uu____645 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____645 FStar_Util.string_of_int))
in (

let uu____646 = (

let uu____647 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____647))
in (Prims.strcat uu____644 uu____646)))
in (Prims.strcat "?" uu____643))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____668 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____668) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____678 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____686 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____686) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(

let uu____696 = (univ_uvar_to_string u1)
in (Prims.strcat "U_unif " uu____696))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "U_name " x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____699 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____699))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____701 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____701) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____715 = (univ_to_string u2)
in (

let uu____716 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____715 uu____716)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____720 = (

let uu____721 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____721 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____720))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universes  ->  Prims.string = (fun us -> (

let uu____731 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____731 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____741 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____741 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___217_752 -> (match (uu___217_752) with
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

let uu____754 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____754))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____757 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____757 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____768 = (

let uu____769 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____769))
in (

let uu____770 = (

let uu____771 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____771 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____768 uu____770)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____790 = (

let uu____791 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____791))
in (

let uu____792 = (

let uu____793 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____793 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____790 uu____792)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____803 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____803))
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
| uu____814 -> begin
(

let uu____817 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____817 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____835 -> begin
(

let uu____838 = (quals_to_string quals)
in (Prims.strcat uu____838 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1002 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____1002))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____1004 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____1004))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____1006 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____1006))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1007) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____1014) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____1015) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1016, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1017}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1030, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1031}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1044) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1063) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1078) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1085) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1102) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1125) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1152) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1165) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1178, m) -> begin
(

let uu____1216 = (FStar_ST.op_Bang m)
in (match (uu____1216) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1272) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1277, m) -> begin
(

let uu____1283 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1283))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1284) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1286 = (

let uu____1287 = (FStar_Options.ugly ())
in (not (uu____1287)))
in (match (uu____1286) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1290 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1295 = (FStar_Options.print_implicits ())
in (match (uu____1295) with
| true -> begin
x1
end
| uu____1298 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1299) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1322, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____1346, thunk); FStar_Syntax_Syntax.ltyp = uu____1348; FStar_Syntax_Syntax.rng = uu____1349}) -> begin
(

let uu____1360 = (

let uu____1361 = (

let uu____1362 = (FStar_Common.force_thunk thunk)
in (term_to_string uu____1362))
in (Prims.strcat uu____1361 "]"))
in (Prims.strcat "[LAZYEMB:" uu____1360))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1406 = (

let uu____1407 = (

let uu____1408 = (

let uu____1409 = (

let uu____1418 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1418))
in (uu____1409 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1408))
in (Prims.strcat uu____1407 "]"))
in (Prims.strcat "[lazy:" uu____1406))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
(

let print_aq = (fun uu____1483 -> (match (uu____1483) with
| (bv, t) -> begin
(

let uu____1490 = (bv_to_string bv)
in (

let uu____1491 = (term_to_string t)
in (FStar_Util.format2 "%s -> %s" uu____1490 uu____1491)))
end))
in (

let uu____1492 = (term_to_string tm)
in (

let uu____1493 = (FStar_Common.string_of_list print_aq qi.FStar_Syntax_Syntax.antiquotes)
in (FStar_Util.format2 "`(%s)%s" uu____1492 uu____1493))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____1500 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1500))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1520 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1554 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1576 -> (match (uu____1576) with
| (t1, uu____1584) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1554 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1520 (FStar_String.concat "\\/")))
in (

let uu____1593 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1593)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1605 = (tag_of_term t)
in (

let uu____1606 = (sli m)
in (

let uu____1607 = (term_to_string t')
in (

let uu____1608 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1605 uu____1606 uu____1607 uu____1608)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1621 = (tag_of_term t)
in (

let uu____1622 = (term_to_string t')
in (

let uu____1623 = (sli m0)
in (

let uu____1624 = (sli m1)
in (

let uu____1625 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1621 uu____1622 uu____1623 uu____1624 uu____1625))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1634 = (FStar_Range.string_of_range r)
in (

let uu____1635 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1634 uu____1635)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1642 = (lid_to_string l)
in (

let uu____1643 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1644 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1642 uu____1643 uu____1644))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1646)) -> begin
(

let uu____1651 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1651))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1653 = (db_to_string x3)
in (

let uu____1654 = (

let uu____1655 = (

let uu____1656 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1656 ")"))
in (Prims.strcat ":(" uu____1655))
in (Prims.strcat uu____1653 uu____1654)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____1660)) -> begin
(

let uu____1675 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____1675) with
| true -> begin
(ctx_uvar_to_string u)
end
| uu____1676 -> begin
(

let uu____1677 = (

let uu____1678 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1678))
in (Prims.strcat "?" uu____1677))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____1697 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____1697) with
| true -> begin
(

let uu____1698 = (ctx_uvar_to_string u)
in (

let uu____1699 = (

let uu____1700 = (FStar_List.map subst_to_string (FStar_Pervasives_Native.fst s))
in (FStar_All.pipe_right uu____1700 (FStar_String.concat "; ")))
in (FStar_Util.format2 "(%s @ %s)" uu____1698 uu____1699)))
end
| uu____1711 -> begin
(

let uu____1712 = (

let uu____1713 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1713))
in (Prims.strcat "?" uu____1712))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1716 = (FStar_Options.print_universes ())
in (match (uu____1716) with
| true -> begin
(

let uu____1717 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1717))
end
| uu____1718 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1741 = (binders_to_string " -> " bs)
in (

let uu____1742 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1741 uu____1742)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1771 = (binders_to_string " " bs)
in (

let uu____1772 = (term_to_string t2)
in (

let uu____1773 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1776 -> begin
(

let uu____1777 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1777))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1771 uu____1772 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1773))))
end
| uu____1780 -> begin
(

let uu____1783 = (binders_to_string " " bs)
in (

let uu____1784 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1783 uu____1784)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1791 = (bv_to_string xt)
in (

let uu____1792 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1793 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1791 uu____1792 uu____1793))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1822 = (term_to_string t)
in (

let uu____1823 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1822 uu____1823)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1842 = (lbs_to_string [] lbs)
in (

let uu____1843 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1842 uu____1843)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1904 = (

let uu____1905 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1905 (FStar_Util.dflt "default")))
in (

let uu____1910 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1904 uu____1910)))
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

let uu____1926 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1926))
end)
in (

let uu____1927 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1927 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1966 = (term_to_string head1)
in (

let uu____1967 = (

let uu____1968 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1998 -> (match (uu____1998) with
| (p, wopt, e) -> begin
(

let uu____2014 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____2015 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2017 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____2017))
end)
in (

let uu____2018 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____2014 uu____2015 uu____2018))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1968))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1966 uu____1967)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____2025 = (FStar_Options.print_universes ())
in (match (uu____2025) with
| true -> begin
(

let uu____2026 = (term_to_string t)
in (

let uu____2027 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____2026 uu____2027)))
end
| uu____2028 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____2030 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____2031 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____2032 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)" ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2030 uu____2031 uu____2032)))))
and subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___218_2033 -> (match (uu___218_2033) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2036 = (FStar_Util.string_of_int i)
in (

let uu____2037 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2036 uu____2037)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2040 = (bv_to_string x)
in (

let uu____2041 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2040 uu____2041)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2048 = (bv_to_string x)
in (

let uu____2049 = (term_to_string t)
in (FStar_Util.format2 "NT (%s, %s)" uu____2048 uu____2049)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2052 = (FStar_Util.string_of_int i)
in (

let uu____2053 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2052 uu____2053)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2056 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2056))
end))
and subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2058 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2058 (FStar_String.concat "; "))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____2068 = (

let uu____2069 = (FStar_Options.ugly ())
in (not (uu____2069)))
in (match (uu____2068) with
| true -> begin
(

let e = (

let uu____2071 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____2071))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2075 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____2094 = (fv_to_string l)
in (

let uu____2095 = (

let uu____2096 = (FStar_List.map (fun uu____2107 -> (match (uu____2107) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____2115 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____2096 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____2094 uu____2095)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2119) -> begin
(

let uu____2124 = (FStar_Options.print_bound_var_types ())
in (match (uu____2124) with
| true -> begin
(

let uu____2125 = (bv_to_string x1)
in (

let uu____2126 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2125 uu____2126)))
end
| uu____2127 -> begin
(

let uu____2128 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2128))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2130 = (FStar_Options.print_bound_var_types ())
in (match (uu____2130) with
| true -> begin
(

let uu____2131 = (bv_to_string x1)
in (

let uu____2132 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2131 uu____2132)))
end
| uu____2133 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2136 = (FStar_Options.print_bound_var_types ())
in (match (uu____2136) with
| true -> begin
(

let uu____2137 = (bv_to_string x1)
in (

let uu____2138 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "_wild_%s:%s" uu____2137 uu____2138)))
end
| uu____2139 -> begin
(bv_to_string x1)
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____2150 = (quals_to_string' quals)
in (

let uu____2151 = (

let uu____2152 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2168 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2169 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2170 = (

let uu____2171 = (FStar_Options.print_universes ())
in (match (uu____2171) with
| true -> begin
(

let uu____2172 = (

let uu____2173 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____2173 ">"))
in (Prims.strcat "<" uu____2172))
end
| uu____2174 -> begin
""
end))
in (

let uu____2175 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2176 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2168 uu____2169 uu____2170 uu____2175 uu____2176)))))))))
in (FStar_Util.concat_l "\n and " uu____2152))
in (FStar_Util.format3 "%slet %s %s" uu____2150 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2179 -> begin
""
end) uu____2151))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___219_2180 -> (match (uu___219_2180) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2186 = (

let uu____2187 = (FStar_List.map (fun t -> (

let uu____2193 = (term_to_string t)
in (paren uu____2193))) tms)
in (FStar_All.pipe_right uu____2187 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2186))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2197 = (FStar_Options.print_effect_args ())
in (match (uu____2197) with
| true -> begin
(

let uu____2198 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2198))
end
| uu____2199 -> begin
(

let uu____2200 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2201 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2200 uu____2201)))
end)))
and aqual_to_string' : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___220_2203 -> (match (uu___220_2203) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
(Prims.strcat "[|" (Prims.strcat s "|]"))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____2212 = (

let uu____2213 = (term_to_string t)
in (Prims.strcat uu____2213 (Prims.strcat "]" s)))
in (Prims.strcat "#[" uu____2212))
end
| FStar_Pervasives_Native.None -> begin
s
end))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun aq -> (aqual_to_string' "" aq))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s aq -> (aqual_to_string' s aq))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun is_arrow b -> (

let uu____2227 = (

let uu____2228 = (FStar_Options.ugly ())
in (not (uu____2228)))
in (match (uu____2227) with
| true -> begin
(

let uu____2229 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2229) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2234 -> begin
(

let uu____2235 = b
in (match (uu____2235) with
| (a, imp) -> begin
(

let uu____2248 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2248) with
| true -> begin
(

let uu____2249 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____2249))
end
| uu____2250 -> begin
(

let uu____2251 = ((not (is_arrow)) && (

let uu____2253 = (FStar_Options.print_bound_var_types ())
in (not (uu____2253))))
in (match (uu____2251) with
| true -> begin
(

let uu____2254 = (nm_to_string a)
in (imp_to_string uu____2254 imp))
end
| uu____2255 -> begin
(

let uu____2256 = (

let uu____2257 = (nm_to_string a)
in (

let uu____2258 = (

let uu____2259 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2259))
in (Prims.strcat uu____2257 uu____2258)))
in (imp_to_string uu____2256 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2273 = (FStar_Options.print_implicits ())
in (match (uu____2273) with
| true -> begin
bs
end
| uu____2276 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2277 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2277 (FStar_String.concat sep)))
end
| uu____2298 -> begin
(

let uu____2299 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2299 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___221_2308 -> (match (uu___221_2308) with
| (a, imp) -> begin
(

let uu____2321 = (term_to_string a)
in (imp_to_string uu____2321 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2332 = (FStar_Options.print_implicits ())
in (match (uu____2332) with
| true -> begin
args
end
| uu____2341 -> begin
(filter_imp args)
end))
in (

let uu____2344 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2344 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2367 = (FStar_Options.ugly ())
in (match (uu____2367) with
| true -> begin
(comp_to_string c)
end
| uu____2368 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2372 = (

let uu____2373 = (FStar_Options.ugly ())
in (not (uu____2373)))
in (match (uu____2372) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2376 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2387 = (

let uu____2388 = (FStar_Syntax_Subst.compress t)
in uu____2388.FStar_Syntax_Syntax.n)
in (match (uu____2387) with
| FStar_Syntax_Syntax.Tm_type (uu____2391) when (

let uu____2392 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2392))) -> begin
(term_to_string t)
end
| uu____2393 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2395 = (univ_to_string u)
in (

let uu____2396 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2395 uu____2396)))
end
| uu____2397 -> begin
(

let uu____2400 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2400))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2411 = (

let uu____2412 = (FStar_Syntax_Subst.compress t)
in uu____2412.FStar_Syntax_Syntax.n)
in (match (uu____2411) with
| FStar_Syntax_Syntax.Tm_type (uu____2415) when (

let uu____2416 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2416))) -> begin
(term_to_string t)
end
| uu____2417 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2419 = (univ_to_string u)
in (

let uu____2420 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2419 uu____2420)))
end
| uu____2421 -> begin
(

let uu____2424 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2424))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2427 = (FStar_Options.print_effect_args ())
in (match (uu____2427) with
| true -> begin
(

let uu____2428 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2429 = (

let uu____2430 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2430 (FStar_String.concat ", ")))
in (

let uu____2439 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2440 = (

let uu____2441 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2441 (FStar_String.concat ", ")))
in (

let uu____2462 = (cflags_to_string c1.FStar_Syntax_Syntax.flags)
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2428 uu____2429 uu____2439 uu____2440 uu____2462))))))
end
| uu____2463 -> begin
(

let uu____2464 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___222_2468 -> (match (uu___222_2468) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2469 -> begin
false
end)))) && (

let uu____2471 = (FStar_Options.print_effect_args ())
in (not (uu____2471))))
in (match (uu____2464) with
| true -> begin
(

let uu____2472 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2472))
end
| uu____2473 -> begin
(

let uu____2474 = (((

let uu____2477 = (FStar_Options.print_effect_args ())
in (not (uu____2477))) && (

let uu____2479 = (FStar_Options.print_implicits ())
in (not (uu____2479)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2474) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2480 -> begin
(

let uu____2481 = ((

let uu____2484 = (FStar_Options.print_effect_args ())
in (not (uu____2484))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___223_2488 -> (match (uu___223_2488) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2489 -> begin
false
end)))))
in (match (uu____2481) with
| true -> begin
(

let uu____2490 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2490))
end
| uu____2491 -> begin
(

let uu____2492 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2493 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2492 uu____2493)))
end))
end))
end))
end))
in (

let dec = (

let uu____2495 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___224_2505 -> (match (uu___224_2505) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2511 = (

let uu____2512 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2512))
in (uu____2511)::[])
end
| uu____2513 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2495 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2517) -> begin
""
end))
and cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list  ->  Prims.string = (fun fs -> (FStar_Common.string_of_list cflag_to_string fs))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___225_2526 -> (match (uu___225_2526) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2541 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2575 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2597 -> (match (uu____2597) with
| (t, uu____2605) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2575 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2541 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2615 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2615))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2618) -> begin
(

let uu____2619 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2619))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2627 = (sli m)
in (

let uu____2628 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2627 uu____2628)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2636 = (sli m)
in (

let uu____2637 = (sli m')
in (

let uu____2638 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2636 uu____2637 uu____2638))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2649 = (FStar_Options.ugly ())
in (match (uu____2649) with
| true -> begin
(term_to_string x)
end
| uu____2650 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2663 = b
in (match (uu____2663) with
| (a, imp) -> begin
(

let n1 = (

let uu____2671 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2671) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2672 -> begin
(

let uu____2673 = (

let uu____2674 = (nm_to_string a)
in (imp_to_string uu____2674 imp))
in FStar_Util.JsonStr (uu____2673))
end))
in (

let t = (

let uu____2676 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2676))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2699 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2699)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2713 = (FStar_Options.print_universes ())
in (match (uu____2713) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2714 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2720 = (

let uu____2721 = (FStar_Options.ugly ())
in (not (uu____2721)))
in (match (uu____2720) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2724 -> begin
(

let uu____2725 = s
in (match (uu____2725) with
| (us, t) -> begin
(

let uu____2736 = (

let uu____2737 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2737))
in (

let uu____2738 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2736 uu____2738)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2744 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2745 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2746 = (

let uu____2747 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2747))
in (

let uu____2748 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2749 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2744 uu____2745 uu____2746 uu____2748 uu____2749)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2774 = (

let uu____2775 = (FStar_Options.ugly ())
in (not (uu____2775)))
in (match (uu____2774) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2778 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2789 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2789 (FStar_String.concat ",\n\t"))))
in (

let uu____2798 = (

let uu____2801 = (

let uu____2804 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2805 = (

let uu____2808 = (

let uu____2809 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2809))
in (

let uu____2810 = (

let uu____2813 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2814 = (

let uu____2817 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2818 = (

let uu____2821 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2822 = (

let uu____2825 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2826 = (

let uu____2829 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2830 = (

let uu____2833 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2834 = (

let uu____2837 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2838 = (

let uu____2841 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2842 = (

let uu____2845 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2846 = (

let uu____2849 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2850 = (

let uu____2853 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2854 = (

let uu____2857 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2858 = (

let uu____2861 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2862 = (

let uu____2865 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2866 = (

let uu____2869 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2870 = (

let uu____2873 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2873)::[])
in (uu____2869)::uu____2870))
in (uu____2865)::uu____2866))
in (uu____2861)::uu____2862))
in (uu____2857)::uu____2858))
in (uu____2853)::uu____2854))
in (uu____2849)::uu____2850))
in (uu____2845)::uu____2846))
in (uu____2841)::uu____2842))
in (uu____2837)::uu____2838))
in (uu____2833)::uu____2834))
in (uu____2829)::uu____2830))
in (uu____2825)::uu____2826))
in (uu____2821)::uu____2822))
in (uu____2817)::uu____2818))
in (uu____2813)::uu____2814))
in (uu____2808)::uu____2810))
in (uu____2804)::uu____2805))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2874 -> begin
""
end))::uu____2801)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2798)))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2898, uu____2899) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2911 = (FStar_Options.print_universes ())
in (match (uu____2911) with
| true -> begin
(

let uu____2912 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2912 binders_str term_str))
end
| uu____2913 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2917, uu____2918, uu____2919) -> begin
(

let uu____2924 = (FStar_Options.print_universes ())
in (match (uu____2924) with
| true -> begin
(

let uu____2925 = (univ_names_to_string univs1)
in (

let uu____2926 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2925 lid.FStar_Ident.str uu____2926)))
end
| uu____2927 -> begin
(

let uu____2928 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2928))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2932 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2933 = (

let uu____2934 = (FStar_Options.print_universes ())
in (match (uu____2934) with
| true -> begin
(

let uu____2935 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2935))
end
| uu____2936 -> begin
""
end))
in (

let uu____2937 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2932 lid.FStar_Ident.str uu____2933 uu____2937))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, f) -> begin
(

let uu____2941 = (FStar_Options.print_universes ())
in (match (uu____2941) with
| true -> begin
(

let uu____2942 = (univ_names_to_string us)
in (

let uu____2943 = (term_to_string f)
in (FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str uu____2942 uu____2943)))
end
| uu____2944 -> begin
(

let uu____2945 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2945))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2947) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2953 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2953))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2955) -> begin
(

let uu____2964 = (

let uu____2965 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2965 (FStar_String.concat "\n")))
in (Prims.strcat "(* Sig_bundle *)" uu____2964))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____3001) -> begin
lift_wp
end
| (uu____3008, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____3016 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____3016) with
| (us, t) -> begin
(

let uu____3027 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____3028 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____3029 = (univ_names_to_string us)
in (

let uu____3030 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____3027 uu____3028 uu____3029 uu____3030)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____3040 = (FStar_Options.print_universes ())
in (match (uu____3040) with
| true -> begin
(

let uu____3041 = (

let uu____3046 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____3046))
in (match (uu____3041) with
| (univs2, t) -> begin
(

let uu____3059 = (

let uu____3064 = (

let uu____3065 = (FStar_Syntax_Subst.compress t)
in uu____3065.FStar_Syntax_Syntax.n)
in (match (uu____3064) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____3094 -> begin
(failwith "impossible")
end))
in (match (uu____3059) with
| (tps1, c1) -> begin
(

let uu____3101 = (sli l)
in (

let uu____3102 = (univ_names_to_string univs2)
in (

let uu____3103 = (binders_to_string " " tps1)
in (

let uu____3104 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____3101 uu____3102 uu____3103 uu____3104)))))
end))
end))
end
| uu____3105 -> begin
(

let uu____3106 = (sli l)
in (

let uu____3107 = (binders_to_string " " tps)
in (

let uu____3108 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____3106 uu____3107 uu____3108))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____3115 = (

let uu____3116 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____3116))
in (

let uu____3121 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____3115 uu____3121)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____3122 -> begin
(

let uu____3125 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____3125 (Prims.strcat "\n" basic)))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____3136 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____3136 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____3142, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____3144; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____3146; FStar_Syntax_Syntax.lbdef = uu____3147; FStar_Syntax_Syntax.lbattrs = uu____3148; FStar_Syntax_Syntax.lbpos = uu____3149})::[]), uu____3150) -> begin
(

let uu____3171 = (lbname_to_string lb)
in (

let uu____3172 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____3171 uu____3172)))
end
| uu____3173 -> begin
(

let uu____3174 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____3174 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____3190 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____3191 = (

let uu____3192 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3192 (FStar_String.concat "\n")))
in (

let uu____3197 = (

let uu____3198 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____3198 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____3190 uu____3191 uu____3197)))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3232 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____3232));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3239 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3239));
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

let uu____3273 = (f x)
in (FStar_Util.string_builder_append strb uu____3273));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3280 = (f x1)
in (FStar_Util.string_builder_append strb uu____3280));
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

let uu____3318 = (f x)
in (FStar_Util.string_builder_append strb uu____3318));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3325 = (f x1)
in (FStar_Util.string_builder_append strb uu____3325));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3341 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3341)))


let rec emb_typ_to_string : FStar_Syntax_Syntax.emb_typ  ->  Prims.string = (fun uu___226_3352 -> (match (uu___226_3352) with
| FStar_Syntax_Syntax.ET_abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.ET_app (h, []) -> begin
h
end
| FStar_Syntax_Syntax.ET_app (h, args) -> begin
(

let uu____3362 = (

let uu____3363 = (

let uu____3364 = (

let uu____3365 = (

let uu____3366 = (FStar_List.map emb_typ_to_string args)
in (FStar_All.pipe_right uu____3366 (FStar_String.concat " ")))
in (Prims.strcat uu____3365 ")"))
in (Prims.strcat " " uu____3364))
in (Prims.strcat h uu____3363))
in (Prims.strcat "(" uu____3362))
end
| FStar_Syntax_Syntax.ET_fun (a, b) -> begin
(

let uu____3373 = (

let uu____3374 = (emb_typ_to_string a)
in (

let uu____3375 = (

let uu____3376 = (emb_typ_to_string b)
in (Prims.strcat ") -> " uu____3376))
in (Prims.strcat uu____3374 uu____3375)))
in (Prims.strcat "(" uu____3373))
end))





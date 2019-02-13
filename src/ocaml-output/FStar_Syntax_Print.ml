
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___215_6 -> (match (uu___215_6) with
| FStar_Syntax_Syntax.Delta_constant_at_level (i) -> begin
(

let uu____10 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_constant_at_level " uu____10))
end
| FStar_Syntax_Syntax.Delta_equational_at_level (i) -> begin
(

let uu____15 = (FStar_Util.string_of_int i)
in (Prims.strcat "Delta_equational_at_level " uu____15))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(

let uu____19 = (

let uu____21 = (delta_depth_to_string d)
in (Prims.strcat uu____21 ")"))
in (Prims.strcat "Delta_abstract (" uu____19))
end))


let sli : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____33 = (FStar_Options.print_real_names ())
in (match (uu____33) with
| true -> begin
l.FStar_Ident.str
end
| uu____37 -> begin
l.FStar_Ident.ident.FStar_Ident.idText
end)))


let lid_to_string : FStar_Ident.lid  ->  Prims.string = (fun l -> (sli l))


let fv_to_string : FStar_Syntax_Syntax.fv  ->  Prims.string = (fun fv -> (lid_to_string fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____60 = (

let uu____62 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "#" uu____62))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____60)))


let nm_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____72 = (FStar_Options.print_real_names ())
in (match (uu____72) with
| true -> begin
(bv_to_string bv)
end
| uu____76 -> begin
bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)))


let db_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun bv -> (

let uu____85 = (

let uu____87 = (FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index)
in (Prims.strcat "@" uu____87))
in (Prims.strcat bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____85)))


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Addition_lid), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Parser_Const.op_Negation), ("not")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.not_lid), ("~")))::[]


let is_prim_op : FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.bool = (fun ps f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(FStar_All.pipe_right ps (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)))
end
| uu____309 -> begin
false
end))


let get_lid : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident = (fun f -> (match (f.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
end
| uu____322 -> begin
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


let is_inr : 'Auu____425 'Auu____426 . ('Auu____425, 'Auu____426) FStar_Util.either  ->  Prims.bool = (fun uu___216_436 -> (match (uu___216_436) with
| FStar_Util.Inl (uu____441) -> begin
false
end
| FStar_Util.Inr (uu____443) -> begin
true
end))


let filter_imp : 'Auu____450 . ('Auu____450 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____450 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___217_505 -> (match (uu___217_505) with
| (uu____513, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t))) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
true
end
| (uu____520, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____521))) -> begin
false
end
| (uu____526, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____527))) -> begin
false
end
| uu____533 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  exp Prims.list FStar_Pervasives_Native.option = (fun e -> (

let uu____551 = (

let uu____552 = (FStar_Syntax_Subst.compress e)
in uu____552.FStar_Syntax_Syntax.n)
in (match (uu____551) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map FStar_Pervasives_Native.fst args1)
in (

let uu____613 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____613) with
| true -> begin
(

let uu____622 = (

let uu____627 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____627))
in (match (uu____622) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____638 = (

let uu____641 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____641)::xs)
in FStar_Pervasives_Native.Some (uu____638))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____649 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____653 -> begin
(

let uu____654 = (is_lex_top e)
in (match (uu____654) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____663 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____702 = (f hd1)
in (match (uu____702) with
| true -> begin
hd1
end
| uu____705 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____734 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____734)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____765 = (get_lid e)
in (find_lid uu____765 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____777 = (get_lid e)
in (find_lid uu____777 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____789 = (get_lid t)
in (find_lid uu____789 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___218_803 -> (match (uu___218_803) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____814 = (FStar_Options.hide_uvar_nums ())
in (match (uu____814) with
| true -> begin
"?"
end
| uu____819 -> begin
(

let uu____821 = (

let uu____823 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____823 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____821))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____835 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____837 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____835 uu____837))))


let univ_uvar_to_string : (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version)  ->  Prims.string = (fun u -> (

let uu____863 = (FStar_Options.hide_uvar_nums ())
in (match (uu____863) with
| true -> begin
"?"
end
| uu____868 -> begin
(

let uu____870 = (

let uu____872 = (

let uu____874 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____874 FStar_Util.string_of_int))
in (

let uu____878 = (

let uu____880 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____880))
in (Prims.strcat uu____872 uu____878)))
in (Prims.strcat "?" uu____870))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____908 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____908) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____921 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____932 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____932) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(

let uu____943 = (univ_uvar_to_string u1)
in (Prims.strcat "U_unif " uu____943))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "U_name " x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____950 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____950))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____955 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____955) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____976 = (univ_to_string u2)
in (

let uu____978 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____976 uu____978)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____984 = (

let uu____986 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____986 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____984))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universes  ->  Prims.string = (fun us -> (

let uu____1005 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____1005 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____1022 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____1022 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___219_1040 -> (match (uu___219_1040) with
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

let uu____1056 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____1056))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____1061 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____1061 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____1074 = (

let uu____1076 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1076))
in (

let uu____1077 = (

let uu____1079 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1079 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____1074 uu____1077)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____1105 = (

let uu____1107 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____1107))
in (

let uu____1108 = (

let uu____1110 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____1110 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____1105 uu____1108)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____1127 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____1127))
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
| uu____1150 -> begin
(

let uu____1153 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____1153 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____1181 -> begin
(

let uu____1184 = (quals_to_string quals)
in (Prims.strcat uu____1184 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____1380 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____1380))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____1384 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____1384))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____1388 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____1388))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____1391) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____1399) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____1401) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1403, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1404}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1418, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1419}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1433) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1453) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1469) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1477) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1495) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1519) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1547) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1562) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1576, m) -> begin
(

let uu____1614 = (FStar_ST.op_Bang m)
in (match (uu____1614) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1672) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1678, m) -> begin
(

let uu____1684 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1684))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1688) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1691 = (

let uu____1693 = (FStar_Options.ugly ())
in (not (uu____1693)))
in (match (uu____1691) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1701 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1707 = (FStar_Options.print_implicits ())
in (match (uu____1707) with
| true -> begin
x1
end
| uu____1712 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1715) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1740, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____1766, thunk1); FStar_Syntax_Syntax.ltyp = uu____1768; FStar_Syntax_Syntax.rng = uu____1769}) -> begin
(

let uu____1780 = (

let uu____1782 = (

let uu____1784 = (FStar_Common.force_thunk thunk1)
in (term_to_string uu____1784))
in (Prims.strcat uu____1782 "]"))
in (Prims.strcat "[LAZYEMB:" uu____1780))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1830 = (

let uu____1832 = (

let uu____1834 = (

let uu____1835 = (

let uu____1844 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1844))
in (uu____1835 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1834))
in (Prims.strcat uu____1832 "]"))
in (Prims.strcat "[lazy:" uu____1830))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
(

let print_aq = (fun uu____1913 -> (match (uu____1913) with
| (bv, t) -> begin
(

let uu____1921 = (bv_to_string bv)
in (

let uu____1923 = (term_to_string t)
in (FStar_Util.format2 "%s -> %s" uu____1921 uu____1923)))
end))
in (

let uu____1926 = (term_to_string tm)
in (

let uu____1928 = (FStar_Common.string_of_list print_aq qi.FStar_Syntax_Syntax.antiquotes)
in (FStar_Util.format2 "`(%s)%s" uu____1926 uu____1928))))
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
(

let uu____1937 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1937))
end)
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1960 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1997 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2022 -> (match (uu____2022) with
| (t1, uu____2031) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1997 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1960 (FStar_String.concat "\\/")))
in (

let uu____2046 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____2046)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____2060 = (tag_of_term t)
in (

let uu____2062 = (sli m)
in (

let uu____2064 = (term_to_string t')
in (

let uu____2066 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2060 uu____2062 uu____2064 uu____2066)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____2081 = (tag_of_term t)
in (

let uu____2083 = (term_to_string t')
in (

let uu____2085 = (sli m0)
in (

let uu____2087 = (sli m1)
in (

let uu____2089 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2081 uu____2083 uu____2085 uu____2087 uu____2089))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____2104 = (FStar_Range.string_of_range r)
in (

let uu____2106 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2104 uu____2106)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____2115 = (lid_to_string l)
in (

let uu____2117 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2119 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2115 uu____2117 uu____2119))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____2123)) -> begin
(

let uu____2128 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____2128))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____2132 = (db_to_string x3)
in (

let uu____2134 = (

let uu____2136 = (

let uu____2138 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____2138 ")"))
in (Prims.strcat ":(" uu____2136))
in (Prims.strcat uu____2132 uu____2134)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____2145)) -> begin
(

let uu____2160 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____2160) with
| true -> begin
(ctx_uvar_to_string u)
end
| uu____2164 -> begin
(

let uu____2166 = (

let uu____2168 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2168))
in (Prims.strcat "?" uu____2166))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____2191 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____2191) with
| true -> begin
(

let uu____2195 = (ctx_uvar_to_string u)
in (

let uu____2197 = (

let uu____2199 = (FStar_List.map subst_to_string (FStar_Pervasives_Native.fst s))
in (FStar_All.pipe_right uu____2199 (FStar_String.concat "; ")))
in (FStar_Util.format2 "(%s @ %s)" uu____2195 uu____2197)))
end
| uu____2216 -> begin
(

let uu____2218 = (

let uu____2220 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____2220))
in (Prims.strcat "?" uu____2218))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____2227 = (FStar_Options.print_universes ())
in (match (uu____2227) with
| true -> begin
(

let uu____2231 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____2231))
end
| uu____2234 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____2259 = (binders_to_string " -> " bs)
in (

let uu____2262 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____2259 uu____2262)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____2294 = (binders_to_string " " bs)
in (

let uu____2297 = (term_to_string t2)
in (

let uu____2299 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____2306 -> begin
(

let uu____2308 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____2308))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____2294 uu____2297 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____2299))))
end
| uu____2312 -> begin
(

let uu____2315 = (binders_to_string " " bs)
in (

let uu____2318 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____2315 uu____2318)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____2327 = (bv_to_string xt)
in (

let uu____2329 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____2332 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____2327 uu____2329 uu____2332))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____2364 = (term_to_string t)
in (

let uu____2366 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____2364 uu____2366)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____2389 = (lbs_to_string [] lbs)
in (

let uu____2391 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____2389 uu____2391)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____2456 = (

let uu____2458 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____2458 (FStar_Util.dflt "default")))
in (

let uu____2469 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____2456 uu____2469)))
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

let uu____2490 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____2490))
end)
in (

let uu____2493 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2493 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____2534 = (term_to_string head1)
in (

let uu____2536 = (

let uu____2538 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____2571 -> (match (uu____2571) with
| (p, wopt, e) -> begin
(

let uu____2588 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____2591 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____2596 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____2596))
end)
in (

let uu____2600 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____2588 uu____2591 uu____2600))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____2538))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____2534 uu____2536)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____2612 = (FStar_Options.print_universes ())
in (match (uu____2612) with
| true -> begin
(

let uu____2616 = (term_to_string t)
in (

let uu____2618 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____2616 uu____2618)))
end
| uu____2621 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____2625 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____2628 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____2630 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)" ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2625 uu____2628 uu____2630)))))
and subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___220_2633 -> (match (uu___220_2633) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2639 = (FStar_Util.string_of_int i)
in (

let uu____2641 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2639 uu____2641)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2648 = (bv_to_string x)
in (

let uu____2650 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2648 uu____2650)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2659 = (bv_to_string x)
in (

let uu____2661 = (term_to_string t)
in (FStar_Util.format2 "NT (%s, %s)" uu____2659 uu____2661)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2668 = (FStar_Util.string_of_int i)
in (

let uu____2670 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2668 uu____2670)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2677 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2677))
end))
and subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2681 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2681 (FStar_String.concat "; "))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____2697 = (

let uu____2699 = (FStar_Options.ugly ())
in (not (uu____2699)))
in (match (uu____2697) with
| true -> begin
(

let e = (

let uu____2704 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____2704))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2710 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____2733 = (fv_to_string l)
in (

let uu____2735 = (

let uu____2737 = (FStar_List.map (fun uu____2751 -> (match (uu____2751) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____2767 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____2737 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____2733 uu____2735)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2776) -> begin
(

let uu____2781 = (FStar_Options.print_bound_var_types ())
in (match (uu____2781) with
| true -> begin
(

let uu____2785 = (bv_to_string x1)
in (

let uu____2787 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2785 uu____2787)))
end
| uu____2790 -> begin
(

let uu____2792 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2792))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2796 = (FStar_Options.print_bound_var_types ())
in (match (uu____2796) with
| true -> begin
(

let uu____2800 = (bv_to_string x1)
in (

let uu____2802 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2800 uu____2802)))
end
| uu____2805 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2809 = (FStar_Options.print_bound_var_types ())
in (match (uu____2809) with
| true -> begin
(

let uu____2813 = (bv_to_string x1)
in (

let uu____2815 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "_wild_%s:%s" uu____2813 uu____2815)))
end
| uu____2818 -> begin
(bv_to_string x1)
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.letbindings  ->  Prims.string = (fun quals lbs -> (

let uu____2824 = (quals_to_string' quals)
in (

let uu____2826 = (

let uu____2828 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2848 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2850 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2852 = (

let uu____2854 = (FStar_Options.print_universes ())
in (match (uu____2854) with
| true -> begin
(

let uu____2858 = (

let uu____2860 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____2860 ">"))
in (Prims.strcat "<" uu____2858))
end
| uu____2864 -> begin
""
end))
in (

let uu____2867 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2869 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2848 uu____2850 uu____2852 uu____2867 uu____2869)))))))))
in (FStar_Util.concat_l "\n and " uu____2828))
in (FStar_Util.format3 "%slet %s %s" uu____2824 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2881 -> begin
""
end) uu____2826))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___221_2884 -> (match (uu___221_2884) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2892 = (

let uu____2894 = (FStar_List.map (fun t -> (

let uu____2902 = (term_to_string t)
in (paren uu____2902))) tms)
in (FStar_All.pipe_right uu____2894 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2892))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2911 = (FStar_Options.print_effect_args ())
in (match (uu____2911) with
| true -> begin
(

let uu____2915 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2915))
end
| uu____2916 -> begin
(

let uu____2918 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2920 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2918 uu____2920)))
end)))
and aqual_to_string' : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___222_2924 -> (match (uu___222_2924) with
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

let uu____2942 = (

let uu____2944 = (term_to_string t)
in (Prims.strcat uu____2944 (Prims.strcat "]" s)))
in (Prims.strcat "#[" uu____2942))
end
| FStar_Pervasives_Native.None -> begin
s
end))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun aq -> (aqual_to_string' "" aq))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s aq -> (aqual_to_string' s aq))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun is_arrow b -> (

let uu____2964 = (

let uu____2966 = (FStar_Options.ugly ())
in (not (uu____2966)))
in (match (uu____2964) with
| true -> begin
(

let uu____2970 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2970) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2979 -> begin
(

let uu____2981 = b
in (match (uu____2981) with
| (a, imp) -> begin
(

let uu____2995 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2995) with
| true -> begin
(

let uu____2999 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____2999))
end
| uu____3002 -> begin
(

let uu____3004 = ((not (is_arrow)) && (

let uu____3007 = (FStar_Options.print_bound_var_types ())
in (not (uu____3007))))
in (match (uu____3004) with
| true -> begin
(

let uu____3011 = (nm_to_string a)
in (imp_to_string uu____3011 imp))
end
| uu____3013 -> begin
(

let uu____3015 = (

let uu____3017 = (nm_to_string a)
in (

let uu____3019 = (

let uu____3021 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____3021))
in (Prims.strcat uu____3017 uu____3019)))
in (imp_to_string uu____3015 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____3040 = (FStar_Options.print_implicits ())
in (match (uu____3040) with
| true -> begin
bs
end
| uu____3045 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____3051 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____3051 (FStar_String.concat sep)))
end
| uu____3077 -> begin
(

let uu____3079 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____3079 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___223_3093 -> (match (uu___223_3093) with
| (a, imp) -> begin
(

let uu____3107 = (term_to_string a)
in (imp_to_string uu____3107 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____3119 = (FStar_Options.print_implicits ())
in (match (uu____3119) with
| true -> begin
args
end
| uu____3130 -> begin
(filter_imp args)
end))
in (

let uu____3134 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3134 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____3163 = (FStar_Options.ugly ())
in (match (uu____3163) with
| true -> begin
(comp_to_string c)
end
| uu____3167 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____3174 = (

let uu____3176 = (FStar_Options.ugly ())
in (not (uu____3176)))
in (match (uu____3174) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____3184 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____3197 = (

let uu____3198 = (FStar_Syntax_Subst.compress t)
in uu____3198.FStar_Syntax_Syntax.n)
in (match (uu____3197) with
| FStar_Syntax_Syntax.Tm_type (uu____3202) when (

let uu____3203 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____3203))) -> begin
(term_to_string t)
end
| uu____3205 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____3208 = (univ_to_string u)
in (

let uu____3210 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____3208 uu____3210)))
end
| uu____3213 -> begin
(

let uu____3216 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____3216))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____3229 = (

let uu____3230 = (FStar_Syntax_Subst.compress t)
in uu____3230.FStar_Syntax_Syntax.n)
in (match (uu____3229) with
| FStar_Syntax_Syntax.Tm_type (uu____3234) when (

let uu____3235 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____3235))) -> begin
(term_to_string t)
end
| uu____3237 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____3240 = (univ_to_string u)
in (

let uu____3242 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____3240 uu____3242)))
end
| uu____3245 -> begin
(

let uu____3248 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____3248))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____3254 = (FStar_Options.print_effect_args ())
in (match (uu____3254) with
| true -> begin
(

let uu____3258 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3260 = (

let uu____3262 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____3262 (FStar_String.concat ", ")))
in (

let uu____3277 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____3279 = (

let uu____3281 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____3281 (FStar_String.concat ", ")))
in (

let uu____3308 = (cflags_to_string c1.FStar_Syntax_Syntax.flags)
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3258 uu____3260 uu____3277 uu____3279 uu____3308))))))
end
| uu____3311 -> begin
(

let uu____3313 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___224_3319 -> (match (uu___224_3319) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3322 -> begin
false
end)))) && (

let uu____3325 = (FStar_Options.print_effect_args ())
in (not (uu____3325))))
in (match (uu____3313) with
| true -> begin
(

let uu____3329 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____3329))
end
| uu____3332 -> begin
(

let uu____3334 = (((

let uu____3338 = (FStar_Options.print_effect_args ())
in (not (uu____3338))) && (

let uu____3341 = (FStar_Options.print_implicits ())
in (not (uu____3341)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____3334) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____3345 -> begin
(

let uu____3347 = ((

let uu____3351 = (FStar_Options.print_effect_args ())
in (not (uu____3351))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___225_3357 -> (match (uu___225_3357) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____3360 -> begin
false
end)))))
in (match (uu____3347) with
| true -> begin
(

let uu____3364 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____3364))
end
| uu____3367 -> begin
(

let uu____3369 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____3371 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____3369 uu____3371)))
end))
end))
end))
end))
in (

let dec = (

let uu____3376 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___226_3389 -> (match (uu___226_3389) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____3396 = (

let uu____3398 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____3398))
in (uu____3396)::[])
end
| uu____3403 -> begin
[]
end))))
in (FStar_All.pipe_right uu____3376 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____3422) -> begin
""
end))
and cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list  ->  Prims.string = (fun fs -> (FStar_Common.string_of_list cflag_to_string fs))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___227_3432 -> (match (uu___227_3432) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____3449 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____3486 = (FStar_All.pipe_right args (FStar_List.map (fun uu____3511 -> (match (uu____3511) with
| (t, uu____3520) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____3486 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____3449 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____3537 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____3537))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____3542) -> begin
(

let uu____3547 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3547))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____3558 = (sli m)
in (

let uu____3560 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3558 uu____3560)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____3570 = (sli m)
in (

let uu____3572 = (sli m')
in (

let uu____3574 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3570 uu____3572 uu____3574))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____3589 = (FStar_Options.ugly ())
in (match (uu____3589) with
| true -> begin
(term_to_string x)
end
| uu____3593 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____3610 = b
in (match (uu____3610) with
| (a, imp) -> begin
(

let n1 = (

let uu____3618 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____3618) with
| true -> begin
FStar_Util.JsonNull
end
| uu____3621 -> begin
(

let uu____3623 = (

let uu____3625 = (nm_to_string a)
in (imp_to_string uu____3625 imp))
in FStar_Util.JsonStr (uu____3623))
end))
in (

let t = (

let uu____3628 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____3628))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____3660 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____3660)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____3678 = (FStar_Options.print_universes ())
in (match (uu____3678) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____3684 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____3694 = (

let uu____3696 = (FStar_Options.ugly ())
in (not (uu____3696)))
in (match (uu____3694) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____3704 -> begin
(

let uu____3706 = s
in (match (uu____3706) with
| (us, t) -> begin
(

let uu____3718 = (

let uu____3720 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____3720))
in (

let uu____3724 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____3718 uu____3724)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____3734 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____3736 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____3739 = (

let uu____3741 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____3741))
in (

let uu____3745 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____3747 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____3734 uu____3736 uu____3739 uu____3745 uu____3747)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____3778 = (

let uu____3780 = (FStar_Options.ugly ())
in (not (uu____3780)))
in (match (uu____3778) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____3788 -> begin
(

let actions_to_string = (fun actions -> (

let uu____3801 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____3801 (FStar_String.concat ",\n\t"))))
in (

let uu____3816 = (

let uu____3820 = (

let uu____3824 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____3826 = (

let uu____3830 = (

let uu____3832 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____3832))
in (

let uu____3836 = (

let uu____3840 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____3843 = (

let uu____3847 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____3849 = (

let uu____3853 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____3855 = (

let uu____3859 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____3861 = (

let uu____3865 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____3867 = (

let uu____3871 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____3873 = (

let uu____3877 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____3879 = (

let uu____3883 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____3885 = (

let uu____3889 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____3891 = (

let uu____3895 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____3897 = (

let uu____3901 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____3903 = (

let uu____3907 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____3909 = (

let uu____3913 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____3915 = (

let uu____3919 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____3921 = (

let uu____3925 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____3927 = (

let uu____3931 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____3931)::[])
in (uu____3925)::uu____3927))
in (uu____3919)::uu____3921))
in (uu____3913)::uu____3915))
in (uu____3907)::uu____3909))
in (uu____3901)::uu____3903))
in (uu____3895)::uu____3897))
in (uu____3889)::uu____3891))
in (uu____3883)::uu____3885))
in (uu____3877)::uu____3879))
in (uu____3871)::uu____3873))
in (uu____3865)::uu____3867))
in (uu____3859)::uu____3861))
in (uu____3853)::uu____3855))
in (uu____3847)::uu____3849))
in (uu____3840)::uu____3843))
in (uu____3830)::uu____3836))
in (uu____3824)::uu____3826))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____3956 -> begin
""
end))::uu____3820)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____3816)))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____4005, uu____4006) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____4022 = (FStar_Options.print_universes ())
in (match (uu____4022) with
| true -> begin
(

let uu____4026 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____4026 binders_str term_str))
end
| uu____4029 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____4035, uu____4036, uu____4037) -> begin
(

let uu____4044 = (FStar_Options.print_universes ())
in (match (uu____4044) with
| true -> begin
(

let uu____4048 = (univ_names_to_string univs1)
in (

let uu____4050 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____4048 lid.FStar_Ident.str uu____4050)))
end
| uu____4053 -> begin
(

let uu____4055 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____4055))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____4061 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____4063 = (

let uu____4065 = (FStar_Options.print_universes ())
in (match (uu____4065) with
| true -> begin
(

let uu____4069 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____4069))
end
| uu____4072 -> begin
""
end))
in (

let uu____4075 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____4061 lid.FStar_Ident.str uu____4063 uu____4075))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, f) -> begin
(

let uu____4081 = (FStar_Options.print_universes ())
in (match (uu____4081) with
| true -> begin
(

let uu____4085 = (univ_names_to_string us)
in (

let uu____4087 = (term_to_string f)
in (FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str uu____4085 uu____4087)))
end
| uu____4090 -> begin
(

let uu____4092 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4092))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____4096) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____4102 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____4102))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4106) -> begin
(

let uu____4115 = (

let uu____4117 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____4117 (FStar_String.concat "\n")))
in (Prims.strcat "(* Sig_bundle *)" uu____4115))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____4162) -> begin
lift_wp
end
| (uu____4169, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____4177 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____4177) with
| (us, t) -> begin
(

let uu____4189 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____4191 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____4193 = (univ_names_to_string us)
in (

let uu____4195 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4189 uu____4191 uu____4193 uu____4195)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____4207 = (FStar_Options.print_universes ())
in (match (uu____4207) with
| true -> begin
(

let uu____4211 = (

let uu____4216 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____4216))
in (match (uu____4211) with
| (univs2, t) -> begin
(

let uu____4230 = (

let uu____4235 = (

let uu____4236 = (FStar_Syntax_Subst.compress t)
in uu____4236.FStar_Syntax_Syntax.n)
in (match (uu____4235) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____4265 -> begin
(failwith "impossible")
end))
in (match (uu____4230) with
| (tps1, c1) -> begin
(

let uu____4274 = (sli l)
in (

let uu____4276 = (univ_names_to_string univs2)
in (

let uu____4278 = (binders_to_string " " tps1)
in (

let uu____4281 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____4274 uu____4276 uu____4278 uu____4281)))))
end))
end))
end
| uu____4284 -> begin
(

let uu____4286 = (sli l)
in (

let uu____4288 = (binders_to_string " " tps)
in (

let uu____4291 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____4286 uu____4288 uu____4291))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____4300 = (

let uu____4302 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____4302))
in (

let uu____4312 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____4300 uu____4312)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____4316 -> begin
(

let uu____4319 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____4319 (Prims.strcat "\n" basic)))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____4336 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____4336 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____4347, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____4349; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____4351; FStar_Syntax_Syntax.lbdef = uu____4352; FStar_Syntax_Syntax.lbattrs = uu____4353; FStar_Syntax_Syntax.lbpos = uu____4354})::[]), uu____4355) -> begin
(

let uu____4378 = (lbname_to_string lb)
in (

let uu____4380 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____4378 uu____4380)))
end
| uu____4383 -> begin
(

let uu____4384 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____4384 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____4408 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____4410 = (

let uu____4412 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____4412 (FStar_String.concat "\n")))
in (

let uu____4422 = (

let uu____4424 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____4424 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4408 uu____4410 uu____4422)))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____4468 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____4468));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____4477 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____4477));
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

let uu____4518 = (f x)
in (FStar_Util.string_builder_append strb uu____4518));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____4527 = (f x1)
in (FStar_Util.string_builder_append strb uu____4527));
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

let uu____4574 = (f x)
in (FStar_Util.string_builder_append strb uu____4574));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____4583 = (f x1)
in (FStar_Util.string_builder_append strb uu____4583));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____4605 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____4605)))


let rec emb_typ_to_string : FStar_Syntax_Syntax.emb_typ  ->  Prims.string = (fun uu___228_4618 -> (match (uu___228_4618) with
| FStar_Syntax_Syntax.ET_abstract -> begin
"abstract"
end
| FStar_Syntax_Syntax.ET_app (h, []) -> begin
h
end
| FStar_Syntax_Syntax.ET_app (h, args) -> begin
(

let uu____4634 = (

let uu____4636 = (

let uu____4638 = (

let uu____4640 = (

let uu____4642 = (FStar_List.map emb_typ_to_string args)
in (FStar_All.pipe_right uu____4642 (FStar_String.concat " ")))
in (Prims.strcat uu____4640 ")"))
in (Prims.strcat " " uu____4638))
in (Prims.strcat h uu____4636))
in (Prims.strcat "(" uu____4634))
end
| FStar_Syntax_Syntax.ET_fun (a, b) -> begin
(

let uu____4657 = (

let uu____4659 = (emb_typ_to_string a)
in (

let uu____4661 = (

let uu____4663 = (emb_typ_to_string b)
in (Prims.strcat ") -> " uu____4663))
in (Prims.strcat uu____4659 uu____4661)))
in (Prims.strcat "(" uu____4657))
end))






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

let uu____436 = (

let uu____441 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____441))
in (match (uu____436) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____451 = (

let uu____454 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____454)::xs)
in FStar_Pervasives_Native.Some (uu____451))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____461 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____464 -> begin
(

let uu____465 = (is_lex_top e)
in (match (uu____465) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____472 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____506 = (f hd1)
in (match (uu____506) with
| true -> begin
hd1
end
| uu____507 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____530 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____530)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____554 = (get_lid e)
in (find_lid uu____554 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____564 = (get_lid e)
in (find_lid uu____564 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____574 = (get_lid t)
in (find_lid uu____574 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___71_584 -> (match (uu___71_584) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____592 = (FStar_Options.hide_uvar_nums ())
in (match (uu____592) with
| true -> begin
"?"
end
| uu____593 -> begin
(

let uu____594 = (

let uu____595 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____595 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____594))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____601 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____602 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____601 uu____602))))


let univ_uvar_to_string : (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version)  ->  Prims.string = (fun u -> (

let uu____624 = (FStar_Options.hide_uvar_nums ())
in (match (uu____624) with
| true -> begin
"?"
end
| uu____625 -> begin
(

let uu____626 = (

let uu____627 = (

let uu____628 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____628 FStar_Util.string_of_int))
in (

let uu____629 = (

let uu____630 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____630))
in (Prims.strcat uu____627 uu____629)))
in (Prims.strcat "?" uu____626))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____651 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____651) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____661 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____669 = (

let uu____670 = (FStar_Options.ugly ())
in (not (uu____670)))
in (match (uu____669) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____673 -> begin
(

let uu____674 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____674) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(univ_uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____686 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____686))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____688 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____688) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____702 = (univ_to_string u2)
in (

let uu____703 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____702 uu____703)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____707 = (

let uu____708 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____708 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____707))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____722 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____722 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____732 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____732 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___72_743 -> (match (uu___72_743) with
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

let uu____745 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____745))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____748 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____748 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____759 = (

let uu____760 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____760))
in (

let uu____761 = (

let uu____762 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____762 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____759 uu____761)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____781 = (

let uu____782 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____782))
in (

let uu____783 = (

let uu____784 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____784 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____781 uu____783)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____794 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____794))
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
| uu____805 -> begin
(

let uu____808 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____808 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____826 -> begin
(

let uu____829 = (quals_to_string quals)
in (Prims.strcat uu____829 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____957 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____957))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____959 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____959))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____961 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____961))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____962) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____969) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____970) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____971, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____972}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____987, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____988}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1003) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1020) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1033) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1040) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1055) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1078) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1105) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1118) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1119, m) -> begin
(

let uu____1161 = (FStar_ST.op_Bang m)
in (match (uu____1161) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1221) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1226, m) -> begin
(

let uu____1232 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1232))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1233) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1235 = (

let uu____1236 = (FStar_Options.ugly ())
in (not (uu____1236)))
in (match (uu____1235) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1239 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1244 = (FStar_Options.print_implicits ())
in (match (uu____1244) with
| true -> begin
x1
end
| uu____1247 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1248) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1273, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1293 = (

let uu____1294 = (

let uu____1303 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1303))
in (uu____1294 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1293))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1358}) -> begin
(

let uu____1373 = (term_to_string tm)
in (FStar_Util.format1 "`(%s)" uu____1373))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1375}) -> begin
(

let uu____1390 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1390))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1408 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1436 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1454 -> (match (uu____1454) with
| (t1, uu____1460) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1436 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1408 (FStar_String.concat "\\/")))
in (

let uu____1465 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1465)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1477 = (tag_of_term t)
in (

let uu____1478 = (sli m)
in (

let uu____1479 = (term_to_string t')
in (

let uu____1480 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1477 uu____1478 uu____1479 uu____1480)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1493 = (tag_of_term t)
in (

let uu____1494 = (term_to_string t')
in (

let uu____1495 = (sli m0)
in (

let uu____1496 = (sli m1)
in (

let uu____1497 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1493 uu____1494 uu____1495 uu____1496 uu____1497))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1506 = (FStar_Range.string_of_range r)
in (

let uu____1507 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1506 uu____1507)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1514 = (lid_to_string l)
in (

let uu____1515 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1516 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1514 uu____1515 uu____1516))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1518)) -> begin
(

let uu____1523 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1523))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1525 = (db_to_string x3)
in (

let uu____1526 = (

let uu____1527 = (

let uu____1528 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1528 ")"))
in (Prims.strcat ":(" uu____1527))
in (Prims.strcat uu____1525 uu____1526)))
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

let uu____1534 = (FStar_Options.print_universes ())
in (match (uu____1534) with
| true -> begin
(

let uu____1535 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1535))
end
| uu____1536 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1555 = (binders_to_string " -> " bs)
in (

let uu____1556 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1555 uu____1556)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1581 = (binders_to_string " " bs)
in (

let uu____1582 = (term_to_string t2)
in (

let uu____1583 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1586 -> begin
(

let uu____1587 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1587))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1581 uu____1582 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1583))))
end
| uu____1590 -> begin
(

let uu____1593 = (binders_to_string " " bs)
in (

let uu____1594 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1593 uu____1594)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1601 = (bv_to_string xt)
in (

let uu____1602 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1603 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1601 uu____1602 uu____1603))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1628 = (term_to_string t)
in (

let uu____1629 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1628 uu____1629)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1648 = (lbs_to_string [] lbs)
in (

let uu____1649 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1648 uu____1649)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1710 = (

let uu____1711 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1711 (FStar_Util.dflt "default")))
in (

let uu____1716 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1710 uu____1716)))
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

let uu____1732 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1732))
end)
in (

let uu____1733 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1733 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1772 = (term_to_string head1)
in (

let uu____1773 = (

let uu____1774 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1804 -> (match (uu____1804) with
| (p, wopt, e) -> begin
(

let uu____1820 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1821 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1823 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1823))
end)
in (

let uu____1824 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1820 uu____1821 uu____1824))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1774))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1772 uu____1773)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1831 = (FStar_Options.print_universes ())
in (match (uu____1831) with
| true -> begin
(

let uu____1832 = (term_to_string t)
in (

let uu____1833 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1832 uu____1833)))
end
| uu____1834 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1836 = (

let uu____1837 = (FStar_Options.ugly ())
in (not (uu____1837)))
in (match (uu____1836) with
| true -> begin
(

let e = (

let uu____1839 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____1839))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1843 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1862 = (fv_to_string l)
in (

let uu____1863 = (

let uu____1864 = (FStar_List.map (fun uu____1875 -> (match (uu____1875) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1883 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1864 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1862 uu____1863)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1887) -> begin
(

let uu____1892 = (FStar_Options.print_bound_var_types ())
in (match (uu____1892) with
| true -> begin
(

let uu____1893 = (bv_to_string x1)
in (

let uu____1894 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1893 uu____1894)))
end
| uu____1895 -> begin
(

let uu____1896 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1896))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1898 = (FStar_Options.print_bound_var_types ())
in (match (uu____1898) with
| true -> begin
(

let uu____1899 = (bv_to_string x1)
in (

let uu____1900 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1899 uu____1900)))
end
| uu____1901 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1904 = (FStar_Options.print_real_names ())
in (match (uu____1904) with
| true -> begin
(

let uu____1905 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1905))
end
| uu____1906 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____1917 = (quals_to_string' quals)
in (

let uu____1918 = (

let uu____1919 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1935 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____1936 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1937 = (

let uu____1938 = (FStar_Options.print_universes ())
in (match (uu____1938) with
| true -> begin
(

let uu____1939 = (

let uu____1940 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1940 ">"))
in (Prims.strcat "<" uu____1939))
end
| uu____1941 -> begin
""
end))
in (

let uu____1942 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1943 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1935 uu____1936 uu____1937 uu____1942 uu____1943)))))))))
in (FStar_Util.concat_l "\n and " uu____1919))
in (FStar_Util.format3 "%slet %s %s" uu____1917 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____1946 -> begin
""
end) uu____1918))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___73_1947 -> (match (uu___73_1947) with
| [] -> begin
""
end
| tms -> begin
(

let uu____1953 = (

let uu____1954 = (FStar_List.map (fun t -> (

let uu____1960 = (term_to_string t)
in (paren uu____1960))) tms)
in (FStar_All.pipe_right uu____1954 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____1953))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1964 = (FStar_Options.print_effect_args ())
in (match (uu____1964) with
| true -> begin
(

let uu____1965 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____1965))
end
| uu____1966 -> begin
(

let uu____1967 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1968 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1967 uu____1968)))
end)))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun uu___74_1969 -> (match (uu___74_1969) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
"#"
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
"#."
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
"$"
end
| uu____1970 -> begin
""
end))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun s aq -> (

let uu____1973 = (aqual_to_string aq)
in (Prims.strcat uu____1973 s)))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

let uu____1980 = (

let uu____1981 = (FStar_Options.ugly ())
in (not (uu____1981)))
in (match (uu____1980) with
| true -> begin
(

let uu____1982 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1982) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1987 -> begin
(

let uu____1988 = b
in (match (uu____1988) with
| (a, imp) -> begin
(

let uu____1995 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1995) with
| true -> begin
(

let uu____1996 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1996))
end
| uu____1997 -> begin
(

let uu____1998 = ((not (is_arrow)) && (

let uu____2000 = (FStar_Options.print_bound_var_types ())
in (not (uu____2000))))
in (match (uu____1998) with
| true -> begin
(

let uu____2001 = (nm_to_string a)
in (imp_to_string uu____2001 imp))
end
| uu____2002 -> begin
(

let uu____2003 = (

let uu____2004 = (nm_to_string a)
in (

let uu____2005 = (

let uu____2006 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2006))
in (Prims.strcat uu____2004 uu____2005)))
in (imp_to_string uu____2003 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2018 = (FStar_Options.print_implicits ())
in (match (uu____2018) with
| true -> begin
bs
end
| uu____2021 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2022 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2022 (FStar_String.concat sep)))
end
| uu____2039 -> begin
(

let uu____2040 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2040 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun uu___75_2049 -> (match (uu___75_2049) with
| (a, imp) -> begin
(

let uu____2056 = (term_to_string a)
in (imp_to_string uu____2056 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2065 = (FStar_Options.print_implicits ())
in (match (uu____2065) with
| true -> begin
args
end
| uu____2072 -> begin
(filter_imp args)
end))
in (

let uu____2075 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2075 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2094 = (FStar_Options.ugly ())
in (match (uu____2094) with
| true -> begin
(comp_to_string c)
end
| uu____2095 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2099 = (

let uu____2100 = (FStar_Options.ugly ())
in (not (uu____2100)))
in (match (uu____2099) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2103 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2114 = (

let uu____2115 = (FStar_Syntax_Subst.compress t)
in uu____2115.FStar_Syntax_Syntax.n)
in (match (uu____2114) with
| FStar_Syntax_Syntax.Tm_type (uu____2118) when (

let uu____2119 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2119))) -> begin
(term_to_string t)
end
| uu____2120 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2122 = (univ_to_string u)
in (

let uu____2123 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2122 uu____2123)))
end
| uu____2124 -> begin
(

let uu____2127 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2127))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2138 = (

let uu____2139 = (FStar_Syntax_Subst.compress t)
in uu____2139.FStar_Syntax_Syntax.n)
in (match (uu____2138) with
| FStar_Syntax_Syntax.Tm_type (uu____2142) when (

let uu____2143 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2143))) -> begin
(term_to_string t)
end
| uu____2144 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2146 = (univ_to_string u)
in (

let uu____2147 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2146 uu____2147)))
end
| uu____2148 -> begin
(

let uu____2151 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2151))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2154 = (FStar_Options.print_effect_args ())
in (match (uu____2154) with
| true -> begin
(

let uu____2155 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2156 = (

let uu____2157 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2157 (FStar_String.concat ", ")))
in (

let uu____2166 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2167 = (

let uu____2168 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2168 (FStar_String.concat ", ")))
in (

let uu____2185 = (

let uu____2186 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2186 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2155 uu____2156 uu____2166 uu____2167 uu____2185))))))
end
| uu____2195 -> begin
(

let uu____2196 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___76_2200 -> (match (uu___76_2200) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2201 -> begin
false
end)))) && (

let uu____2203 = (FStar_Options.print_effect_args ())
in (not (uu____2203))))
in (match (uu____2196) with
| true -> begin
(

let uu____2204 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2204))
end
| uu____2205 -> begin
(

let uu____2206 = (((

let uu____2209 = (FStar_Options.print_effect_args ())
in (not (uu____2209))) && (

let uu____2211 = (FStar_Options.print_implicits ())
in (not (uu____2211)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2206) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2212 -> begin
(

let uu____2213 = ((

let uu____2216 = (FStar_Options.print_effect_args ())
in (not (uu____2216))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___77_2220 -> (match (uu___77_2220) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2221 -> begin
false
end)))))
in (match (uu____2213) with
| true -> begin
(

let uu____2222 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2222))
end
| uu____2223 -> begin
(

let uu____2224 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2225 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2224 uu____2225)))
end))
end))
end))
end))
in (

let dec = (

let uu____2227 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___78_2237 -> (match (uu___78_2237) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2243 = (

let uu____2244 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2244))
in (uu____2243)::[])
end
| uu____2245 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2227 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2249) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___79_2255 -> (match (uu___79_2255) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2268 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2296 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2314 -> (match (uu____2314) with
| (t, uu____2320) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2296 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2268 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2326 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2326))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2329) -> begin
(

let uu____2330 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2330))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2338 = (sli m)
in (

let uu____2339 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2338 uu____2339)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2347 = (sli m)
in (

let uu____2348 = (sli m')
in (

let uu____2349 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2347 uu____2348 uu____2349))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2360 = (FStar_Options.ugly ())
in (match (uu____2360) with
| true -> begin
(term_to_string x)
end
| uu____2361 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2374 = b
in (match (uu____2374) with
| (a, imp) -> begin
(

let n1 = (

let uu____2378 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2378) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2379 -> begin
(

let uu____2380 = (

let uu____2381 = (nm_to_string a)
in (imp_to_string uu____2381 imp))
in FStar_Util.JsonStr (uu____2380))
end))
in (

let t = (

let uu____2383 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2383))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2406 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2406)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2418 = (FStar_Options.print_universes ())
in (match (uu____2418) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2419 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2425 = (

let uu____2426 = (FStar_Options.ugly ())
in (not (uu____2426)))
in (match (uu____2425) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2429 -> begin
(

let uu____2430 = s
in (match (uu____2430) with
| (us, t) -> begin
(

let uu____2441 = (

let uu____2442 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2442))
in (

let uu____2443 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2441 uu____2443)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2449 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2450 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2451 = (

let uu____2452 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2452))
in (

let uu____2453 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2454 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2449 uu____2450 uu____2451 uu____2453 uu____2454)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2479 = (

let uu____2480 = (FStar_Options.ugly ())
in (not (uu____2480)))
in (match (uu____2479) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2483 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2494 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2494 (FStar_String.concat ",\n\t"))))
in (

let uu____2503 = (

let uu____2506 = (

let uu____2509 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2510 = (

let uu____2513 = (

let uu____2514 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2514))
in (

let uu____2515 = (

let uu____2518 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2519 = (

let uu____2522 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2523 = (

let uu____2526 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2527 = (

let uu____2530 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2531 = (

let uu____2534 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2535 = (

let uu____2538 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2539 = (

let uu____2542 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2543 = (

let uu____2546 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2547 = (

let uu____2550 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2551 = (

let uu____2554 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2555 = (

let uu____2558 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2559 = (

let uu____2562 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2563 = (

let uu____2566 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2567 = (

let uu____2570 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2571 = (

let uu____2574 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2575 = (

let uu____2578 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2578)::[])
in (uu____2574)::uu____2575))
in (uu____2570)::uu____2571))
in (uu____2566)::uu____2567))
in (uu____2562)::uu____2563))
in (uu____2558)::uu____2559))
in (uu____2554)::uu____2555))
in (uu____2550)::uu____2551))
in (uu____2546)::uu____2547))
in (uu____2542)::uu____2543))
in (uu____2538)::uu____2539))
in (uu____2534)::uu____2535))
in (uu____2530)::uu____2531))
in (uu____2526)::uu____2527))
in (uu____2522)::uu____2523))
in (uu____2518)::uu____2519))
in (uu____2513)::uu____2515))
in (uu____2509)::uu____2510))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2579 -> begin
""
end))::uu____2506)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2503)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____2595 = (

let uu____2596 = (FStar_Options.ugly ())
in (not (uu____2596)))
in (match (uu____2595) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____2602 -> begin
""
end))
end
| uu____2605 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2613, uu____2614) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2626 = (FStar_Options.print_universes ())
in (match (uu____2626) with
| true -> begin
(

let uu____2627 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2627 binders_str term_str))
end
| uu____2628 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2632, uu____2633, uu____2634) -> begin
(

let uu____2639 = (FStar_Options.print_universes ())
in (match (uu____2639) with
| true -> begin
(

let uu____2640 = (univ_names_to_string univs1)
in (

let uu____2641 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2640 lid.FStar_Ident.str uu____2641)))
end
| uu____2642 -> begin
(

let uu____2643 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2643))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2647 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2648 = (

let uu____2649 = (FStar_Options.print_universes ())
in (match (uu____2649) with
| true -> begin
(

let uu____2650 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2650))
end
| uu____2651 -> begin
""
end))
in (

let uu____2652 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2647 lid.FStar_Ident.str uu____2648 uu____2652))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2654, f) -> begin
(

let uu____2656 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2656))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2658) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2664 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2664))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2666) -> begin
(

let uu____2675 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2675 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2705) -> begin
lift_wp
end
| (uu____2712, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2720 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2720) with
| (us, t) -> begin
(

let uu____2727 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2728 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2729 = (univ_names_to_string us)
in (

let uu____2730 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2727 uu____2728 uu____2729 uu____2730)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____2740 = (FStar_Options.print_universes ())
in (match (uu____2740) with
| true -> begin
(

let uu____2741 = (

let uu____2746 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2746))
in (match (uu____2741) with
| (univs2, t) -> begin
(

let uu____2757 = (

let uu____2770 = (

let uu____2771 = (FStar_Syntax_Subst.compress t)
in uu____2771.FStar_Syntax_Syntax.n)
in (match (uu____2770) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____2812 -> begin
(failwith "impossible")
end))
in (match (uu____2757) with
| (tps1, c1) -> begin
(

let uu____2843 = (sli l)
in (

let uu____2844 = (univ_names_to_string univs2)
in (

let uu____2845 = (binders_to_string " " tps1)
in (

let uu____2846 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____2843 uu____2844 uu____2845 uu____2846)))))
end))
end))
end
| uu____2847 -> begin
(

let uu____2848 = (sli l)
in (

let uu____2849 = (binders_to_string " " tps)
in (

let uu____2850 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____2848 uu____2849 uu____2850))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____2857 = (

let uu____2858 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____2858))
in (

let uu____2863 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____2857 uu____2863)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____2864 -> begin
(

let uu____2867 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____2867 (Prims.strcat "\n" basic)))
end))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____2878 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____2878 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____2884, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____2886; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____2888; FStar_Syntax_Syntax.lbdef = uu____2889; FStar_Syntax_Syntax.lbattrs = uu____2890; FStar_Syntax_Syntax.lbpos = uu____2891})::[]), uu____2892) -> begin
(

let uu____2913 = (lbname_to_string lb)
in (

let uu____2914 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____2913 uu____2914)))
end
| uu____2915 -> begin
(

let uu____2916 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____2916 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____2932 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____2933 = (

let uu____2934 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____2934 (FStar_String.concat "\n")))
in (

let uu____2939 = (

let uu____2940 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____2940 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n" uu____2932 uu____2933 uu____2939)))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___80_2949 -> (match (uu___80_2949) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2952 = (FStar_Util.string_of_int i)
in (

let uu____2953 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2952 uu____2953)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2956 = (bv_to_string x)
in (

let uu____2957 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2956 uu____2957)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2964 = (bv_to_string x)
in (

let uu____2965 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____2964 uu____2965)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2968 = (FStar_Util.string_of_int i)
in (

let uu____2969 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2968 uu____2969)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2972 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2972))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2978 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2978 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3016 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____3016));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3023 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3023));
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

let uu____3057 = (f x)
in (FStar_Util.string_builder_append strb uu____3057));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3064 = (f x1)
in (FStar_Util.string_builder_append strb uu____3064));
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

let uu____3102 = (f x)
in (FStar_Util.string_builder_append strb uu____3102));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3109 = (f x1)
in (FStar_Util.string_builder_append strb uu____3109));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3125 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3125)))


let ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____3135 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____3136 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____3137 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format3 "(%s |- %s : %s)" uu____3135 uu____3136 uu____3137)))))





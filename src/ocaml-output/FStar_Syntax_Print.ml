
open Prims
open FStar_Pervasives

let rec delta_depth_to_string : FStar_Syntax_Syntax.delta_depth  ->  Prims.string = (fun uu___202_5 -> (match (uu___202_5) with
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


let is_inr : 'Auu____271 'Auu____272 . ('Auu____271, 'Auu____272) FStar_Util.either  ->  Prims.bool = (fun uu___203_281 -> (match (uu___203_281) with
| FStar_Util.Inl (uu____286) -> begin
false
end
| FStar_Util.Inr (uu____287) -> begin
true
end))


let filter_imp : 'Auu____292 . ('Auu____292 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____292 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___204_347 -> (match (uu___204_347) with
| (uu____354, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____355))) -> begin
false
end
| uu____358 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  exp Prims.list FStar_Pervasives_Native.option = (fun e -> (

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

let uu____436 = ((is_lex_cons f) && (Prims.op_Equality (FStar_List.length exps) (Prims.parse_int "2")))
in (match (uu____436) with
| true -> begin
(

let uu____441 = (

let uu____446 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____446))
in (match (uu____441) with
| FStar_Pervasives_Native.Some (xs) -> begin
(

let uu____456 = (

let uu____459 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____459)::xs)
in FStar_Pervasives_Native.Some (uu____456))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end
| uu____466 -> begin
FStar_Pervasives_Native.None
end))))
end
| uu____469 -> begin
(

let uu____470 = (is_lex_top e)
in (match (uu____470) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____477 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec find : 'a . ('a  ->  Prims.bool)  ->  'a Prims.list  ->  'a = (fun f l -> (match (l) with
| [] -> begin
(failwith "blah")
end
| (hd1)::tl1 -> begin
(

let uu____511 = (f hd1)
in (match (uu____511) with
| true -> begin
hd1
end
| uu____512 -> begin
(find f tl1)
end))
end))


let find_lid : FStar_Ident.lident  ->  (FStar_Ident.lident * Prims.string) Prims.list  ->  Prims.string = (fun x xs -> (

let uu____535 = (find (fun p -> (FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))) xs)
in (FStar_Pervasives_Native.snd uu____535)))


let infix_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____559 = (get_lid e)
in (find_lid uu____559 infix_prim_ops)))


let unary_prim_op_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun e -> (

let uu____569 = (get_lid e)
in (find_lid uu____569 unary_prim_ops)))


let quant_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (

let uu____579 = (get_lid t)
in (find_lid uu____579 quants)))


let const_to_string : FStar_Const.sconst  ->  Prims.string = (fun x -> (FStar_Parser_Const.const_to_string x))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___205_589 -> (match (uu___205_589) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let uvar_to_string : FStar_Syntax_Syntax.uvar  ->  Prims.string = (fun u -> (

let uu____597 = (FStar_Options.hide_uvar_nums ())
in (match (uu____597) with
| true -> begin
"?"
end
| uu____598 -> begin
(

let uu____599 = (

let uu____600 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____600 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____599))
end)))


let version_to_string : FStar_Syntax_Syntax.version  ->  Prims.string = (fun v1 -> (

let uu____606 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major)
in (

let uu____607 = (FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor)
in (FStar_Util.format2 "%s.%s" uu____606 uu____607))))


let univ_uvar_to_string : (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version)  ->  Prims.string = (fun u -> (

let uu____629 = (FStar_Options.hide_uvar_nums ())
in (match (uu____629) with
| true -> begin
"?"
end
| uu____630 -> begin
(

let uu____631 = (

let uu____632 = (

let uu____633 = (FStar_Syntax_Unionfind.univ_uvar_id u)
in (FStar_All.pipe_right uu____633 FStar_Util.string_of_int))
in (

let uu____634 = (

let uu____635 = (version_to_string (FStar_Pervasives_Native.snd u))
in (Prims.strcat ":" uu____635))
in (Prims.strcat uu____632 uu____634)))
in (Prims.strcat "?" uu____631))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____656 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____656) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____666 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____674 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____674) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(

let uu____684 = (univ_uvar_to_string u1)
in (Prims.strcat "U_unif " uu____684))
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(Prims.strcat "U_name " x.FStar_Ident.idText)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____687 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____687))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____689 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____689) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____703 = (univ_to_string u2)
in (

let uu____704 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____703 uu____704)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____708 = (

let uu____709 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____709 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____708))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universes  ->  Prims.string = (fun us -> (

let uu____719 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____719 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Syntax_Syntax.univ_names  ->  Prims.string = (fun us -> (

let uu____729 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____729 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___206_740 -> (match (uu___206_740) with
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

let uu____742 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____742))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____745 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____745 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____756 = (

let uu____757 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____757))
in (

let uu____758 = (

let uu____759 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____759 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____756 uu____758)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____778 = (

let uu____779 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____779))
in (

let uu____780 = (

let uu____781 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____781 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____778 uu____780)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____791 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____791))
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
| uu____802 -> begin
(

let uu____805 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____805 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____823 -> begin
(

let uu____826 = (quals_to_string quals)
in (Prims.strcat uu____826 " "))
end))


let paren : Prims.string  ->  Prims.string = (fun s -> (Prims.strcat "(" (Prims.strcat s ")")))


let rec tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____970 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____970))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____972 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____972))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____974 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____974))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____975) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____982) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____983) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____984, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____985}) -> begin
"Tm_quoted (static)"
end
| FStar_Syntax_Syntax.Tm_quoted (uu____1000, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1001}) -> begin
"Tm_quoted (dynamic)"
end
| FStar_Syntax_Syntax.Tm_abs (uu____1016) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____1035) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____1050) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____1057) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____1074) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____1097) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____1124) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____1137) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____1150, m) -> begin
(

let uu____1188 = (FStar_ST.op_Bang m)
in (match (uu____1188) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____1244) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____1249, m) -> begin
(

let uu____1255 = (metadata_to_string m)
in (Prims.strcat "Tm_meta:" uu____1255))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end
| FStar_Syntax_Syntax.Tm_lazy (uu____1256) -> begin
"Tm_lazy"
end))
and term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____1258 = (

let uu____1259 = (FStar_Options.ugly ())
in (not (uu____1259)))
in (match (uu____1258) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1262 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____1267 = (FStar_Options.print_implicits ())
in (match (uu____1267) with
| true -> begin
x1
end
| uu____1270 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1271) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____1294, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_lazy ({FStar_Syntax_Syntax.blob = b; FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding (uu____1318, thunk); FStar_Syntax_Syntax.ltyp = uu____1320; FStar_Syntax_Syntax.rng = uu____1321}) -> begin
(

let uu____1332 = (FStar_Common.force_thunk thunk)
in (term_to_string uu____1332))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1376 = (

let uu____1377 = (

let uu____1378 = (

let uu____1379 = (

let uu____1388 = (FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser)
in (FStar_Util.must uu____1388))
in (uu____1379 i.FStar_Syntax_Syntax.lkind i))
in (term_to_string uu____1378))
in (Prims.strcat uu____1377 "]"))
in (Prims.strcat "[lazy:" uu____1376))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = uu____1439}) -> begin
(

let uu____1454 = (term_to_string tm)
in (FStar_Util.format1 "`(%s)" uu____1454))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____1456}) -> begin
(

let uu____1471 = (term_to_string tm)
in (FStar_Util.format1 "quote (%s)" uu____1471))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____1491 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____1525 = (FStar_All.pipe_right args (FStar_List.map (fun uu____1547 -> (match (uu____1547) with
| (t1, uu____1555) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____1525 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____1491 (FStar_String.concat "\\/")))
in (

let uu____1564 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____1564)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____1576 = (tag_of_term t)
in (

let uu____1577 = (sli m)
in (

let uu____1578 = (term_to_string t')
in (

let uu____1579 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1576 uu____1577 uu____1578 uu____1579)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____1592 = (tag_of_term t)
in (

let uu____1593 = (term_to_string t')
in (

let uu____1594 = (sli m0)
in (

let uu____1595 = (sli m1)
in (

let uu____1596 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1592 uu____1593 uu____1594 uu____1595 uu____1596))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) -> begin
(

let uu____1605 = (FStar_Range.string_of_range r)
in (

let uu____1606 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1605 uu____1606)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named (l)) -> begin
(

let uu____1613 = (lid_to_string l)
in (

let uu____1614 = (FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____1615 = (term_to_string t)
in (FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1613 uu____1614 uu____1615))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_desugared (uu____1617)) -> begin
(

let uu____1622 = (term_to_string t)
in (FStar_Util.format1 "Meta_desugared{%s}" uu____1622))
end
| FStar_Syntax_Syntax.Tm_bvar (x3) -> begin
(

let uu____1624 = (db_to_string x3)
in (

let uu____1625 = (

let uu____1626 = (

let uu____1627 = (tag_of_term x3.FStar_Syntax_Syntax.sort)
in (Prims.strcat uu____1627 ")"))
in (Prims.strcat ":(" uu____1626))
in (Prims.strcat uu____1624 uu____1625)))
end
| FStar_Syntax_Syntax.Tm_name (x3) -> begin
(nm_to_string x3)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____1631)) -> begin
(

let uu____1646 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____1646) with
| true -> begin
(ctx_uvar_to_string u)
end
| uu____1647 -> begin
(

let uu____1648 = (

let uu____1649 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1649))
in (Prims.strcat "?" uu____1648))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (u, s) -> begin
(

let uu____1668 = ((FStar_Options.print_bound_var_types ()) && (FStar_Options.print_effect_args ()))
in (match (uu____1668) with
| true -> begin
(

let uu____1669 = (ctx_uvar_to_string u)
in (

let uu____1670 = (

let uu____1671 = (FStar_List.map subst_to_string (FStar_Pervasives_Native.fst s))
in (FStar_All.pipe_right uu____1671 (FStar_String.concat "; ")))
in (FStar_Util.format2 "(%s @ %s)" uu____1669 uu____1670)))
end
| uu____1682 -> begin
(

let uu____1683 = (

let uu____1684 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1684))
in (Prims.strcat "?" uu____1683))
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1687 = (FStar_Options.print_universes ())
in (match (uu____1687) with
| true -> begin
(

let uu____1688 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____1688))
end
| uu____1689 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____1712 = (binders_to_string " -> " bs)
in (

let uu____1713 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____1712 uu____1713)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (rc) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1742 = (binders_to_string " " bs)
in (

let uu____1743 = (term_to_string t2)
in (

let uu____1744 = (match ((FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ)) with
| true -> begin
"None"
end
| uu____1747 -> begin
(

let uu____1748 = (FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ)
in (term_to_string uu____1748))
end)
in (FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))" uu____1742 uu____1743 rc.FStar_Syntax_Syntax.residual_effect.FStar_Ident.str uu____1744))))
end
| uu____1751 -> begin
(

let uu____1754 = (binders_to_string " " bs)
in (

let uu____1755 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1754 uu____1755)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1762 = (bv_to_string xt)
in (

let uu____1763 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1764 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1762 uu____1763 uu____1764))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1793 = (term_to_string t)
in (

let uu____1794 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1793 uu____1794)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1813 = (lbs_to_string [] lbs)
in (

let uu____1814 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1813 uu____1814)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1875 = (

let uu____1876 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1876 (FStar_Util.dflt "default")))
in (

let uu____1881 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1875 uu____1881)))
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

let uu____1897 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1897))
end)
in (

let uu____1898 = (term_to_string e)
in (FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1898 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1937 = (term_to_string head1)
in (

let uu____1938 = (

let uu____1939 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1969 -> (match (uu____1969) with
| (p, wopt, e) -> begin
(

let uu____1985 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1986 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1988 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1988))
end)
in (

let uu____1989 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1985 uu____1986 uu____1989))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1939))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1937 uu____1938)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1996 = (FStar_Options.print_universes ())
in (match (uu____1996) with
| true -> begin
(

let uu____1997 = (term_to_string t)
in (

let uu____1998 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1997 uu____1998)))
end
| uu____1999 -> begin
(term_to_string t)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"_"
end)))
end)))
and ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar  ->  Prims.string = (fun ctx_uvar -> (

let uu____2001 = (binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders)
in (

let uu____2002 = (uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head)
in (

let uu____2003 = (term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ)
in (FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)" ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2001 uu____2002 uu____2003)))))
and subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___207_2004 -> (match (uu___207_2004) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____2007 = (FStar_Util.string_of_int i)
in (

let uu____2008 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____2007 uu____2008)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____2011 = (bv_to_string x)
in (

let uu____2012 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____2011 uu____2012)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____2019 = (bv_to_string x)
in (

let uu____2020 = (term_to_string t)
in (FStar_Util.format2 "NT (%s, %s)" uu____2019 uu____2020)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____2023 = (FStar_Util.string_of_int i)
in (

let uu____2024 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____2023 uu____2024)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____2027 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2027))
end))
and subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____2029 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____2029 (FStar_String.concat "; "))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____2039 = (

let uu____2040 = (FStar_Options.ugly ())
in (not (uu____2040)))
in (match (uu____2039) with
| true -> begin
(

let e = (

let uu____2042 = (FStar_Syntax_Syntax.new_bv_set ())
in (FStar_Syntax_Resugar.resugar_pat x uu____2042))
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2046 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____2065 = (fv_to_string l)
in (

let uu____2066 = (

let uu____2067 = (FStar_List.map (fun uu____2078 -> (match (uu____2078) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____2086 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____2067 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____2065 uu____2066)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2090) -> begin
(

let uu____2095 = (FStar_Options.print_bound_var_types ())
in (match (uu____2095) with
| true -> begin
(

let uu____2096 = (bv_to_string x1)
in (

let uu____2097 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____2096 uu____2097)))
end
| uu____2098 -> begin
(

let uu____2099 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____2099))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____2101 = (FStar_Options.print_bound_var_types ())
in (match (uu____2101) with
| true -> begin
(

let uu____2102 = (bv_to_string x1)
in (

let uu____2103 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____2102 uu____2103)))
end
| uu____2104 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____2107 = (FStar_Options.print_real_names ())
in (match (uu____2107) with
| true -> begin
(

let uu____2108 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____2108))
end
| uu____2109 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let uu____2120 = (quals_to_string' quals)
in (

let uu____2121 = (

let uu____2122 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____2138 = (attrs_to_string lb.FStar_Syntax_Syntax.lbattrs)
in (

let uu____2139 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____2140 = (

let uu____2141 = (FStar_Options.print_universes ())
in (match (uu____2141) with
| true -> begin
(

let uu____2142 = (

let uu____2143 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____2143 ">"))
in (Prims.strcat "<" uu____2142))
end
| uu____2144 -> begin
""
end))
in (

let uu____2145 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2146 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2138 uu____2139 uu____2140 uu____2145 uu____2146)))))))))
in (FStar_Util.concat_l "\n and " uu____2122))
in (FStar_Util.format3 "%slet %s %s" uu____2120 (match ((FStar_Pervasives_Native.fst lbs)) with
| true -> begin
"rec"
end
| uu____2149 -> begin
""
end) uu____2121))))
and attrs_to_string : FStar_Syntax_Syntax.attribute Prims.list  ->  Prims.string = (fun uu___208_2150 -> (match (uu___208_2150) with
| [] -> begin
""
end
| tms -> begin
(

let uu____2156 = (

let uu____2157 = (FStar_List.map (fun t -> (

let uu____2163 = (term_to_string t)
in (paren uu____2163))) tms)
in (FStar_All.pipe_right uu____2157 (FStar_String.concat "; ")))
in (FStar_Util.format1 "[@ %s]" uu____2156))
end))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____2167 = (FStar_Options.print_effect_args ())
in (match (uu____2167) with
| true -> begin
(

let uu____2168 = (FStar_Syntax_Syntax.lcomp_comp lc)
in (comp_to_string uu____2168))
end
| uu____2169 -> begin
(

let uu____2170 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____2171 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____2170 uu____2171)))
end)))
and aqual_to_string : FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun uu___209_2172 -> (match (uu___209_2172) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
"#"
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
"#."
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
"$"
end
| uu____2173 -> begin
""
end))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.aqual  ->  Prims.string = (fun s aq -> (

let uu____2176 = (aqual_to_string aq)
in (Prims.strcat uu____2176 s)))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun is_arrow b -> (

let uu____2185 = (

let uu____2186 = (FStar_Options.ugly ())
in (not (uu____2186)))
in (match (uu____2185) with
| true -> begin
(

let uu____2187 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____2187) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____2192 -> begin
(

let uu____2193 = b
in (match (uu____2193) with
| (a, imp) -> begin
(

let uu____2206 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2206) with
| true -> begin
(

let uu____2207 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____2207))
end
| uu____2208 -> begin
(

let uu____2209 = ((not (is_arrow)) && (

let uu____2211 = (FStar_Options.print_bound_var_types ())
in (not (uu____2211))))
in (match (uu____2209) with
| true -> begin
(

let uu____2212 = (nm_to_string a)
in (imp_to_string uu____2212 imp))
end
| uu____2213 -> begin
(

let uu____2214 = (

let uu____2215 = (nm_to_string a)
in (

let uu____2216 = (

let uu____2217 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____2217))
in (Prims.strcat uu____2215 uu____2216)))
in (imp_to_string uu____2214 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____2231 = (FStar_Options.print_implicits ())
in (match (uu____2231) with
| true -> begin
bs
end
| uu____2234 -> begin
(filter_imp bs)
end))
in (match ((Prims.op_Equality sep " -> ")) with
| true -> begin
(

let uu____2235 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____2235 (FStar_String.concat sep)))
end
| uu____2256 -> begin
(

let uu____2257 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____2257 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun uu___210_2266 -> (match (uu___210_2266) with
| (a, imp) -> begin
(

let uu____2273 = (term_to_string a)
in (imp_to_string uu____2273 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____2282 = (FStar_Options.print_implicits ())
in (match (uu____2282) with
| true -> begin
args
end
| uu____2289 -> begin
(filter_imp args)
end))
in (

let uu____2292 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2292 (FStar_String.concat " ")))))
and comp_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  Prims.string = (fun env c -> (

let uu____2311 = (FStar_Options.ugly ())
in (match (uu____2311) with
| true -> begin
(comp_to_string c)
end
| uu____2312 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp' env c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____2316 = (

let uu____2317 = (FStar_Options.ugly ())
in (not (uu____2317)))
in (match (uu____2316) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____2320 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uopt) -> begin
(

let uu____2331 = (

let uu____2332 = (FStar_Syntax_Subst.compress t)
in uu____2332.FStar_Syntax_Syntax.n)
in (match (uu____2331) with
| FStar_Syntax_Syntax.Tm_type (uu____2335) when (

let uu____2336 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2336))) -> begin
(term_to_string t)
end
| uu____2337 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2339 = (univ_to_string u)
in (

let uu____2340 = (term_to_string t)
in (FStar_Util.format2 "Tot<%s> %s" uu____2339 uu____2340)))
end
| uu____2341 -> begin
(

let uu____2344 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____2344))
end)
end))
end
| FStar_Syntax_Syntax.GTotal (t, uopt) -> begin
(

let uu____2355 = (

let uu____2356 = (FStar_Syntax_Subst.compress t)
in uu____2356.FStar_Syntax_Syntax.n)
in (match (uu____2355) with
| FStar_Syntax_Syntax.Tm_type (uu____2359) when (

let uu____2360 = ((FStar_Options.print_implicits ()) || (FStar_Options.print_universes ()))
in (not (uu____2360))) -> begin
(term_to_string t)
end
| uu____2361 -> begin
(match (uopt) with
| FStar_Pervasives_Native.Some (u) when (FStar_Options.print_universes ()) -> begin
(

let uu____2363 = (univ_to_string u)
in (

let uu____2364 = (term_to_string t)
in (FStar_Util.format2 "GTot<%s> %s" uu____2363 uu____2364)))
end
| uu____2365 -> begin
(

let uu____2368 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____2368))
end)
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____2371 = (FStar_Options.print_effect_args ())
in (match (uu____2371) with
| true -> begin
(

let uu____2372 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2373 = (

let uu____2374 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs (FStar_List.map univ_to_string))
in (FStar_All.pipe_right uu____2374 (FStar_String.concat ", ")))
in (

let uu____2383 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____2384 = (

let uu____2385 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____2385 (FStar_String.concat ", ")))
in (

let uu____2402 = (

let uu____2403 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____2403 (FStar_String.concat " ")))
in (FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2372 uu____2373 uu____2383 uu____2384 uu____2402))))))
end
| uu____2412 -> begin
(

let uu____2413 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___211_2417 -> (match (uu___211_2417) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____2418 -> begin
false
end)))) && (

let uu____2420 = (FStar_Options.print_effect_args ())
in (not (uu____2420))))
in (match (uu____2413) with
| true -> begin
(

let uu____2421 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____2421))
end
| uu____2422 -> begin
(

let uu____2423 = (((

let uu____2426 = (FStar_Options.print_effect_args ())
in (not (uu____2426))) && (

let uu____2428 = (FStar_Options.print_implicits ())
in (not (uu____2428)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____2423) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____2429 -> begin
(

let uu____2430 = ((

let uu____2433 = (FStar_Options.print_effect_args ())
in (not (uu____2433))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___212_2437 -> (match (uu___212_2437) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____2438 -> begin
false
end)))))
in (match (uu____2430) with
| true -> begin
(

let uu____2439 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____2439))
end
| uu____2440 -> begin
(

let uu____2441 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____2442 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____2441 uu____2442)))
end))
end))
end))
end))
in (

let dec = (

let uu____2444 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___213_2454 -> (match (uu___213_2454) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____2460 = (

let uu____2461 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____2461))
in (uu____2460)::[])
end
| uu____2462 -> begin
[]
end))))
in (FStar_All.pipe_right uu____2444 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____2466) -> begin
""
end))
and formula_to_string : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))
and metadata_to_string : FStar_Syntax_Syntax.metadata  ->  Prims.string = (fun uu___214_2472 -> (match (uu___214_2472) with
| FStar_Syntax_Syntax.Meta_pattern (ps) -> begin
(

let pats = (

let uu____2487 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____2521 = (FStar_All.pipe_right args (FStar_List.map (fun uu____2543 -> (match (uu____2543) with
| (t, uu____2551) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____2521 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____2487 (FStar_String.concat "\\/")))
in (FStar_Util.format1 "{Meta_pattern %s}" pats))
end
| FStar_Syntax_Syntax.Meta_named (lid) -> begin
(

let uu____2561 = (sli lid)
in (FStar_Util.format1 "{Meta_named %s}" uu____2561))
end
| FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2564) -> begin
(

let uu____2565 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2565))
end
| FStar_Syntax_Syntax.Meta_desugared (msi) -> begin
"{Meta_desugared}"
end
| FStar_Syntax_Syntax.Meta_monadic (m, t) -> begin
(

let uu____2573 = (sli m)
in (

let uu____2574 = (term_to_string t)
in (FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2573 uu____2574)))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) -> begin
(

let uu____2582 = (sli m)
in (

let uu____2583 = (sli m')
in (

let uu____2584 = (term_to_string t)
in (FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2582 uu____2583 uu____2584))))
end))


let term_to_string' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  Prims.string = (fun env x -> (

let uu____2595 = (FStar_Options.ugly ())
in (match (uu____2595) with
| true -> begin
(term_to_string x)
end
| uu____2596 -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term' env x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end)))


let binder_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Util.json = (fun env b -> (

let uu____2609 = b
in (match (uu____2609) with
| (a, imp) -> begin
(

let n1 = (

let uu____2617 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____2617) with
| true -> begin
FStar_Util.JsonNull
end
| uu____2618 -> begin
(

let uu____2619 = (

let uu____2620 = (nm_to_string a)
in (imp_to_string uu____2620 imp))
in FStar_Util.JsonStr (uu____2619))
end))
in (

let t = (

let uu____2622 = (term_to_string' env a.FStar_Syntax_Syntax.sort)
in FStar_Util.JsonStr (uu____2622))
in FStar_Util.JsonAssoc (((("name"), (n1)))::((("type"), (t)))::[])))
end)))


let binders_to_json : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Util.json = (fun env bs -> (

let uu____2645 = (FStar_List.map (binder_to_json env) bs)
in FStar_Util.JsonList (uu____2645)))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____2659 = (FStar_Options.print_universes ())
in (match (uu____2659) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____2660 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____2666 = (

let uu____2667 = (FStar_Options.ugly ())
in (not (uu____2667)))
in (match (uu____2666) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2670 -> begin
(

let uu____2671 = s
in (match (uu____2671) with
| (us, t) -> begin
(

let uu____2682 = (

let uu____2683 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____2683))
in (

let uu____2684 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____2682 uu____2684)))
end))
end)))


let action_to_string : FStar_Syntax_Syntax.action  ->  Prims.string = (fun a -> (

let uu____2690 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____2691 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____2692 = (

let uu____2693 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____2693))
in (

let uu____2694 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____2695 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____2690 uu____2691 uu____2692 uu____2694 uu____2695)))))))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____2720 = (

let uu____2721 = (FStar_Options.ugly ())
in (not (uu____2721)))
in (match (uu____2720) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____2724 -> begin
(

let actions_to_string = (fun actions -> (

let uu____2735 = (FStar_All.pipe_right actions (FStar_List.map action_to_string))
in (FStar_All.pipe_right uu____2735 (FStar_String.concat ",\n\t"))))
in (

let uu____2744 = (

let uu____2747 = (

let uu____2750 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____2751 = (

let uu____2754 = (

let uu____2755 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____2755))
in (

let uu____2756 = (

let uu____2759 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____2760 = (

let uu____2763 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____2764 = (

let uu____2767 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____2768 = (

let uu____2771 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____2772 = (

let uu____2775 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____2776 = (

let uu____2779 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____2780 = (

let uu____2783 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____2784 = (

let uu____2787 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____2788 = (

let uu____2791 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____2792 = (

let uu____2795 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____2796 = (

let uu____2799 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____2800 = (

let uu____2803 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____2804 = (

let uu____2807 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____2808 = (

let uu____2811 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____2812 = (

let uu____2815 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____2816 = (

let uu____2819 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____2819)::[])
in (uu____2815)::uu____2816))
in (uu____2811)::uu____2812))
in (uu____2807)::uu____2808))
in (uu____2803)::uu____2804))
in (uu____2799)::uu____2800))
in (uu____2795)::uu____2796))
in (uu____2791)::uu____2792))
in (uu____2787)::uu____2788))
in (uu____2783)::uu____2784))
in (uu____2779)::uu____2780))
in (uu____2775)::uu____2776))
in (uu____2771)::uu____2772))
in (uu____2767)::uu____2768))
in (uu____2763)::uu____2764))
in (uu____2759)::uu____2760))
in (uu____2754)::uu____2756))
in (uu____2750)::uu____2751))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____2820 -> begin
""
end))::uu____2747)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____2744)))
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____2844, uu____2845) -> begin
(

let quals_str = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let binders_str = (binders_to_string " " tps)
in (

let term_str = (term_to_string k)
in (

let uu____2857 = (FStar_Options.print_universes ())
in (match (uu____2857) with
| true -> begin
(

let uu____2858 = (univ_names_to_string univs1)
in (FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str lid.FStar_Ident.str uu____2858 binders_str term_str))
end
| uu____2859 -> begin
(FStar_Util.format4 "%stype %s %s : %s" quals_str lid.FStar_Ident.str binders_str term_str)
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____2863, uu____2864, uu____2865) -> begin
(

let uu____2870 = (FStar_Options.print_universes ())
in (match (uu____2870) with
| true -> begin
(

let uu____2871 = (univ_names_to_string univs1)
in (

let uu____2872 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____2871 lid.FStar_Ident.str uu____2872)))
end
| uu____2873 -> begin
(

let uu____2874 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____2874))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____2878 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____2879 = (

let uu____2880 = (FStar_Options.print_universes ())
in (match (uu____2880) with
| true -> begin
(

let uu____2881 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____2881))
end
| uu____2882 -> begin
""
end))
in (

let uu____2883 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____2878 lid.FStar_Ident.str uu____2879 uu____2883))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, us, f) -> begin
(

let uu____2887 = (FStar_Options.print_universes ())
in (match (uu____2887) with
| true -> begin
(

let uu____2888 = (univ_names_to_string us)
in (

let uu____2889 = (term_to_string f)
in (FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str uu____2888 uu____2889)))
end
| uu____2890 -> begin
(

let uu____2891 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2891))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____2893) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____2899 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____2899))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____2901) -> begin
(

let uu____2910 = (

let uu____2911 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____2911 (FStar_String.concat "\n")))
in (Prims.strcat "(* Sig_bundle *)" uu____2910))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____2947) -> begin
lift_wp
end
| (uu____2954, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____2962 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____2962) with
| (us, t) -> begin
(

let uu____2973 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____2974 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____2975 = (univ_names_to_string us)
in (

let uu____2976 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2973 uu____2974 uu____2975 uu____2976)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1) -> begin
(

let uu____2986 = (FStar_Options.print_universes ())
in (match (uu____2986) with
| true -> begin
(

let uu____2987 = (

let uu____2992 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____2992))
in (match (uu____2987) with
| (univs2, t) -> begin
(

let uu____3005 = (

let uu____3010 = (

let uu____3011 = (FStar_Syntax_Subst.compress t)
in uu____3011.FStar_Syntax_Syntax.n)
in (match (uu____3010) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____3040 -> begin
(failwith "impossible")
end))
in (match (uu____3005) with
| (tps1, c1) -> begin
(

let uu____3047 = (sli l)
in (

let uu____3048 = (univ_names_to_string univs2)
in (

let uu____3049 = (binders_to_string " " tps1)
in (

let uu____3050 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____3047 uu____3048 uu____3049 uu____3050)))))
end))
end))
end
| uu____3051 -> begin
(

let uu____3052 = (sli l)
in (

let uu____3053 = (binders_to_string " " tps)
in (

let uu____3054 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____3052 uu____3053 uu____3054))))
end))
end
| FStar_Syntax_Syntax.Sig_splice (lids, t) -> begin
(

let uu____3061 = (

let uu____3062 = (FStar_List.map FStar_Ident.string_of_lid lids)
in (FStar_All.pipe_left (FStar_String.concat "; ") uu____3062))
in (

let uu____3067 = (term_to_string t)
in (FStar_Util.format2 "splice[%s] (%s)" uu____3061 uu____3067)))
end)
in (match (x.FStar_Syntax_Syntax.sigattrs) with
| [] -> begin
basic
end
| uu____3068 -> begin
(

let uu____3071 = (attrs_to_string x.FStar_Syntax_Syntax.sigattrs)
in (Prims.strcat uu____3071 (Prims.strcat "\n" basic)))
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____3082 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____3082 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____3088, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____3090; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____3092; FStar_Syntax_Syntax.lbdef = uu____3093; FStar_Syntax_Syntax.lbattrs = uu____3094; FStar_Syntax_Syntax.lbpos = uu____3095})::[]), uu____3096) -> begin
(

let uu____3117 = (lbname_to_string lb)
in (

let uu____3118 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____3117 uu____3118)))
end
| uu____3119 -> begin
(

let uu____3120 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____3120 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____3136 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____3137 = (

let uu____3138 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____3138 (FStar_String.concat "\n")))
in (

let uu____3143 = (

let uu____3144 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports)
in (FStar_All.pipe_right uu____3144 (FStar_String.concat "\n")))
in (FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n" uu____3136 uu____3137 uu____3143)))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either FStar_Pervasives_Native.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.string_builder_append strb "None")
end
| FStar_Pervasives_Native.Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3178 = (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name)
in (FStar_Util.string_builder_append strb uu____3178));
)
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (lid)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(

let uu____3185 = (FStar_Ident.text_of_lid lid)
in (FStar_Util.string_builder_append strb uu____3185));
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

let uu____3219 = (f x)
in (FStar_Util.string_builder_append strb uu____3219));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____3226 = (f x1)
in (FStar_Util.string_builder_append strb uu____3226));
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

let uu____3264 = (f x)
in (FStar_Util.string_builder_append strb uu____3264));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____3271 = (f x1)
in (FStar_Util.string_builder_append strb uu____3271));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))


let bvs_to_string : Prims.string  ->  FStar_Syntax_Syntax.bv Prims.list  ->  Prims.string = (fun sep bvs -> (

let uu____3287 = (FStar_List.map FStar_Syntax_Syntax.mk_binder bvs)
in (binders_to_string sep uu____3287)))





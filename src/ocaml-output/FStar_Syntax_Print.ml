
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
| FStar_Const.Const_string (s, uu____427) -> begin
(FStar_Util.format1 "\"%s\"" s)
end
| FStar_Const.Const_bytearray (uu____428) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x1, uu____433) -> begin
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

let uu____443 = (sli l)
in (FStar_Util.format1 "[[%s.reflect]]" uu____443))
end))


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___202_446 -> (match (uu___202_446) with
| FStar_Util.Inl (l) -> begin
(bv_to_string l)
end
| FStar_Util.Inr (l) -> begin
(lid_to_string l.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))


let tag_of_term : FStar_Syntax_Syntax.term  ->  Prims.string = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____457 = (db_to_string x)
in (Prims.strcat "Tm_bvar: " uu____457))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let uu____459 = (nm_to_string x)
in (Prims.strcat "Tm_name: " uu____459))
end
| FStar_Syntax_Syntax.Tm_fvar (x) -> begin
(

let uu____461 = (lid_to_string x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (Prims.strcat "Tm_fvar: " uu____461))
end
| FStar_Syntax_Syntax.Tm_uinst (uu____466) -> begin
"Tm_uinst"
end
| FStar_Syntax_Syntax.Tm_constant (uu____471) -> begin
"Tm_constant"
end
| FStar_Syntax_Syntax.Tm_type (uu____472) -> begin
"Tm_type"
end
| FStar_Syntax_Syntax.Tm_abs (uu____473) -> begin
"Tm_abs"
end
| FStar_Syntax_Syntax.Tm_arrow (uu____488) -> begin
"Tm_arrow"
end
| FStar_Syntax_Syntax.Tm_refine (uu____496) -> begin
"Tm_refine"
end
| FStar_Syntax_Syntax.Tm_app (uu____501) -> begin
"Tm_app"
end
| FStar_Syntax_Syntax.Tm_match (uu____511) -> begin
"Tm_match"
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____527) -> begin
"Tm_ascribed"
end
| FStar_Syntax_Syntax.Tm_let (uu____545) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____553) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____562, m) -> begin
(

let uu____600 = (FStar_ST.read m)
in (match (uu____600) with
| FStar_Pervasives_Native.None -> begin
"Tm_delayed"
end
| FStar_Pervasives_Native.Some (uu____611) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____616) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> (

let uu____630 = (FStar_Options.hide_uvar_nums ())
in (match (uu____630) with
| true -> begin
"?"
end
| uu____631 -> begin
(

let uu____632 = (

let uu____633 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____633 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____632))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option) = (fun n1 u -> (

let uu____643 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____643) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (FStar_Pervasives_Native.None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____649 -> begin
((n1), (FStar_Pervasives_Native.Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____654 = (

let uu____655 = (FStar_Options.ugly ())
in (not (uu____655)))
in (match (uu____654) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____658 -> begin
(

let uu____659 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____659) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____666 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____666))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____668 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____668) with
| (n1, FStar_Pervasives_Native.None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, FStar_Pervasives_Native.Some (u2)) -> begin
(

let uu____677 = (univ_to_string u2)
in (

let uu____678 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____677 uu____678)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____681 = (

let uu____682 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____682 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____681))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end))
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____690 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____690 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____698 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____698 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___203_704 -> (match (uu___203_704) with
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

let uu____706 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____706))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____709 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____709 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____716 = (

let uu____717 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____717))
in (

let uu____719 = (

let uu____720 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____720 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____716 uu____719)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____731 = (

let uu____732 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____732))
in (

let uu____734 = (

let uu____735 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____735 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____731 uu____734)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____741 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____741))
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
| uu____748 -> begin
(

let uu____750 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____750 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____760 -> begin
(

let uu____762 = (quals_to_string quals)
in (Prims.strcat uu____762 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let uu____810 = (

let uu____811 = (FStar_Options.ugly ())
in (not (uu____811)))
in (match (uu____810) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_term x)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____814 -> begin
(

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____817 = (FStar_Options.print_implicits ())
in (match (uu____817) with
| true -> begin
x1
end
| uu____818 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____819) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____840, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____867 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____883 = (FStar_All.pipe_right args (FStar_List.map (fun uu____891 -> (match (uu____891) with
| (t1, uu____895) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____883 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____867 (FStar_String.concat "\\/")))
in (

let uu____898 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____898)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____910 = (tag_of_term t)
in (

let uu____911 = (sli m)
in (

let uu____912 = (term_to_string t')
in (

let uu____913 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____910 uu____911 uu____912 uu____913)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____926 = (tag_of_term t)
in (

let uu____927 = (term_to_string t')
in (

let uu____928 = (sli m0)
in (

let uu____929 = (sli m1)
in (

let uu____930 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____926 uu____927 uu____928 uu____929 uu____930))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____939 = (FStar_Range.string_of_range r)
in (

let uu____940 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____939 uu____940)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____942) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, uu____951) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____969 = (FStar_Options.print_universes ())
in (match (uu____969) with
| true -> begin
(

let uu____970 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____970))
end
| uu____971 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____984 = (binders_to_string " -> " bs)
in (

let uu____985 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____984 uu____985)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1020 = (binders_to_string " " bs)
in (

let uu____1021 = (term_to_string t2)
in (

let uu____1022 = (

let uu____1023 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string uu____1023))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1020 uu____1021 uu____1022))))
end
| FStar_Pervasives_Native.Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1036 = (binders_to_string " " bs)
in (

let uu____1037 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" uu____1036 uu____1037 l.FStar_Ident.str)))
end
| uu____1038 -> begin
(

let uu____1045 = (binders_to_string " " bs)
in (

let uu____1046 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1045 uu____1046)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1053 = (bv_to_string xt)
in (

let uu____1054 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1057 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1053 uu____1054 uu____1057))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1076 = (term_to_string t)
in (

let uu____1077 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1076 uu____1077)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1090 = (lbs_to_string [] lbs)
in (

let uu____1091 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1090 uu____1091)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1139 = (

let uu____1140 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1140 (FStar_Util.dflt "default")))
in (

let uu____1143 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1139 uu____1143)))
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

let uu____1159 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1159))
end)
in (

let uu____1160 = (term_to_string e)
in (FStar_Util.format3 "(%s <: %s %s)" uu____1160 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1189 = (term_to_string head1)
in (

let uu____1190 = (

let uu____1191 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1209 -> (match (uu____1209) with
| (p, wopt, e) -> begin
(

let uu____1219 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1220 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (w) -> begin
(

let uu____1222 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1222))
end)
in (

let uu____1223 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1219 uu____1220 uu____1223))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1191))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1189 uu____1190)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1230 = (FStar_Options.print_universes ())
in (match (uu____1230) with
| true -> begin
(

let uu____1231 = (term_to_string t)
in (

let uu____1232 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1231 uu____1232)))
end
| uu____1233 -> begin
(term_to_string t)
end))
end
| uu____1234 -> begin
(tag_of_term x2)
end)))
end)))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (

let uu____1236 = (

let uu____1237 = (FStar_Options.ugly ())
in (not (uu____1237)))
in (match (uu____1236) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_pat x)
in (

let d = (FStar_Parser_ToDocument.pat_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1240 -> begin
(match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1253 = (fv_to_string l)
in (

let uu____1254 = (

let uu____1255 = (FStar_List.map (fun uu____1259 -> (match (uu____1259) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1265 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1255 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1253 uu____1254)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1268) -> begin
(

let uu____1273 = (FStar_Options.print_bound_var_types ())
in (match (uu____1273) with
| true -> begin
(

let uu____1274 = (bv_to_string x1)
in (

let uu____1275 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1274 uu____1275)))
end
| uu____1276 -> begin
(

let uu____1277 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1277))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1279 = (FStar_Options.print_bound_var_types ())
in (match (uu____1279) with
| true -> begin
(

let uu____1280 = (bv_to_string x1)
in (

let uu____1281 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1280 uu____1281)))
end
| uu____1282 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1285 = (FStar_Options.print_real_names ())
in (match (uu____1285) with
| true -> begin
(

let uu____1286 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1286))
end
| uu____1287 -> begin
"_"
end))
end)
end)))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1298 = (FStar_Options.print_universes ())
in (match (uu____1298) with
| true -> begin
(

let uu____1302 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let uu____1308 = (

let uu____1311 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1311))
in (match (uu____1308) with
| (us, td) -> begin
(

let uu____1314 = (

let uu____1321 = (

let uu____1322 = (FStar_Syntax_Subst.compress td)
in uu____1322.FStar_Syntax_Syntax.n)
in (match (uu____1321) with
| FStar_Syntax_Syntax.Tm_app (uu____1331, ((t, uu____1333))::((d, uu____1335))::[]) -> begin
((t), (d))
end
| uu____1369 -> begin
(failwith "Impossibe")
end))
in (match (uu____1314) with
| (t, d) -> begin
(

let uu___210_1386 = lb
in {FStar_Syntax_Syntax.lbname = uu___210_1386.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___210_1386.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____1302)))
end
| uu____1389 -> begin
lbs
end))
in (

let uu____1390 = (quals_to_string' quals)
in (

let uu____1391 = (

let uu____1392 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1398 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1399 = (

let uu____1400 = (FStar_Options.print_universes ())
in (match (uu____1400) with
| true -> begin
(

let uu____1401 = (

let uu____1402 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1402 ">"))
in (Prims.strcat "<" uu____1401))
end
| uu____1403 -> begin
""
end))
in (

let uu____1404 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1405 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1398 uu____1399 uu____1404 uu____1405))))))))
in (FStar_Util.concat_l "\n and " uu____1392))
in (FStar_Util.format3 "%slet %s %s" uu____1390 (match ((FStar_Pervasives_Native.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1409 -> begin
""
end) uu____1391)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1411 = (FStar_Options.print_effect_args ())
in (match (uu____1411) with
| true -> begin
(

let uu____1412 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1412))
end
| uu____1413 -> begin
(

let uu____1414 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1415 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1414 uu____1415)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  Prims.string = (fun s uu___204_1417 -> (match (uu___204_1417) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1419 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  FStar_Syntax_Syntax.binder  ->  Prims.string = (fun is_arrow b -> (

let uu____1423 = (

let uu____1424 = (FStar_Options.ugly ())
in (not (uu____1424)))
in (match (uu____1423) with
| true -> begin
(

let uu____1425 = (FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange)
in (match (uu____1425) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let d = (FStar_Parser_ToDocument.binder_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d))
end))
end
| uu____1429 -> begin
(

let uu____1430 = b
in (match (uu____1430) with
| (a, imp) -> begin
(

let uu____1433 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1433) with
| true -> begin
(

let uu____1434 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1434))
end
| uu____1435 -> begin
(

let uu____1436 = ((not (is_arrow)) && (

let uu____1437 = (FStar_Options.print_bound_var_types ())
in (not (uu____1437))))
in (match (uu____1436) with
| true -> begin
(

let uu____1438 = (nm_to_string a)
in (imp_to_string uu____1438 imp))
end
| uu____1439 -> begin
(

let uu____1440 = (

let uu____1441 = (nm_to_string a)
in (

let uu____1442 = (

let uu____1443 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1443))
in (Prims.strcat uu____1441 uu____1442)))
in (imp_to_string uu____1440 imp))
end))
end))
end))
end)))
and binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : FStar_Syntax_Syntax.binder  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs1 = (

let uu____1449 = (FStar_Options.print_implicits ())
in (match (uu____1449) with
| true -> begin
bs
end
| uu____1450 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(

let uu____1451 = (FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____1451 (FStar_String.concat sep)))
end
| uu____1455 -> begin
(

let uu____1456 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1456 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)  ->  Prims.string = (fun uu___205_1460 -> (match (uu___205_1460) with
| (a, imp) -> begin
(

let uu____1468 = (term_to_string a)
in (imp_to_string uu____1468 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____1471 = (FStar_Options.print_implicits ())
in (match (uu____1471) with
| true -> begin
args
end
| uu____1472 -> begin
(filter_imp args)
end))
in (

let uu____1475 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1475 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (

let uu____1483 = (

let uu____1484 = (FStar_Options.ugly ())
in (not (uu____1484)))
in (match (uu____1483) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_comp c)
in (

let d = (FStar_Parser_ToDocument.term_to_document e)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d)))
end
| uu____1487 -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1489) -> begin
(

let uu____1496 = (

let uu____1497 = (FStar_Syntax_Subst.compress t)
in uu____1497.FStar_Syntax_Syntax.n)
in (match (uu____1496) with
| FStar_Syntax_Syntax.Tm_type (uu____1500) when (

let uu____1501 = (FStar_Options.print_implicits ())
in (not (uu____1501))) -> begin
(term_to_string t)
end
| uu____1502 -> begin
(

let uu____1503 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____1503))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1505) -> begin
(

let uu____1512 = (

let uu____1513 = (FStar_Syntax_Subst.compress t)
in uu____1513.FStar_Syntax_Syntax.n)
in (match (uu____1512) with
| FStar_Syntax_Syntax.Tm_type (uu____1516) when (

let uu____1517 = (FStar_Options.print_implicits ())
in (not (uu____1517))) -> begin
(term_to_string t)
end
| uu____1518 -> begin
(

let uu____1519 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____1519))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____1522 = (FStar_Options.print_effect_args ())
in (match (uu____1522) with
| true -> begin
(

let uu____1523 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1524 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____1525 = (

let uu____1526 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1526 (FStar_String.concat ", ")))
in (

let uu____1538 = (

let uu____1539 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____1539 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1523 uu____1524 uu____1525 uu____1538)))))
end
| uu____1544 -> begin
(

let uu____1545 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___206_1547 -> (match (uu___206_1547) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1548 -> begin
false
end)))) && (

let uu____1549 = (FStar_Options.print_effect_args ())
in (not (uu____1549))))
in (match (uu____1545) with
| true -> begin
(

let uu____1550 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____1550))
end
| uu____1551 -> begin
(

let uu____1552 = (((

let uu____1553 = (FStar_Options.print_effect_args ())
in (not (uu____1553))) && (

let uu____1554 = (FStar_Options.print_implicits ())
in (not (uu____1554)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_ML_lid))
in (match (uu____1552) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____1555 -> begin
(

let uu____1556 = ((

let uu____1557 = (FStar_Options.print_effect_args ())
in (not (uu____1557))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___207_1559 -> (match (uu___207_1559) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1560 -> begin
false
end)))))
in (match (uu____1556) with
| true -> begin
(

let uu____1561 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____1561))
end
| uu____1562 -> begin
(

let uu____1563 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1564 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____1563 uu____1564)))
end))
end))
end))
end))
in (

let dec = (

let uu____1566 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___208_1570 -> (match (uu___208_1570) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____1575 = (

let uu____1576 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____1576))
in (uu____1575)::[])
end
| uu____1577 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1566 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____1580) -> begin
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1589 = (FStar_Options.print_universes ())
in (match (uu____1589) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1590 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun s -> (

let uu____1594 = (

let uu____1595 = (FStar_Options.ugly ())
in (not (uu____1595)))
in (match (uu____1594) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_tscheme s)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1598 -> begin
(

let uu____1599 = s
in (match (uu____1599) with
| (us, t) -> begin
(

let uu____1604 = (

let uu____1605 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____1605))
in (

let uu____1606 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____1604 uu____1606)))
end))
end)))


let eff_decl_to_string' : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free r q ed -> (

let uu____1621 = (

let uu____1622 = (FStar_Options.ugly ())
in (not (uu____1622)))
in (match (uu____1621) with
| true -> begin
(

let d = (FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed)
in (

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1)))
end
| uu____1625 -> begin
(

let actions_to_string = (fun actions -> (

let uu____1632 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (

let uu____1637 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____1638 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____1639 = (

let uu____1640 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____1640))
in (

let uu____1641 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1642 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1637 uu____1638 uu____1639 uu____1641 uu____1642)))))))))
in (FStar_All.pipe_right uu____1632 (FStar_String.concat ",\n\t"))))
in (

let uu____1644 = (

let uu____1646 = (

let uu____1648 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1649 = (

let uu____1651 = (

let uu____1652 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____1652))
in (

let uu____1653 = (

let uu____1655 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____1656 = (

let uu____1658 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____1659 = (

let uu____1661 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1662 = (

let uu____1664 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____1665 = (

let uu____1667 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____1668 = (

let uu____1670 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____1671 = (

let uu____1673 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____1674 = (

let uu____1676 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____1677 = (

let uu____1679 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____1680 = (

let uu____1682 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____1683 = (

let uu____1685 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____1686 = (

let uu____1688 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____1689 = (

let uu____1691 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____1692 = (

let uu____1694 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____1695 = (

let uu____1697 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____1698 = (

let uu____1700 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____1700)::[])
in (uu____1697)::uu____1698))
in (uu____1694)::uu____1695))
in (uu____1691)::uu____1692))
in (uu____1688)::uu____1689))
in (uu____1685)::uu____1686))
in (uu____1682)::uu____1683))
in (uu____1679)::uu____1680))
in (uu____1676)::uu____1677))
in (uu____1673)::uu____1674))
in (uu____1670)::uu____1671))
in (uu____1667)::uu____1668))
in (uu____1664)::uu____1665))
in (uu____1661)::uu____1662))
in (uu____1658)::uu____1659))
in (uu____1655)::uu____1656))
in (uu____1651)::uu____1653))
in (uu____1648)::uu____1649))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1701 -> begin
""
end))::uu____1646)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____1644)))
end)))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (eff_decl_to_string' for_free FStar_Range.dummyRange [] ed))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (

let uu____1711 = (

let uu____1712 = (FStar_Options.ugly ())
in (not (uu____1712)))
in (match (uu____1711) with
| true -> begin
(

let e = (FStar_Syntax_Resugar.resugar_sigelt x)
in (match (e) with
| FStar_Pervasives_Native.Some (d) -> begin
(

let d1 = (FStar_Parser_ToDocument.decl_to_document d)
in (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") d1))
end
| uu____1717 -> begin
""
end))
end
| uu____1719 -> begin
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
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs1, tps, k, uu____1726, uu____1727) -> begin
(

let uu____1732 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1733 = (binders_to_string " " tps)
in (

let uu____1734 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____1732 lid.FStar_Ident.str uu____1733 uu____1734))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs1, t, uu____1738, uu____1739, uu____1740) -> begin
(

let uu____1743 = (FStar_Options.print_universes ())
in (match (uu____1743) with
| true -> begin
(

let uu____1744 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1744) with
| (univs2, t1) -> begin
(

let uu____1749 = (univ_names_to_string univs2)
in (

let uu____1750 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____1749 lid.FStar_Ident.str uu____1750)))
end))
end
| uu____1751 -> begin
(

let uu____1752 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____1752))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) -> begin
(

let uu____1756 = (FStar_Syntax_Subst.open_univ_vars univs1 t)
in (match (uu____1756) with
| (univs2, t1) -> begin
(

let uu____1761 = (quals_to_string' x.FStar_Syntax_Syntax.sigquals)
in (

let uu____1762 = (

let uu____1763 = (FStar_Options.print_universes ())
in (match (uu____1763) with
| true -> begin
(

let uu____1764 = (univ_names_to_string univs2)
in (FStar_Util.format1 "<%s>" uu____1764))
end
| uu____1765 -> begin
""
end))
in (

let uu____1766 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____1761 lid.FStar_Ident.str uu____1762 uu____1766))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f) -> begin
(

let uu____1769 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1769))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1771, uu____1772) -> begin
(lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1778 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____1778))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1780) -> begin
(

let uu____1785 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____1785 (FStar_String.concat "\n")))
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
| (FStar_Pervasives_Native.Some (lift_wp), uu____1797) -> begin
lift_wp
end
| (uu____1801, FStar_Pervasives_Native.Some (lift)) -> begin
lift
end)
in (

let uu____1806 = (FStar_Syntax_Subst.open_univ_vars (FStar_Pervasives_Native.fst lift_wp) (FStar_Pervasives_Native.snd lift_wp))
in (match (uu____1806) with
| (us, t) -> begin
(

let uu____1813 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____1814 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____1815 = (univ_names_to_string us)
in (

let uu____1816 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1813 uu____1814 uu____1815 uu____1816)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) -> begin
(

let uu____1824 = (FStar_Options.print_universes ())
in (match (uu____1824) with
| true -> begin
(

let uu____1825 = (

let uu____1828 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs1 uu____1828))
in (match (uu____1825) with
| (univs2, t) -> begin
(

let uu____1839 = (

let uu____1847 = (

let uu____1848 = (FStar_Syntax_Subst.compress t)
in uu____1848.FStar_Syntax_Syntax.n)
in (match (uu____1847) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____1875 -> begin
(failwith "impossible")
end))
in (match (uu____1839) with
| (tps1, c1) -> begin
(

let uu____1895 = (sli l)
in (

let uu____1896 = (univ_names_to_string univs2)
in (

let uu____1897 = (binders_to_string " " tps1)
in (

let uu____1898 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____1895 uu____1896 uu____1897 uu____1898)))))
end))
end))
end
| uu____1899 -> begin
(

let uu____1900 = (sli l)
in (

let uu____1901 = (binders_to_string " " tps)
in (

let uu____1902 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____1900 uu____1901 uu____1902))))
end))
end)
end)))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____1909 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____1909 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1913, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1915; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1917; FStar_Syntax_Syntax.lbdef = uu____1918})::[]), uu____1919, uu____1920) -> begin
(

let uu____1936 = (lbname_to_string lb)
in (

let uu____1937 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____1936 uu____1937)))
end
| uu____1938 -> begin
(

let uu____1939 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____1939 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____1948 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____1949 = (

let uu____1950 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1950 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____1948 uu____1949))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___209_1955 -> (match (uu___209_1955) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____1958 = (FStar_Util.string_of_int i)
in (

let uu____1959 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____1958 uu____1959)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____1962 = (bv_to_string x)
in (

let uu____1963 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____1962 uu____1963)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____1970 = (bv_to_string x)
in (

let uu____1971 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____1970 uu____1971)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____1974 = (FStar_Util.string_of_int i)
in (

let uu____1975 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____1974 uu____1975)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____1978 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1978))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____1982 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____1982 (FStar_String.concat "; "))))


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

let uu____2032 = (f x)
in (FStar_Util.string_builder_append strb uu____2032));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2036 = (f x1)
in (FStar_Util.string_builder_append strb uu____2036));
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

let uu____2065 = (f x)
in (FStar_Util.string_builder_append strb uu____2065));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2069 = (f x1)
in (FStar_Util.string_builder_append strb uu____2069));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





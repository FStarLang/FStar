
open Prims

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


let infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Addition), ("+")))::(((FStar_Syntax_Const.op_Subtraction), ("-")))::(((FStar_Syntax_Const.op_Multiply), ("*")))::(((FStar_Syntax_Const.op_Division), ("/")))::(((FStar_Syntax_Const.op_Eq), ("=")))::(((FStar_Syntax_Const.op_ColonEq), (":=")))::(((FStar_Syntax_Const.op_notEq), ("<>")))::(((FStar_Syntax_Const.op_And), ("&&")))::(((FStar_Syntax_Const.op_Or), ("||")))::(((FStar_Syntax_Const.op_LTE), ("<=")))::(((FStar_Syntax_Const.op_GTE), (">=")))::(((FStar_Syntax_Const.op_LT), ("<")))::(((FStar_Syntax_Const.op_GT), (">")))::(((FStar_Syntax_Const.op_Modulus), ("mod")))::(((FStar_Syntax_Const.and_lid), ("/\\")))::(((FStar_Syntax_Const.or_lid), ("\\/")))::(((FStar_Syntax_Const.imp_lid), ("==>")))::(((FStar_Syntax_Const.iff_lid), ("<==>")))::(((FStar_Syntax_Const.precedes_lid), ("<<")))::(((FStar_Syntax_Const.eq2_lid), ("==")))::(((FStar_Syntax_Const.eq3_lid), ("===")))::[]


let unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.op_Negation), ("not")))::(((FStar_Syntax_Const.op_Minus), ("-")))::(((FStar_Syntax_Const.not_lid), ("~")))::[]


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


let is_infix_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e))


let is_unary_prim_op : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun e -> (is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e))


let quants : (FStar_Ident.lident * Prims.string) Prims.list = (((FStar_Syntax_Const.forall_lid), ("forall")))::(((FStar_Syntax_Const.exists_lid), ("exists")))::[]


type exp =
FStar_Syntax_Syntax.term


let is_b2t : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.b2t_lid)::[]) t))


let is_quant : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op (Prims.fst (FStar_List.split quants)) t))


let is_ite : FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t -> (is_prim_op ((FStar_Syntax_Const.ite_lid)::[]) t))


let is_lex_cons : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lexcons_lid)::[]) f))


let is_lex_top : exp  ->  Prims.bool = (fun f -> (is_prim_op ((FStar_Syntax_Const.lextop_lid)::[]) f))


let is_inr = (fun uu___178_173 -> (match (uu___178_173) with
| FStar_Util.Inl (uu____176) -> begin
false
end
| FStar_Util.Inr (uu____177) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___179_208 -> (match (uu___179_208) with
| (uu____212, Some (FStar_Syntax_Syntax.Implicit (uu____213))) -> begin
false
end
| uu____215 -> begin
true
end)))))


let rec reconstruct_lex : exp  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax Prims.list Prims.option = (fun e -> (

let uu____226 = (

let uu____227 = (FStar_Syntax_Subst.compress e)
in uu____227.FStar_Syntax_Syntax.n)
in (match (uu____226) with
| FStar_Syntax_Syntax.Tm_app (f, args) -> begin
(

let args1 = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args1)
in (

let uu____273 = ((is_lex_cons f) && ((FStar_List.length exps) = (Prims.parse_int "2")))
in (match (uu____273) with
| true -> begin
(

let uu____282 = (

let uu____287 = (FStar_List.nth exps (Prims.parse_int "1"))
in (reconstruct_lex uu____287))
in (match (uu____282) with
| Some (xs) -> begin
(

let uu____301 = (

let uu____305 = (FStar_List.nth exps (Prims.parse_int "0"))
in (uu____305)::xs)
in Some (uu____301))
end
| None -> begin
None
end))
end
| uu____321 -> begin
None
end))))
end
| uu____325 -> begin
(

let uu____326 = (is_lex_top e)
in (match (uu____326) with
| true -> begin
Some ([])
end
| uu____336 -> begin
None
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

let uu____376 = (find (fun p -> (FStar_Ident.lid_equals x (Prims.fst p))) xs)
in (Prims.snd uu____376)))


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


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___180_448 -> (match (uu___180_448) with
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
| None -> begin
"Tm_delayed"
end
| Some (uu____613) -> begin
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


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n1 u -> (

let uu____645 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____645) with
| FStar_Syntax_Syntax.U_zero -> begin
((n1), (None))
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(int_of_univ (n1 + (Prims.parse_int "1")) u1)
end
| uu____651 -> begin
((n1), (Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____656 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____656) with
| FStar_Syntax_Syntax.U_unif (u1) -> begin
(uvar_to_string u1)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____663 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____663))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(

let uu____665 = (int_of_univ (Prims.parse_int "1") u1)
in (match (uu____665) with
| (n1, None) -> begin
(FStar_Util.string_of_int n1)
end
| (n1, Some (u2)) -> begin
(

let uu____674 = (univ_to_string u2)
in (

let uu____675 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 "(%s + %s)" uu____674 uu____675)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____678 = (

let uu____679 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____679 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____678))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____687 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____687 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____695 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____695 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___181_701 -> (match (uu___181_701) with
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

let uu____703 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____703))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____706 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____706 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____713 = (

let uu____714 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____714))
in (

let uu____716 = (

let uu____717 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____717 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____713 uu____716)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____728 = (

let uu____729 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____729))
in (

let uu____731 = (

let uu____732 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____732 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____728 uu____731)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____738 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____738))
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
| uu____745 -> begin
(

let uu____747 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____747 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____757 -> begin
(

let uu____759 = (quals_to_string quals)
in (Prims.strcat uu____759 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x1 = (FStar_Syntax_Subst.compress x)
in (

let x2 = (

let uu____815 = (FStar_Options.print_implicits ())
in (match (uu____815) with
| true -> begin
x1
end
| uu____816 -> begin
(FStar_Syntax_Util.unmeta x1)
end))
in (match (x2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____817) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____838, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____865 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____881 = (FStar_All.pipe_right args (FStar_List.map (fun uu____889 -> (match (uu____889) with
| (t1, uu____893) -> begin
(term_to_string t1)
end))))
in (FStar_All.pipe_right uu____881 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____865 (FStar_String.concat "\\/")))
in (

let uu____896 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____896)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____908 = (tag_of_term t)
in (

let uu____909 = (sli m)
in (

let uu____910 = (term_to_string t')
in (

let uu____911 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____908 uu____909 uu____910 uu____911)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____924 = (tag_of_term t)
in (

let uu____925 = (term_to_string t')
in (

let uu____926 = (sli m0)
in (

let uu____927 = (sli m1)
in (

let uu____928 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____924 uu____925 uu____926 uu____927 uu____928))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____937 = (FStar_Range.string_of_range r)
in (

let uu____938 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____937 uu____938)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____940) -> begin
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
| FStar_Syntax_Syntax.Tm_uvar (u, uu____949) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____967 = (FStar_Options.print_universes ())
in (match (uu____967) with
| true -> begin
(

let uu____968 = (univ_to_string u)
in (FStar_Util.format1 "Type u#(%s)" uu____968))
end
| uu____969 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____982 = (binders_to_string " -> " bs)
in (

let uu____983 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____982 uu____983)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1018 = (binders_to_string " " bs)
in (

let uu____1019 = (term_to_string t2)
in (

let uu____1020 = (

let uu____1021 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string uu____1021))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1018 uu____1019 uu____1020))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1034 = (binders_to_string " " bs)
in (

let uu____1035 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" uu____1034 uu____1035 l.FStar_Ident.str)))
end
| uu____1036 -> begin
(

let uu____1043 = (binders_to_string " " bs)
in (

let uu____1044 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1043 uu____1044)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1051 = (bv_to_string xt)
in (

let uu____1052 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1055 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1051 uu____1052 uu____1055))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1074 = (term_to_string t)
in (

let uu____1075 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1074 uu____1075)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1088 = (lbs_to_string [] lbs)
in (

let uu____1089 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1088 uu____1089)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) -> begin
(

let annot1 = (match (annot) with
| FStar_Util.Inl (t) -> begin
(

let uu____1137 = (

let uu____1138 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1138 (FStar_Util.dflt "default")))
in (

let uu____1141 = (term_to_string t)
in (FStar_Util.format2 "[%s] %s" uu____1137 uu____1141)))
end
| FStar_Util.Inr (c) -> begin
(comp_to_string c)
end)
in (

let topt1 = (match (topt) with
| None -> begin
""
end
| Some (t) -> begin
(

let uu____1157 = (term_to_string t)
in (FStar_Util.format1 "by %s" uu____1157))
end)
in (

let uu____1158 = (term_to_string e)
in (FStar_Util.format3 "(%s <: %s %s)" uu____1158 annot1 topt1))))
end
| FStar_Syntax_Syntax.Tm_match (head1, branches) -> begin
(

let uu____1187 = (term_to_string head1)
in (

let uu____1188 = (

let uu____1189 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1207 -> (match (uu____1207) with
| (p, wopt, e) -> begin
(

let uu____1217 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1218 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(

let uu____1220 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1220))
end)
in (

let uu____1221 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1217 uu____1218 uu____1221))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1189))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1187 uu____1188)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1228 = (FStar_Options.print_universes ())
in (match (uu____1228) with
| true -> begin
(

let uu____1229 = (term_to_string t)
in (

let uu____1230 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1229 uu____1230)))
end
| uu____1231 -> begin
(term_to_string t)
end))
end
| uu____1232 -> begin
(tag_of_term x2)
end))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1246 = (fv_to_string l)
in (

let uu____1247 = (

let uu____1248 = (FStar_List.map (fun uu____1252 -> (match (uu____1252) with
| (x1, b) -> begin
(

let p = (pat_to_string x1)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1258 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1248 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1246 uu____1247)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1261) -> begin
(

let uu____1266 = (FStar_Options.print_bound_var_types ())
in (match (uu____1266) with
| true -> begin
(

let uu____1267 = (bv_to_string x1)
in (

let uu____1268 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1267 uu____1268)))
end
| uu____1269 -> begin
(

let uu____1270 = (bv_to_string x1)
in (FStar_Util.format1 ".%s" uu____1270))
end))
end
| FStar_Syntax_Syntax.Pat_var (x1) -> begin
(

let uu____1272 = (FStar_Options.print_bound_var_types ())
in (match (uu____1272) with
| true -> begin
(

let uu____1273 = (bv_to_string x1)
in (

let uu____1274 = (term_to_string x1.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1273 uu____1274)))
end
| uu____1275 -> begin
(bv_to_string x1)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x1) -> begin
(

let uu____1278 = (FStar_Options.print_real_names ())
in (match (uu____1278) with
| true -> begin
(

let uu____1279 = (bv_to_string x1)
in (Prims.strcat "Pat_wild " uu____1279))
end
| uu____1280 -> begin
"_"
end))
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let uu____1285 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " uu____1285))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs1 = (

let uu____1297 = (FStar_Options.print_universes ())
in (match (uu____1297) with
| true -> begin
(

let uu____1301 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____1307 = (

let uu____1310 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1310))
in (match (uu____1307) with
| (us, td) -> begin
(

let uu____1313 = (

let uu____1320 = (

let uu____1321 = (FStar_Syntax_Subst.compress td)
in uu____1321.FStar_Syntax_Syntax.n)
in (match (uu____1320) with
| FStar_Syntax_Syntax.Tm_app (uu____1330, ((t, uu____1332))::((d, uu____1334))::[]) -> begin
((t), (d))
end
| uu____1368 -> begin
(failwith "Impossibe")
end))
in (match (uu____1313) with
| (t, d) -> begin
(

let uu___188_1385 = lb
in {FStar_Syntax_Syntax.lbname = uu___188_1385.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___188_1385.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (uu____1301)))
end
| uu____1388 -> begin
lbs
end))
in (

let uu____1389 = (quals_to_string' quals)
in (

let uu____1390 = (

let uu____1391 = (FStar_All.pipe_right (Prims.snd lbs1) (FStar_List.map (fun lb -> (

let uu____1397 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1398 = (

let uu____1399 = (FStar_Options.print_universes ())
in (match (uu____1399) with
| true -> begin
(

let uu____1400 = (

let uu____1401 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1401 ">"))
in (Prims.strcat "<" uu____1400))
end
| uu____1402 -> begin
""
end))
in (

let uu____1403 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1404 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1397 uu____1398 uu____1403 uu____1404))))))))
in (FStar_Util.concat_l "\n and " uu____1391))
in (FStar_Util.format3 "%slet %s %s" uu____1389 (match ((Prims.fst lbs1)) with
| true -> begin
"rec"
end
| uu____1408 -> begin
""
end) uu____1390)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1410 = (FStar_Options.print_effect_args ())
in (match (uu____1410) with
| true -> begin
(

let uu____1411 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1411))
end
| uu____1412 -> begin
(

let uu____1413 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1414 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1413 uu____1414)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___182_1416 -> (match (uu___182_1416) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1418 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

let uu____1424 = b
in (match (uu____1424) with
| (a, imp) -> begin
(

let uu____1429 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1429) with
| true -> begin
(

let uu____1430 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1430))
end
| uu____1431 -> begin
(

let uu____1432 = ((not (is_arrow)) && (

let uu____1433 = (FStar_Options.print_bound_var_types ())
in (not (uu____1433))))
in (match (uu____1432) with
| true -> begin
(

let uu____1434 = (nm_to_string a)
in (imp_to_string uu____1434 imp))
end
| uu____1435 -> begin
(

let uu____1436 = (

let uu____1437 = (nm_to_string a)
in (

let uu____1438 = (

let uu____1439 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1439))
in (Prims.strcat uu____1437 uu____1438)))
in (imp_to_string uu____1436 imp))
end))
end))
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' true b))
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
| uu____1457 -> begin
(

let uu____1458 = (FStar_All.pipe_right bs1 (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1458 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___183_1464 -> (match (uu___183_1464) with
| (a, imp) -> begin
(

let uu____1472 = (term_to_string a)
in (imp_to_string uu____1472 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args1 = (

let uu____1475 = (FStar_Options.print_implicits ())
in (match (uu____1475) with
| true -> begin
args
end
| uu____1476 -> begin
(filter_imp args)
end))
in (

let uu____1479 = (FStar_All.pipe_right args1 (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1479 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1488) -> begin
(

let uu____1495 = (

let uu____1496 = (FStar_Syntax_Subst.compress t)
in uu____1496.FStar_Syntax_Syntax.n)
in (match (uu____1495) with
| FStar_Syntax_Syntax.Tm_type (uu____1499) when (

let uu____1500 = (FStar_Options.print_implicits ())
in (not (uu____1500))) -> begin
(term_to_string t)
end
| uu____1501 -> begin
(

let uu____1502 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____1502))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1504) -> begin
(

let uu____1511 = (

let uu____1512 = (FStar_Syntax_Subst.compress t)
in uu____1512.FStar_Syntax_Syntax.n)
in (match (uu____1511) with
| FStar_Syntax_Syntax.Tm_type (uu____1515) when (

let uu____1516 = (FStar_Options.print_implicits ())
in (not (uu____1516))) -> begin
(term_to_string t)
end
| uu____1517 -> begin
(

let uu____1518 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____1518))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let basic = (

let uu____1521 = (FStar_Options.print_effect_args ())
in (match (uu____1521) with
| true -> begin
(

let uu____1522 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1523 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (

let uu____1524 = (

let uu____1525 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1525 (FStar_String.concat ", ")))
in (

let uu____1537 = (

let uu____1538 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____1538 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1522 uu____1523 uu____1524 uu____1537)))))
end
| uu____1543 -> begin
(

let uu____1544 = ((FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___184_1546 -> (match (uu___184_1546) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1547 -> begin
false
end)))) && (

let uu____1548 = (FStar_Options.print_effect_args ())
in (not (uu____1548))))
in (match (uu____1544) with
| true -> begin
(

let uu____1549 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____1549))
end
| uu____1550 -> begin
(

let uu____1551 = (((

let uu____1552 = (FStar_Options.print_effect_args ())
in (not (uu____1552))) && (

let uu____1553 = (FStar_Options.print_implicits ())
in (not (uu____1553)))) && (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid))
in (match (uu____1551) with
| true -> begin
(term_to_string c1.FStar_Syntax_Syntax.result_typ)
end
| uu____1554 -> begin
(

let uu____1555 = ((

let uu____1556 = (FStar_Options.print_effect_args ())
in (not (uu____1556))) && (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___185_1558 -> (match (uu___185_1558) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1559 -> begin
false
end)))))
in (match (uu____1555) with
| true -> begin
(

let uu____1560 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____1560))
end
| uu____1561 -> begin
(

let uu____1562 = (sli c1.FStar_Syntax_Syntax.effect_name)
in (

let uu____1563 = (term_to_string c1.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____1562 uu____1563)))
end))
end))
end))
end))
in (

let dec = (

let uu____1565 = (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___186_1569 -> (match (uu___186_1569) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____1574 = (

let uu____1575 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____1575))
in (uu____1574)::[])
end
| uu____1576 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1565 (FStar_String.concat " ")))
in (FStar_Util.format2 "%s%s" basic dec)))
end))
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
| FStar_Syntax_Syntax.DECREASES (uu____1579) -> begin
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1588 = (FStar_Options.print_universes ())
in (match (uu____1588) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1589 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun uu____1592 -> (match (uu____1592) with
| (us, t) -> begin
(

let uu____1597 = (

let uu____1598 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____1598))
in (

let uu____1599 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____1597 uu____1599)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (

let uu____1612 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (

let uu____1617 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____1618 = (binders_to_string " " a.FStar_Syntax_Syntax.action_params)
in (

let uu____1619 = (

let uu____1620 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____1620))
in (

let uu____1621 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1622 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format5 "%s%s %s : %s = %s" uu____1617 uu____1618 uu____1619 uu____1621 uu____1622)))))))))
in (FStar_All.pipe_right uu____1612 (FStar_String.concat ",\n\t"))))
in (

let uu____1624 = (

let uu____1626 = (

let uu____1628 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1629 = (

let uu____1631 = (

let uu____1632 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____1632))
in (

let uu____1633 = (

let uu____1635 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____1636 = (

let uu____1638 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____1639 = (

let uu____1641 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1642 = (

let uu____1644 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____1645 = (

let uu____1647 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____1648 = (

let uu____1650 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____1651 = (

let uu____1653 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____1654 = (

let uu____1656 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____1657 = (

let uu____1659 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____1660 = (

let uu____1662 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____1663 = (

let uu____1665 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____1666 = (

let uu____1668 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____1669 = (

let uu____1671 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____1672 = (

let uu____1674 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____1675 = (

let uu____1677 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____1678 = (

let uu____1680 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____1680)::[])
in (uu____1677)::uu____1678))
in (uu____1674)::uu____1675))
in (uu____1671)::uu____1672))
in (uu____1668)::uu____1669))
in (uu____1665)::uu____1666))
in (uu____1662)::uu____1663))
in (uu____1659)::uu____1660))
in (uu____1656)::uu____1657))
in (uu____1653)::uu____1654))
in (uu____1650)::uu____1651))
in (uu____1647)::uu____1648))
in (uu____1644)::uu____1645))
in (uu____1641)::uu____1642))
in (uu____1638)::uu____1639))
in (uu____1635)::uu____1636))
in (uu____1631)::uu____1633))
in (uu____1628)::uu____1629))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1681 -> begin
""
end))::uu____1626)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____1624))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff) -> begin
"#light \"off\""
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None)) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s))) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s)) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, uu____1691, uu____1692, quals) -> begin
(

let uu____1700 = (quals_to_string' quals)
in (

let uu____1701 = (binders_to_string " " tps)
in (

let uu____1702 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____1700 lid.FStar_Ident.str uu____1701 uu____1702))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, uu____1706, uu____1707, uu____1708, uu____1709) -> begin
(

let uu____1714 = (FStar_Options.print_universes ())
in (match (uu____1714) with
| true -> begin
(

let uu____1715 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1715) with
| (univs1, t1) -> begin
(

let uu____1720 = (univ_names_to_string univs1)
in (

let uu____1721 = (term_to_string t1)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____1720 lid.FStar_Ident.str uu____1721)))
end))
end
| uu____1722 -> begin
(

let uu____1723 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____1723))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals) -> begin
(

let uu____1730 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1730) with
| (univs1, t1) -> begin
(

let uu____1735 = (quals_to_string' quals)
in (

let uu____1736 = (

let uu____1737 = (FStar_Options.print_universes ())
in (match (uu____1737) with
| true -> begin
(

let uu____1738 = (univ_names_to_string univs1)
in (FStar_Util.format1 "<%s>" uu____1738))
end
| uu____1739 -> begin
""
end))
in (

let uu____1740 = (term_to_string t1)
in (FStar_Util.format4 "%sval %s %s : %s" uu____1735 lid.FStar_Ident.str uu____1736 uu____1740))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, uu____1743) -> begin
(

let uu____1746 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1746))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1748, qs, uu____1750) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e) -> begin
(

let uu____1758 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____1758))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1760, uu____1761) -> begin
(

let uu____1768 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____1768 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
| (Some (lift_wp), uu____1780) -> begin
lift_wp
end
| (uu____1784, Some (lift)) -> begin
lift
end)
in (

let uu____1789 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (uu____1789) with
| (us, t) -> begin
(

let uu____1796 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____1797 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____1798 = (univ_names_to_string us)
in (

let uu____1799 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1796 uu____1797 uu____1798 uu____1799)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, uu____1804, flags) -> begin
(

let uu____1810 = (FStar_Options.print_universes ())
in (match (uu____1810) with
| true -> begin
(

let uu____1811 = (

let uu____1814 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs uu____1814))
in (match (uu____1811) with
| (univs1, t) -> begin
(

let uu____1825 = (

let uu____1833 = (

let uu____1834 = (FStar_Syntax_Subst.compress t)
in uu____1834.FStar_Syntax_Syntax.n)
in (match (uu____1833) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> begin
((bs), (c1))
end
| uu____1861 -> begin
(failwith "impossible")
end))
in (match (uu____1825) with
| (tps1, c1) -> begin
(

let uu____1881 = (sli l)
in (

let uu____1882 = (univ_names_to_string univs1)
in (

let uu____1883 = (binders_to_string " " tps1)
in (

let uu____1884 = (comp_to_string c1)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____1881 uu____1882 uu____1883 uu____1884)))))
end))
end))
end
| uu____1885 -> begin
(

let uu____1886 = (sli l)
in (

let uu____1887 = (binders_to_string " " tps)
in (

let uu____1888 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____1886 uu____1887 uu____1888))))
end))
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____1895 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____1895 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____1899, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1901; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1903; FStar_Syntax_Syntax.lbdef = uu____1904})::[]), uu____1905, uu____1906, uu____1907) -> begin
(

let uu____1925 = (lbname_to_string lb)
in (

let uu____1926 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____1925 uu____1926)))
end
| uu____1927 -> begin
(

let uu____1928 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____1928 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____1937 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____1938 = (

let uu____1939 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1939 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____1937 uu____1938))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___187_1944 -> (match (uu___187_1944) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____1947 = (FStar_Util.string_of_int i)
in (

let uu____1948 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____1947 uu____1948)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____1951 = (bv_to_string x)
in (

let uu____1952 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____1951 uu____1952)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____1959 = (bv_to_string x)
in (

let uu____1960 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____1959 uu____1960)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____1963 = (FStar_Util.string_of_int i)
in (

let uu____1964 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____1963 uu____1964)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____1967 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1967))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____1971 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____1971 (FStar_String.concat "; "))))


let abs_ascription_to_string : (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either Prims.option  ->  Prims.string = (fun ascription -> (

let strb = (FStar_Util.new_string_builder ())
in ((match (ascription) with
| None -> begin
(FStar_Util.string_builder_append strb "None")
end
| Some (FStar_Util.Inl (lc)) -> begin
((FStar_Util.string_builder_append strb "Some Inr ");
(FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name));
)
end
| Some (FStar_Util.Inr (lid)) -> begin
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

let uu____2021 = (f x)
in (FStar_Util.string_builder_append strb uu____2021));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2025 = (f x1)
in (FStar_Util.string_builder_append strb uu____2025));
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

let uu____2054 = (f x)
in (FStar_Util.string_builder_append strb uu____2054));
(FStar_List.iter (fun x1 -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2058 = (f x1)
in (FStar_Util.string_builder_append strb uu____2058));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





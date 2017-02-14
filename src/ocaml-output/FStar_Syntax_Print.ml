
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


let is_inr = (fun uu___180_173 -> (match (uu___180_173) with
| FStar_Util.Inl (uu____176) -> begin
false
end
| FStar_Util.Inr (uu____177) -> begin
true
end))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___181_208 -> (match (uu___181_208) with
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

let args = (filter_imp args)
in (

let exps = (FStar_List.map Prims.fst args)
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
| (hd)::tl -> begin
(

let uu____362 = (f hd)
in (match (uu____362) with
| true -> begin
hd
end
| uu____363 -> begin
(find f tl)
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
| FStar_Const.Const_float (x) -> begin
(FStar_Util.string_of_float x)
end
| FStar_Const.Const_string (bytes, uu____427) -> begin
(FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes))
end
| FStar_Const.Const_bytearray (uu____430) -> begin
"<bytearray>"
end
| FStar_Const.Const_int (x, uu____435) -> begin
x
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


let lbname_to_string : FStar_Syntax_Syntax.lbname  ->  Prims.string = (fun uu___182_448 -> (match (uu___182_448) with
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
| FStar_Syntax_Syntax.Tm_let (uu____542) -> begin
"Tm_let"
end
| FStar_Syntax_Syntax.Tm_uvar (uu____550) -> begin
"Tm_uvar"
end
| FStar_Syntax_Syntax.Tm_delayed (uu____559, m) -> begin
(

let uu____597 = (FStar_ST.read m)
in (match (uu____597) with
| None -> begin
"Tm_delayed"
end
| Some (uu____608) -> begin
"Tm_delayed-resolved"
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____613) -> begin
"Tm_meta"
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
"Tm_unknown"
end))


let uvar_to_string = (fun u -> (

let uu____627 = (FStar_Options.hide_uvar_nums ())
in (match (uu____627) with
| true -> begin
"?"
end
| uu____628 -> begin
(

let uu____629 = (

let uu____630 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____630 FStar_Util.string_of_int))
in (Prims.strcat "?" uu____629))
end)))


let rec int_of_univ : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe Prims.option) = (fun n u -> (

let uu____640 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____640) with
| FStar_Syntax_Syntax.U_zero -> begin
((n), (None))
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(int_of_univ (n + (Prims.parse_int "1")) u)
end
| uu____646 -> begin
((n), (Some (u)))
end)))


let rec univ_to_string : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (

let uu____651 = (FStar_Syntax_Subst.compress_univ u)
in (match (uu____651) with
| FStar_Syntax_Syntax.U_unif (u) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
x.FStar_Ident.idText
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let uu____658 = (FStar_Util.string_of_int x)
in (Prims.strcat "@" uu____658))
end
| FStar_Syntax_Syntax.U_zero -> begin
"0"
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(

let uu____660 = (int_of_univ (Prims.parse_int "1") u)
in (match (uu____660) with
| (n, None) -> begin
(FStar_Util.string_of_int n)
end
| (n, Some (u)) -> begin
(

let uu____669 = (univ_to_string u)
in (

let uu____670 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 "(%s + %s)" uu____669 uu____670)))
end))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(

let uu____673 = (

let uu____674 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____674 (FStar_String.concat ", ")))
in (FStar_Util.format1 "(max %s)" uu____673))
end
| FStar_Syntax_Syntax.U_unknown -> begin
"unknown"
end)))


let univs_to_string : FStar_Syntax_Syntax.universe Prims.list  ->  Prims.string = (fun us -> (

let uu____682 = (FStar_List.map univ_to_string us)
in (FStar_All.pipe_right uu____682 (FStar_String.concat ", "))))


let univ_names_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun us -> (

let uu____690 = (FStar_List.map (fun x -> x.FStar_Ident.idText) us)
in (FStar_All.pipe_right uu____690 (FStar_String.concat ", "))))


let qual_to_string : FStar_Syntax_Syntax.qualifier  ->  Prims.string = (fun uu___183_696 -> (match (uu___183_696) with
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

let uu____698 = (lid_to_string l)
in (FStar_Util.format1 "(Discriminator %s)" uu____698))
end
| FStar_Syntax_Syntax.Projector (l, x) -> begin
(

let uu____701 = (lid_to_string l)
in (FStar_Util.format2 "(Projector %s %s)" uu____701 x.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.RecordType (ns, fns) -> begin
(

let uu____708 = (

let uu____709 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____709))
in (

let uu____711 = (

let uu____712 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____712 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordType %s %s)" uu____708 uu____711)))
end
| FStar_Syntax_Syntax.RecordConstructor (ns, fns) -> begin
(

let uu____723 = (

let uu____724 = (FStar_Ident.path_of_ns ns)
in (FStar_Ident.text_of_path uu____724))
in (

let uu____726 = (

let uu____727 = (FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id))
in (FStar_All.pipe_right uu____727 (FStar_String.concat ", ")))
in (FStar_Util.format2 "(RecordConstructor %s %s)" uu____723 uu____726)))
end
| FStar_Syntax_Syntax.Action (eff_lid) -> begin
(

let uu____733 = (lid_to_string eff_lid)
in (FStar_Util.format1 "(Action %s)" uu____733))
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
| uu____740 -> begin
(

let uu____742 = (FStar_All.pipe_right quals (FStar_List.map qual_to_string))
in (FStar_All.pipe_right uu____742 (FStar_String.concat " ")))
end))


let quals_to_string' : FStar_Syntax_Syntax.qualifier Prims.list  ->  Prims.string = (fun quals -> (match (quals) with
| [] -> begin
""
end
| uu____752 -> begin
(

let uu____754 = (quals_to_string quals)
in (Prims.strcat uu____754 " "))
end))


let rec term_to_string : FStar_Syntax_Syntax.term  ->  Prims.string = (fun x -> (

let x = (FStar_Syntax_Subst.compress x)
in (

let x = (

let uu____810 = (FStar_Options.print_implicits ())
in (match (uu____810) with
| true -> begin
x
end
| uu____811 -> begin
(FStar_Syntax_Util.unmeta x)
end))
in (match (x.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____812) -> begin
(failwith "impossible")
end
| FStar_Syntax_Syntax.Tm_app (uu____833, []) -> begin
(failwith "Empty args!")
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(

let pats = (

let uu____860 = (FStar_All.pipe_right ps (FStar_List.map (fun args -> (

let uu____876 = (FStar_All.pipe_right args (FStar_List.map (fun uu____884 -> (match (uu____884) with
| (t, uu____888) -> begin
(term_to_string t)
end))))
in (FStar_All.pipe_right uu____876 (FStar_String.concat "; "))))))
in (FStar_All.pipe_right uu____860 (FStar_String.concat "\\/")))
in (

let uu____891 = (term_to_string t)
in (FStar_Util.format2 "{:pattern %s} %s" pats uu____891)))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) -> begin
(

let uu____903 = (tag_of_term t)
in (

let uu____904 = (sli m)
in (

let uu____905 = (term_to_string t')
in (

let uu____906 = (term_to_string t)
in (FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____903 uu____904 uu____905 uu____906)))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) -> begin
(

let uu____919 = (tag_of_term t)
in (

let uu____920 = (term_to_string t')
in (

let uu____921 = (sli m0)
in (

let uu____922 = (sli m1)
in (

let uu____923 = (term_to_string t)
in (FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____919 uu____920 uu____921 uu____922 uu____923))))))
end
| FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____932 = (FStar_Range.string_of_range r)
in (

let uu____933 = (term_to_string t)
in (FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____932 uu____933)))
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____935) -> begin
(term_to_string t)
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(db_to_string x)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(nm_to_string x)
end
| FStar_Syntax_Syntax.Tm_fvar (f) -> begin
(fv_to_string f)
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____944) -> begin
(uvar_to_string u)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____962 = (FStar_Options.print_universes ())
in (match (uu____962) with
| true -> begin
(

let uu____963 = (univ_to_string u)
in (FStar_Util.format1 "Type(%s)" uu____963))
end
| uu____964 -> begin
"Type"
end))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____977 = (binders_to_string " -> " bs)
in (

let uu____978 = (comp_to_string c)
in (FStar_Util.format2 "(%s -> %s)" uu____977 uu____978)))
end
| FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) -> begin
(match (lc) with
| Some (FStar_Util.Inl (l)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1013 = (binders_to_string " " bs)
in (

let uu____1014 = (term_to_string t2)
in (

let uu____1015 = (

let uu____1016 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_All.pipe_left comp_to_string uu____1016))
in (FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1013 uu____1014 uu____1015))))
end
| Some (FStar_Util.Inr (l, flags)) when (FStar_Options.print_implicits ()) -> begin
(

let uu____1029 = (binders_to_string " " bs)
in (

let uu____1030 = (term_to_string t2)
in (FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" uu____1029 uu____1030 l.FStar_Ident.str)))
end
| uu____1031 -> begin
(

let uu____1038 = (binders_to_string " " bs)
in (

let uu____1039 = (term_to_string t2)
in (FStar_Util.format2 "(fun %s -> %s)" uu____1038 uu____1039)))
end)
end
| FStar_Syntax_Syntax.Tm_refine (xt, f) -> begin
(

let uu____1046 = (bv_to_string xt)
in (

let uu____1047 = (FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string)
in (

let uu____1050 = (FStar_All.pipe_right f formula_to_string)
in (FStar_Util.format3 "(%s:%s{%s})" uu____1046 uu____1047 uu____1050))))
end
| FStar_Syntax_Syntax.Tm_app (t, args) -> begin
(

let uu____1069 = (term_to_string t)
in (

let uu____1070 = (args_to_string args)
in (FStar_Util.format2 "(%s %s)" uu____1069 uu____1070)))
end
| FStar_Syntax_Syntax.Tm_let (lbs, e) -> begin
(

let uu____1083 = (lbs_to_string [] lbs)
in (

let uu____1084 = (term_to_string e)
in (FStar_Util.format2 "%s\nin\n%s" uu____1083 uu____1084)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inl (t), eff_name) -> begin
(

let uu____1106 = (term_to_string e)
in (

let uu____1107 = (

let uu____1108 = (FStar_Util.map_opt eff_name FStar_Ident.text_of_lid)
in (FStar_All.pipe_right uu____1108 (FStar_Util.dflt "default")))
in (

let uu____1111 = (term_to_string t)
in (FStar_Util.format3 "(%s <: [%s] %s)" uu____1106 uu____1107 uu____1111))))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, FStar_Util.Inr (c), uu____1114) -> begin
(

let uu____1133 = (term_to_string e)
in (

let uu____1134 = (comp_to_string c)
in (FStar_Util.format2 "(%s <: %s)" uu____1133 uu____1134)))
end
| FStar_Syntax_Syntax.Tm_match (head, branches) -> begin
(

let uu____1163 = (term_to_string head)
in (

let uu____1164 = (

let uu____1165 = (FStar_All.pipe_right branches (FStar_List.map (fun uu____1183 -> (match (uu____1183) with
| (p, wopt, e) -> begin
(

let uu____1193 = (FStar_All.pipe_right p pat_to_string)
in (

let uu____1194 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(

let uu____1196 = (FStar_All.pipe_right w term_to_string)
in (FStar_Util.format1 "when %s" uu____1196))
end)
in (

let uu____1197 = (FStar_All.pipe_right e term_to_string)
in (FStar_Util.format3 "%s %s -> %s" uu____1193 uu____1194 uu____1197))))
end))))
in (FStar_Util.concat_l "\n\t|" uu____1165))
in (FStar_Util.format2 "(match %s with\n\t| %s)" uu____1163 uu____1164)))
end
| FStar_Syntax_Syntax.Tm_uinst (t, us) -> begin
(

let uu____1204 = (FStar_Options.print_universes ())
in (match (uu____1204) with
| true -> begin
(

let uu____1205 = (term_to_string t)
in (

let uu____1206 = (univs_to_string us)
in (FStar_Util.format2 "%s<%s>" uu____1205 uu____1206)))
end
| uu____1207 -> begin
(term_to_string t)
end))
end
| uu____1208 -> begin
(tag_of_term x)
end))))
and pat_to_string : FStar_Syntax_Syntax.pat  ->  Prims.string = (fun x -> (match (x.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (l, pats) -> begin
(

let uu____1222 = (fv_to_string l)
in (

let uu____1223 = (

let uu____1224 = (FStar_List.map (fun uu____1228 -> (match (uu____1228) with
| (x, b) -> begin
(

let p = (pat_to_string x)
in (match (b) with
| true -> begin
(Prims.strcat "#" p)
end
| uu____1234 -> begin
p
end))
end)) pats)
in (FStar_All.pipe_right uu____1224 (FStar_String.concat " ")))
in (FStar_Util.format2 "(%s %s)" uu____1222 uu____1223)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____1237) -> begin
(

let uu____1242 = (FStar_Options.print_bound_var_types ())
in (match (uu____1242) with
| true -> begin
(

let uu____1243 = (bv_to_string x)
in (

let uu____1244 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 ".%s:%s" uu____1243 uu____1244)))
end
| uu____1245 -> begin
(

let uu____1246 = (bv_to_string x)
in (FStar_Util.format1 ".%s" uu____1246))
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu____1248 = (FStar_Options.print_bound_var_types ())
in (match (uu____1248) with
| true -> begin
(

let uu____1249 = (bv_to_string x)
in (

let uu____1250 = (term_to_string x.FStar_Syntax_Syntax.sort)
in (FStar_Util.format2 "%s:%s" uu____1249 uu____1250)))
end
| uu____1251 -> begin
(bv_to_string x)
end))
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu____1254 = (FStar_Options.print_real_names ())
in (match (uu____1254) with
| true -> begin
(

let uu____1255 = (bv_to_string x)
in (Prims.strcat "Pat_wild " uu____1255))
end
| uu____1256 -> begin
"_"
end))
end
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(

let uu____1261 = (FStar_List.map pat_to_string ps)
in (FStar_Util.concat_l " | " uu____1261))
end))
and lbs_to_string : FStar_Syntax_Syntax.qualifier Prims.list  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  Prims.string = (fun quals lbs -> (

let lbs = (

let uu____1273 = (FStar_Options.print_universes ())
in (match (uu____1273) with
| true -> begin
(

let uu____1277 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____1283 = (

let uu____1286 = (FStar_Syntax_Util.mk_conj lb.FStar_Syntax_Syntax.lbtyp lb.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars lb.FStar_Syntax_Syntax.lbunivs uu____1286))
in (match (uu____1283) with
| (us, td) -> begin
(

let uu____1289 = (

let uu____1296 = (

let uu____1297 = (FStar_Syntax_Subst.compress td)
in uu____1297.FStar_Syntax_Syntax.n)
in (match (uu____1296) with
| FStar_Syntax_Syntax.Tm_app (uu____1306, ((t, uu____1308))::((d, uu____1310))::[]) -> begin
((t), (d))
end
| uu____1344 -> begin
(failwith "Impossibe")
end))
in (match (uu____1289) with
| (t, d) -> begin
(

let uu___190_1361 = lb
in {FStar_Syntax_Syntax.lbname = uu___190_1361.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu___190_1361.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = d})
end))
end)))))
in (((Prims.fst lbs)), (uu____1277)))
end
| uu____1364 -> begin
lbs
end))
in (

let uu____1365 = (quals_to_string' quals)
in (

let uu____1366 = (

let uu____1367 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let uu____1373 = (lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____1374 = (

let uu____1375 = (FStar_Options.print_universes ())
in (match (uu____1375) with
| true -> begin
(

let uu____1376 = (

let uu____1377 = (univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs)
in (Prims.strcat uu____1377 ">"))
in (Prims.strcat "<" uu____1376))
end
| uu____1378 -> begin
""
end))
in (

let uu____1379 = (term_to_string lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____1380 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef term_to_string)
in (FStar_Util.format4 "%s %s : %s = %s" uu____1373 uu____1374 uu____1379 uu____1380))))))))
in (FStar_Util.concat_l "\n and " uu____1367))
in (FStar_Util.format3 "%slet %s %s" uu____1365 (match ((Prims.fst lbs)) with
| true -> begin
"rec"
end
| uu____1384 -> begin
""
end) uu____1366)))))
and lcomp_to_string : FStar_Syntax_Syntax.lcomp  ->  Prims.string = (fun lc -> (

let uu____1386 = (FStar_Options.print_effect_args ())
in (match (uu____1386) with
| true -> begin
(

let uu____1387 = (lc.FStar_Syntax_Syntax.comp ())
in (comp_to_string uu____1387))
end
| uu____1388 -> begin
(

let uu____1389 = (sli lc.FStar_Syntax_Syntax.eff_name)
in (

let uu____1390 = (term_to_string lc.FStar_Syntax_Syntax.res_typ)
in (FStar_Util.format2 "%s %s" uu____1389 uu____1390)))
end)))
and imp_to_string : Prims.string  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option  ->  Prims.string = (fun s uu___184_1392 -> (match (uu___184_1392) with
| Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
(Prims.strcat "#" s)
end
| Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(Prims.strcat "#." s)
end
| Some (FStar_Syntax_Syntax.Equality) -> begin
(Prims.strcat "$" s)
end
| uu____1394 -> begin
s
end))
and binder_to_string' : Prims.bool  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun is_arrow b -> (

let uu____1400 = b
in (match (uu____1400) with
| (a, imp) -> begin
(

let uu____1405 = (FStar_Syntax_Syntax.is_null_binder b)
in (match (uu____1405) with
| true -> begin
(

let uu____1406 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat "_:" uu____1406))
end
| uu____1407 -> begin
(

let uu____1408 = ((not (is_arrow)) && (

let uu____1409 = (FStar_Options.print_bound_var_types ())
in (not (uu____1409))))
in (match (uu____1408) with
| true -> begin
(

let uu____1410 = (nm_to_string a)
in (imp_to_string uu____1410 imp))
end
| uu____1411 -> begin
(

let uu____1412 = (

let uu____1413 = (nm_to_string a)
in (

let uu____1414 = (

let uu____1415 = (term_to_string a.FStar_Syntax_Syntax.sort)
in (Prims.strcat ":" uu____1415))
in (Prims.strcat uu____1413 uu____1414)))
in (imp_to_string uu____1412 imp))
end))
end))
end)))
and binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' false b))
and arrow_binder_to_string : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)  ->  Prims.string = (fun b -> (binder_to_string' true b))
and binders_to_string : Prims.string  ->  FStar_Syntax_Syntax.binders  ->  Prims.string = (fun sep bs -> (

let bs = (

let uu____1425 = (FStar_Options.print_implicits ())
in (match (uu____1425) with
| true -> begin
bs
end
| uu____1426 -> begin
(filter_imp bs)
end))
in (match ((sep = " -> ")) with
| true -> begin
(

let uu____1427 = (FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string))
in (FStar_All.pipe_right uu____1427 (FStar_String.concat sep)))
end
| uu____1433 -> begin
(

let uu____1434 = (FStar_All.pipe_right bs (FStar_List.map binder_to_string))
in (FStar_All.pipe_right uu____1434 (FStar_String.concat sep)))
end)))
and arg_to_string : (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option)  ->  Prims.string = (fun uu___185_1440 -> (match (uu___185_1440) with
| (a, imp) -> begin
(

let uu____1448 = (term_to_string a)
in (imp_to_string uu____1448 imp))
end))
and args_to_string : FStar_Syntax_Syntax.args  ->  Prims.string = (fun args -> (

let args = (

let uu____1451 = (FStar_Options.print_implicits ())
in (match (uu____1451) with
| true -> begin
args
end
| uu____1452 -> begin
(filter_imp args)
end))
in (

let uu____1455 = (FStar_All.pipe_right args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1455 (FStar_String.concat " ")))))
and comp_to_string : FStar_Syntax_Syntax.comp  ->  Prims.string = (fun c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, uu____1464) -> begin
(

let uu____1471 = (

let uu____1472 = (FStar_Syntax_Subst.compress t)
in uu____1472.FStar_Syntax_Syntax.n)
in (match (uu____1471) with
| FStar_Syntax_Syntax.Tm_type (uu____1475) when (

let uu____1476 = (FStar_Options.print_implicits ())
in (not (uu____1476))) -> begin
(term_to_string t)
end
| uu____1477 -> begin
(

let uu____1478 = (term_to_string t)
in (FStar_Util.format1 "Tot %s" uu____1478))
end))
end
| FStar_Syntax_Syntax.GTotal (t, uu____1480) -> begin
(

let uu____1487 = (

let uu____1488 = (FStar_Syntax_Subst.compress t)
in uu____1488.FStar_Syntax_Syntax.n)
in (match (uu____1487) with
| FStar_Syntax_Syntax.Tm_type (uu____1491) when (

let uu____1492 = (FStar_Options.print_implicits ())
in (not (uu____1492))) -> begin
(term_to_string t)
end
| uu____1493 -> begin
(

let uu____1494 = (term_to_string t)
in (FStar_Util.format1 "GTot %s" uu____1494))
end))
end
| FStar_Syntax_Syntax.Comp (c) -> begin
(

let basic = (

let uu____1497 = (FStar_Options.print_effect_args ())
in (match (uu____1497) with
| true -> begin
(

let uu____1498 = (sli c.FStar_Syntax_Syntax.effect_name)
in (

let uu____1499 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (

let uu____1500 = (

let uu____1501 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map arg_to_string))
in (FStar_All.pipe_right uu____1501 (FStar_String.concat ", ")))
in (

let uu____1513 = (

let uu____1514 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.map cflags_to_string))
in (FStar_All.pipe_right uu____1514 (FStar_String.concat " ")))
in (FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1498 uu____1499 uu____1500 uu____1513)))))
end
| uu____1519 -> begin
(

let uu____1520 = ((FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___186_1522 -> (match (uu___186_1522) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1523 -> begin
false
end)))) && (

let uu____1524 = (FStar_Options.print_effect_args ())
in (not (uu____1524))))
in (match (uu____1520) with
| true -> begin
(

let uu____1525 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "Tot %s" uu____1525))
end
| uu____1526 -> begin
(

let uu____1527 = (((

let uu____1528 = (FStar_Options.print_effect_args ())
in (not (uu____1528))) && (

let uu____1529 = (FStar_Options.print_implicits ())
in (not (uu____1529)))) && (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name FStar_Syntax_Const.effect_ML_lid))
in (match (uu____1527) with
| true -> begin
(term_to_string c.FStar_Syntax_Syntax.result_typ)
end
| uu____1530 -> begin
(

let uu____1531 = ((

let uu____1532 = (FStar_Options.print_effect_args ())
in (not (uu____1532))) && (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun uu___187_1534 -> (match (uu___187_1534) with
| FStar_Syntax_Syntax.MLEFFECT -> begin
true
end
| uu____1535 -> begin
false
end)))))
in (match (uu____1531) with
| true -> begin
(

let uu____1536 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format1 "ALL %s" uu____1536))
end
| uu____1537 -> begin
(

let uu____1538 = (sli c.FStar_Syntax_Syntax.effect_name)
in (

let uu____1539 = (term_to_string c.FStar_Syntax_Syntax.result_typ)
in (FStar_Util.format2 "%s (%s)" uu____1538 uu____1539)))
end))
end))
end))
end))
in (

let dec = (

let uu____1541 = (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags (FStar_List.collect (fun uu___188_1545 -> (match (uu___188_1545) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let uu____1550 = (

let uu____1551 = (term_to_string e)
in (FStar_Util.format1 " (decreases %s)" uu____1551))
in (uu____1550)::[])
end
| uu____1552 -> begin
[]
end))))
in (FStar_All.pipe_right uu____1541 (FStar_String.concat " ")))
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
| FStar_Syntax_Syntax.DECREASES (uu____1555) -> begin
""
end))
and formula_to_string : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun phi -> (term_to_string phi))


let enclose_universes : Prims.string  ->  Prims.string = (fun s -> (

let uu____1564 = (FStar_Options.print_universes ())
in (match (uu____1564) with
| true -> begin
(Prims.strcat "<" (Prims.strcat s ">"))
end
| uu____1565 -> begin
""
end)))


let tscheme_to_string : FStar_Syntax_Syntax.tscheme  ->  Prims.string = (fun uu____1568 -> (match (uu____1568) with
| (us, t) -> begin
(

let uu____1573 = (

let uu____1574 = (univ_names_to_string us)
in (FStar_All.pipe_left enclose_universes uu____1574))
in (

let uu____1575 = (term_to_string t)
in (FStar_Util.format2 "%s%s" uu____1573 uu____1575)))
end))


let eff_decl_to_string : Prims.bool  ->  FStar_Syntax_Syntax.eff_decl  ->  Prims.string = (fun for_free ed -> (

let actions_to_string = (fun actions -> (

let uu____1588 = (FStar_All.pipe_right actions (FStar_List.map (fun a -> (

let uu____1593 = (sli a.FStar_Syntax_Syntax.action_name)
in (

let uu____1594 = (

let uu____1595 = (univ_names_to_string a.FStar_Syntax_Syntax.action_univs)
in (FStar_All.pipe_left enclose_universes uu____1595))
in (

let uu____1596 = (term_to_string a.FStar_Syntax_Syntax.action_typ)
in (

let uu____1597 = (term_to_string a.FStar_Syntax_Syntax.action_defn)
in (FStar_Util.format4 "%s%s : %s = %s" uu____1593 uu____1594 uu____1596 uu____1597))))))))
in (FStar_All.pipe_right uu____1588 (FStar_String.concat ",\n\t"))))
in (

let uu____1599 = (

let uu____1601 = (

let uu____1603 = (lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____1604 = (

let uu____1606 = (

let uu____1607 = (univ_names_to_string ed.FStar_Syntax_Syntax.univs)
in (FStar_All.pipe_left enclose_universes uu____1607))
in (

let uu____1608 = (

let uu____1610 = (binders_to_string " " ed.FStar_Syntax_Syntax.binders)
in (

let uu____1611 = (

let uu____1613 = (term_to_string ed.FStar_Syntax_Syntax.signature)
in (

let uu____1614 = (

let uu____1616 = (tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____1617 = (

let uu____1619 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____1620 = (

let uu____1622 = (tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____1623 = (

let uu____1625 = (tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____1626 = (

let uu____1628 = (tscheme_to_string ed.FStar_Syntax_Syntax.stronger)
in (

let uu____1629 = (

let uu____1631 = (tscheme_to_string ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____1632 = (

let uu____1634 = (tscheme_to_string ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____1635 = (

let uu____1637 = (tscheme_to_string ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____1638 = (

let uu____1640 = (tscheme_to_string ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____1641 = (

let uu____1643 = (tscheme_to_string ed.FStar_Syntax_Syntax.trivial)
in (

let uu____1644 = (

let uu____1646 = (term_to_string ed.FStar_Syntax_Syntax.repr)
in (

let uu____1647 = (

let uu____1649 = (tscheme_to_string ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____1650 = (

let uu____1652 = (tscheme_to_string ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____1653 = (

let uu____1655 = (actions_to_string ed.FStar_Syntax_Syntax.actions)
in (uu____1655)::[])
in (uu____1652)::uu____1653))
in (uu____1649)::uu____1650))
in (uu____1646)::uu____1647))
in (uu____1643)::uu____1644))
in (uu____1640)::uu____1641))
in (uu____1637)::uu____1638))
in (uu____1634)::uu____1635))
in (uu____1631)::uu____1632))
in (uu____1628)::uu____1629))
in (uu____1625)::uu____1626))
in (uu____1622)::uu____1623))
in (uu____1619)::uu____1620))
in (uu____1616)::uu____1617))
in (uu____1613)::uu____1614))
in (uu____1610)::uu____1611))
in (uu____1606)::uu____1608))
in (uu____1603)::uu____1604))
in ((match (for_free) with
| true -> begin
"_for_free "
end
| uu____1656 -> begin
""
end))::uu____1601)
in (FStar_Util.format "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n" uu____1599))))


let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff, uu____1660) -> begin
"#light \"off\""
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None), uu____1661) -> begin
"#reset-options"
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some (s)), uu____1663) -> begin
(FStar_Util.format1 "#reset-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions (s), uu____1665) -> begin
(FStar_Util.format1 "#set-options \"%s\"" s)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, univs, tps, k, uu____1670, uu____1671, quals, uu____1673) -> begin
(

let uu____1680 = (quals_to_string' quals)
in (

let uu____1681 = (binders_to_string " " tps)
in (

let uu____1682 = (term_to_string k)
in (FStar_Util.format4 "%stype %s %s : %s" uu____1680 lid.FStar_Ident.str uu____1681 uu____1682))))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, univs, t, uu____1686, uu____1687, uu____1688, uu____1689, uu____1690) -> begin
(

let uu____1695 = (FStar_Options.print_universes ())
in (match (uu____1695) with
| true -> begin
(

let uu____1696 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1696) with
| (univs, t) -> begin
(

let uu____1701 = (univ_names_to_string univs)
in (

let uu____1702 = (term_to_string t)
in (FStar_Util.format3 "datacon<%s> %s : %s" uu____1701 lid.FStar_Ident.str uu____1702)))
end))
end
| uu____1703 -> begin
(

let uu____1704 = (term_to_string t)
in (FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str uu____1704))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t, quals, uu____1709) -> begin
(

let uu____1712 = (FStar_Syntax_Subst.open_univ_vars univs t)
in (match (uu____1712) with
| (univs, t) -> begin
(

let uu____1717 = (quals_to_string' quals)
in (

let uu____1718 = (

let uu____1719 = (FStar_Options.print_universes ())
in (match (uu____1719) with
| true -> begin
(

let uu____1720 = (univ_names_to_string univs)
in (FStar_Util.format1 "<%s>" uu____1720))
end
| uu____1721 -> begin
""
end))
in (

let uu____1722 = (term_to_string t)
in (FStar_Util.format4 "%sval %s %s : %s" uu____1717 lid.FStar_Ident.str uu____1718 uu____1722))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, f, uu____1725, uu____1726) -> begin
(

let uu____1729 = (term_to_string f)
in (FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1729))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____1731, uu____1732, qs, uu____1734) -> begin
(lbs_to_string qs lbs)
end
| FStar_Syntax_Syntax.Sig_main (e, uu____1742) -> begin
(

let uu____1743 = (term_to_string e)
in (FStar_Util.format1 "let _ = %s" uu____1743))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____1745, uu____1746, uu____1747) -> begin
(

let uu____1754 = (FStar_List.map sigelt_to_string ses)
in (FStar_All.pipe_right uu____1754 (FStar_String.concat "\n")))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____1758) -> begin
(eff_decl_to_string false ed)
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed, uu____1760) -> begin
(eff_decl_to_string true ed)
end
| FStar_Syntax_Syntax.Sig_sub_effect (se, r) -> begin
(

let lift_wp = (match (((se.FStar_Syntax_Syntax.lift_wp), (se.FStar_Syntax_Syntax.lift))) with
| (None, None) -> begin
(failwith "impossible")
end
| (Some (lift_wp), uu____1769) -> begin
lift_wp
end
| (uu____1773, Some (lift)) -> begin
lift
end)
in (

let uu____1778 = (FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp) (Prims.snd lift_wp))
in (match (uu____1778) with
| (us, t) -> begin
(

let uu____1785 = (lid_to_string se.FStar_Syntax_Syntax.source)
in (

let uu____1786 = (lid_to_string se.FStar_Syntax_Syntax.target)
in (

let uu____1787 = (univ_names_to_string us)
in (

let uu____1788 = (term_to_string t)
in (FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1785 uu____1786 uu____1787 uu____1788)))))
end)))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, uu____1793, flags, uu____1795) -> begin
(

let uu____1800 = (FStar_Options.print_universes ())
in (match (uu____1800) with
| true -> begin
(

let uu____1801 = (

let uu____1804 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (((tps), (c))))) None FStar_Range.dummyRange)
in (FStar_Syntax_Subst.open_univ_vars univs uu____1804))
in (match (uu____1801) with
| (univs, t) -> begin
(

let uu____1815 = (

let uu____1823 = (

let uu____1824 = (FStar_Syntax_Subst.compress t)
in uu____1824.FStar_Syntax_Syntax.n)
in (match (uu____1823) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
((bs), (c))
end
| uu____1851 -> begin
(failwith "impossible")
end))
in (match (uu____1815) with
| (tps, c) -> begin
(

let uu____1871 = (sli l)
in (

let uu____1872 = (univ_names_to_string univs)
in (

let uu____1873 = (binders_to_string " " tps)
in (

let uu____1874 = (comp_to_string c)
in (FStar_Util.format4 "effect %s<%s> %s = %s" uu____1871 uu____1872 uu____1873 uu____1874)))))
end))
end))
end
| uu____1875 -> begin
(

let uu____1876 = (sli l)
in (

let uu____1877 = (binders_to_string " " tps)
in (

let uu____1878 = (comp_to_string c)
in (FStar_Util.format3 "effect %s %s = %s" uu____1876 uu____1877 uu____1878))))
end))
end))


let format_error : FStar_Range.range  ->  Prims.string  ->  Prims.string = (fun r msg -> (

let uu____1885 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "%s: %s\n" uu____1885 msg)))


let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt  ->  Prims.string = (fun x -> (match (x) with
| FStar_Syntax_Syntax.Sig_let ((uu____1889, ({FStar_Syntax_Syntax.lbname = lb; FStar_Syntax_Syntax.lbunivs = uu____1891; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = uu____1893; FStar_Syntax_Syntax.lbdef = uu____1894})::[]), uu____1895, uu____1896, uu____1897, uu____1898) -> begin
(

let uu____1916 = (lbname_to_string lb)
in (

let uu____1917 = (term_to_string t)
in (FStar_Util.format2 "let %s : %s" uu____1916 uu____1917)))
end
| uu____1918 -> begin
(

let uu____1919 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x) (FStar_List.map (fun l -> l.FStar_Ident.str)))
in (FStar_All.pipe_right uu____1919 (FStar_String.concat ", ")))
end))


let rec modul_to_string : FStar_Syntax_Syntax.modul  ->  Prims.string = (fun m -> (

let uu____1928 = (sli m.FStar_Syntax_Syntax.name)
in (

let uu____1929 = (

let uu____1930 = (FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations)
in (FStar_All.pipe_right uu____1930 (FStar_String.concat "\n")))
in (FStar_Util.format2 "module %s\n%s" uu____1928 uu____1929))))


let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt  ->  Prims.string = (fun uu___189_1935 -> (match (uu___189_1935) with
| FStar_Syntax_Syntax.DB (i, x) -> begin
(

let uu____1938 = (FStar_Util.string_of_int i)
in (

let uu____1939 = (bv_to_string x)
in (FStar_Util.format2 "DB (%s, %s)" uu____1938 uu____1939)))
end
| FStar_Syntax_Syntax.NM (x, i) -> begin
(

let uu____1942 = (bv_to_string x)
in (

let uu____1943 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "NM (%s, %s)" uu____1942 uu____1943)))
end
| FStar_Syntax_Syntax.NT (x, t) -> begin
(

let uu____1950 = (bv_to_string x)
in (

let uu____1951 = (term_to_string t)
in (FStar_Util.format2 "DB (%s, %s)" uu____1950 uu____1951)))
end
| FStar_Syntax_Syntax.UN (i, u) -> begin
(

let uu____1954 = (FStar_Util.string_of_int i)
in (

let uu____1955 = (univ_to_string u)
in (FStar_Util.format2 "UN (%s, %s)" uu____1954 uu____1955)))
end
| FStar_Syntax_Syntax.UD (u, i) -> begin
(

let uu____1958 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1958))
end))


let subst_to_string : FStar_Syntax_Syntax.subst_t  ->  Prims.string = (fun s -> (

let uu____1962 = (FStar_All.pipe_right s (FStar_List.map subst_elt_to_string))
in (FStar_All.pipe_right uu____1962 (FStar_String.concat "; "))))


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

let uu____2012 = (f x)
in (FStar_Util.string_builder_append strb uu____2012));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb "; ");
(

let uu____2016 = (f x)
in (FStar_Util.string_builder_append strb uu____2016));
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

let uu____2045 = (f x)
in (FStar_Util.string_builder_append strb uu____2045));
(FStar_List.iter (fun x -> ((FStar_Util.string_builder_append strb ", ");
(

let uu____2049 = (f x)
in (FStar_Util.string_builder_append strb uu____2049));
)) xs);
(FStar_Util.string_builder_append strb "}");
(FStar_Util.string_of_string_builder strb);
))
end)))





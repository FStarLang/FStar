
open Prims
open FStar_Pervasives

let doc_to_string : FStar_Pprint.document  ->  Prims.string = (fun doc1 -> (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1))


let parser_term_to_string : FStar_Parser_AST.term  ->  Prims.string = (fun t -> (

let uu____15 = (FStar_Parser_ToDocument.term_to_document t)
in (doc_to_string uu____15)))


let parser_pat_to_string : FStar_Parser_AST.pattern  ->  Prims.string = (fun t -> (

let uu____23 = (FStar_Parser_ToDocument.pat_to_document t)
in (doc_to_string uu____23)))


let map_opt : 'Auu____33 'Auu____34 . unit  ->  ('Auu____33  ->  'Auu____34 FStar_Pervasives_Native.option)  ->  'Auu____33 Prims.list  ->  'Auu____34 Prims.list = (fun uu____50 -> FStar_List.filter_map)


let bv_as_unique_ident : FStar_Syntax_Syntax.bv  ->  FStar_Ident.ident = (fun x -> (

let unique_name = (

let uu____59 = ((FStar_Util.starts_with FStar_Ident.reserved_prefix x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) || (FStar_Options.print_real_names ()))
in (match (uu____59) with
| true -> begin
(

let uu____63 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.op_Hat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____63))
end
| uu____65 -> begin
x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))
in (FStar_Ident.mk_ident ((unique_name), (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))))


let filter_imp : 'Auu____73 . ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___0_128 -> (match (uu___0_128) with
| (uu____136, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t))) when (FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t) -> begin
true
end
| (uu____143, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____144))) -> begin
false
end
| (uu____149, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (uu____150))) -> begin
false
end
| uu____156 -> begin
true
end)))))


let filter_pattern_imp : 'Auu____169 . ('Auu____169 * Prims.bool) Prims.list  ->  ('Auu____169 * Prims.bool) Prims.list = (fun xs -> (FStar_List.filter (fun uu____204 -> (match (uu____204) with
| (uu____211, is_implicit1) -> begin
(not (is_implicit1))
end)) xs))


let label : Prims.string  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun s t -> (match ((Prims.op_Equality s "")) with
| true -> begin
t
end
| uu____231 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((t), (s), (true)))) t.FStar_Parser_AST.range FStar_Parser_AST.Un)
end))


let rec universe_to_int : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe) = (fun n1 u -> (match (u) with
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(universe_to_int (n1 + (Prims.parse_int "1")) u1)
end
| uu____261 -> begin
((n1), (u))
end))


let universe_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun univs1 -> (

let uu____274 = (FStar_Options.print_universes ())
in (match (uu____274) with
| true -> begin
(

let uu____278 = (FStar_List.map (fun x -> x.FStar_Ident.idText) univs1)
in (FStar_All.pipe_right uu____278 (FStar_String.concat ", ")))
end
| uu____290 -> begin
""
end)))


let rec resugar_universe' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun env u r -> (resugar_universe u r))
and resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____342) -> begin
(

let uu____343 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____343) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____354 = (

let uu____355 = (

let uu____356 = (

let uu____368 = (FStar_Util.string_of_int n1)
in ((uu____368), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____356))
in FStar_Parser_AST.Const (uu____355))
in (mk1 uu____354 r))
end
| uu____381 -> begin
(

let e1 = (

let uu____383 = (

let uu____384 = (

let uu____385 = (

let uu____397 = (FStar_Util.string_of_int n1)
in ((uu____397), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____385))
in FStar_Parser_AST.Const (uu____384))
in (mk1 uu____383 r))
in (

let e2 = (resugar_universe u1 r)
in (

let uu____411 = (

let uu____412 = (

let uu____419 = (FStar_Ident.id_of_text "+")
in ((uu____419), ((e1)::(e2)::[])))
in FStar_Parser_AST.Op (uu____412))
in (mk1 uu____411 r))))
end)
end))
end
| FStar_Syntax_Syntax.U_max (l) -> begin
(match (l) with
| [] -> begin
(failwith "Impossible: U_max without arguments")
end
| uu____427 -> begin
(

let t = (

let uu____431 = (

let uu____432 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____432))
in (mk1 uu____431 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____441 = (

let uu____442 = (

let uu____449 = (resugar_universe x r)
in ((acc), (uu____449), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____442))
in (mk1 uu____441 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____451) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id1 = (

let uu____463 = (

let uu____469 = (

let uu____471 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____471))
in ((uu____469), (r)))
in (FStar_Ident.mk_ident uu____463))
in (mk1 (FStar_Parser_AST.Uvar (id1)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___1_509 -> (match (uu___1_509) with
| "Amp" -> begin
FStar_Pervasives_Native.Some ((("&"), (FStar_Pervasives_Native.None)))
end
| "At" -> begin
FStar_Pervasives_Native.Some ((("@"), (FStar_Pervasives_Native.None)))
end
| "Plus" -> begin
FStar_Pervasives_Native.Some ((("+"), (FStar_Pervasives_Native.None)))
end
| "Minus" -> begin
FStar_Pervasives_Native.Some ((("-"), (FStar_Pervasives_Native.None)))
end
| "Subtraction" -> begin
FStar_Pervasives_Native.Some ((("-"), (FStar_Pervasives_Native.Some ((Prims.parse_int "2")))))
end
| "Tilde" -> begin
FStar_Pervasives_Native.Some ((("~"), (FStar_Pervasives_Native.None)))
end
| "Slash" -> begin
FStar_Pervasives_Native.Some ((("/"), (FStar_Pervasives_Native.None)))
end
| "Backslash" -> begin
FStar_Pervasives_Native.Some ((("\\"), (FStar_Pervasives_Native.None)))
end
| "Less" -> begin
FStar_Pervasives_Native.Some ((("<"), (FStar_Pervasives_Native.None)))
end
| "Equals" -> begin
FStar_Pervasives_Native.Some ((("="), (FStar_Pervasives_Native.None)))
end
| "Greater" -> begin
FStar_Pervasives_Native.Some (((">"), (FStar_Pervasives_Native.None)))
end
| "Underscore" -> begin
FStar_Pervasives_Native.Some ((("_"), (FStar_Pervasives_Native.None)))
end
| "Bar" -> begin
FStar_Pervasives_Native.Some ((("|"), (FStar_Pervasives_Native.None)))
end
| "Bang" -> begin
FStar_Pervasives_Native.Some ((("!"), (FStar_Pervasives_Native.None)))
end
| "Hat" -> begin
FStar_Pervasives_Native.Some ((("^"), (FStar_Pervasives_Native.None)))
end
| "Percent" -> begin
FStar_Pervasives_Native.Some ((("%"), (FStar_Pervasives_Native.None)))
end
| "Star" -> begin
FStar_Pervasives_Native.Some ((("*"), (FStar_Pervasives_Native.None)))
end
| "Question" -> begin
FStar_Pervasives_Native.Some ((("?"), (FStar_Pervasives_Native.None)))
end
| "Colon" -> begin
FStar_Pervasives_Native.Some (((":"), (FStar_Pervasives_Native.None)))
end
| "Dollar" -> begin
FStar_Pervasives_Native.Some ((("$"), (FStar_Pervasives_Native.None)))
end
| "Dot" -> begin
FStar_Pervasives_Native.Some ((("."), (FStar_Pervasives_Native.None)))
end
| uu____837 -> begin
FStar_Pervasives_Native.None
end))
in (match (s) with
| "op_String_Assignment" -> begin
FStar_Pervasives_Native.Some (((".[]<-"), (FStar_Pervasives_Native.None)))
end
| "op_Array_Assignment" -> begin
FStar_Pervasives_Native.Some (((".()<-"), (FStar_Pervasives_Native.None)))
end
| "op_Brack_Lens_Assignment" -> begin
FStar_Pervasives_Native.Some (((".[||]<-"), (FStar_Pervasives_Native.None)))
end
| "op_Lens_Assignment" -> begin
FStar_Pervasives_Native.Some (((".(||)<-"), (FStar_Pervasives_Native.None)))
end
| "op_String_Access" -> begin
FStar_Pervasives_Native.Some (((".[]"), (FStar_Pervasives_Native.None)))
end
| "op_Array_Access" -> begin
FStar_Pervasives_Native.Some (((".()"), (FStar_Pervasives_Native.None)))
end
| "op_Brack_Lens_Access" -> begin
FStar_Pervasives_Native.Some (((".[||]"), (FStar_Pervasives_Native.None)))
end
| "op_Lens_Access" -> begin
FStar_Pervasives_Native.Some (((".(||)"), (FStar_Pervasives_Native.None)))
end
| uu____977 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____995 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____995 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____1013 -> begin
(

let op = (

let uu____1019 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (x) with
| FStar_Pervasives_Native.Some (op, uu____1073) -> begin
(Prims.op_Hat acc op)
end
| FStar_Pervasives_Native.None -> begin
(failwith "wrong composed operator format")
end)) "" uu____1019))
in FStar_Pervasives_Native.Some (((op), (FStar_Pervasives_Native.None))))
end))
end
| uu____1114 -> begin
FStar_Pervasives_Native.None
end)
end)))


type expected_arity =
Prims.int FStar_Pervasives_Native.option


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * expected_arity) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____1400 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____1400) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), (FStar_Pervasives_Native.None)))
end
| uu____1470 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1485 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), (FStar_Pervasives_Native.None)))
end
| uu____1514 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), (FStar_Pervasives_Native.None)))
end
| uu____1542 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), (FStar_Pervasives_Native.None)))
end
| uu____1570 -> begin
(

let uu____1572 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____1572) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), (FStar_Pervasives_Native.None)))
end
| uu____1598 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____1608 = (

let uu____1609 = (FStar_Syntax_Subst.compress t)
in uu____1609.FStar_Syntax_Syntax.n)
in (match (uu____1608) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1627 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____1630 = (string_to_op s)
in (match (uu____1630) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____1670 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____1687 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____1704 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____1715) -> begin
true
end
| uu____1717 -> begin
false
end))


let is_tuple_constructor_lid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Parser_Const.is_tuple_data_lid' lid) || (FStar_Parser_Const.is_dtuple_data_lid' lid)))


let may_shorten : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (match (lid.FStar_Ident.str) with
| "Prims.Nil" -> begin
false
end
| "Prims.Cons" -> begin
false
end
| uu____1738 -> begin
(

let uu____1740 = (is_tuple_constructor_lid lid)
in (not (uu____1740)))
end))


let maybe_shorten_fv : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Ident.lident = (fun env fv -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____1754 = (may_shorten lid)
in (match (uu____1754) with
| true -> begin
(FStar_Syntax_DsEnv.shorten_lid env lid)
end
| uu____1757 -> begin
lid
end))))


let rec resugar_term' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun env t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____1899 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____1899)))
in (

let uu____1902 = (

let uu____1903 = (FStar_Syntax_Subst.compress t)
in uu____1903.FStar_Syntax_Syntax.n)
in (match (uu____1902) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1906) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1931 = (FStar_Syntax_Util.unfold_lazy i)
in (resugar_term' env uu____1931))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____1934 = (

let uu____1937 = (bv_as_unique_ident x)
in (uu____1937)::[])
in (FStar_Ident.lid_of_ids uu____1934))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____1940 = (

let uu____1943 = (bv_as_unique_ident x)
in (uu____1943)::[])
in (FStar_Ident.lid_of_ids uu____1940))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let a = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
a.FStar_Ident.str
end
| uu____1953 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.op_Hat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____1962 = (

let uu____1963 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____1963))
in (mk1 uu____1962)))
end
| uu____1966 -> begin
(match ((FStar_Util.starts_with s FStar_Syntax_Util.field_projector_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length FStar_Syntax_Util.field_projector_prefix))
in (

let r = (FStar_Util.split rest FStar_Syntax_Util.field_projector_sep)
in (match (r) with
| (fst1)::(snd1)::[] -> begin
(

let l = (FStar_Ident.lid_of_path ((fst1)::[]) t.FStar_Syntax_Syntax.pos)
in (

let r1 = (FStar_Ident.mk_ident ((snd1), (t.FStar_Syntax_Syntax.pos)))
in (mk1 (FStar_Parser_AST.Projector (((l), (r1)))))))
end
| uu____1987 -> begin
(failwith "wrong projector format")
end)))
end
| uu____1992 -> begin
(

let uu____1994 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____1998 = (

let uu____2000 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____2000))
in (

let uu____2003 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____1998 uu____2003))))
in (match (uu____1994) with
| true -> begin
(

let uu____2008 = (

let uu____2009 = (maybe_shorten_fv env fv)
in FStar_Parser_AST.Var (uu____2009))
in (mk1 uu____2008))
end
| uu____2010 -> begin
(

let uu____2012 = (

let uu____2013 = (

let uu____2024 = (maybe_shorten_fv env fv)
in ((uu____2024), ([])))
in FStar_Parser_AST.Construct (uu____2013))
in (mk1 uu____2012))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let e1 = (resugar_term' env e)
in (

let uu____2042 = (FStar_Options.print_universes ())
in (match (uu____2042) with
| true -> begin
(

let univs1 = (FStar_List.map (fun x -> (resugar_universe x t.FStar_Syntax_Syntax.pos)) universes)
in (match (e1) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(

let args1 = (

let uu____2073 = (FStar_List.map (fun u -> ((u), (FStar_Parser_AST.UnivApp))) univs1)
in (FStar_List.append args uu____2073))
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), (args1)))) r l))
end
| uu____2096 -> begin
(FStar_List.fold_left (fun acc u -> (mk1 (FStar_Parser_AST.App (((acc), (u), (FStar_Parser_AST.UnivApp)))))) e1 univs1)
end))
end
| uu____2101 -> begin
e1
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2104 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____2104) with
| true -> begin
(

let uu____2107 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____2107))
end
| uu____2109 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____2112 = (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(("Type0"), (false))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(("Type"), (false))
end
| uu____2133 -> begin
(("Type"), (true))
end)
in (match (uu____2112) with
| (nm, needs_app) -> begin
(

let typ = (

let uu____2145 = (name nm t.FStar_Syntax_Syntax.pos)
in (mk1 uu____2145))
in (

let uu____2146 = (needs_app && (FStar_Options.print_universes ()))
in (match (uu____2146) with
| true -> begin
(

let uu____2149 = (

let uu____2150 = (

let uu____2157 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((typ), (uu____2157), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____2150))
in (mk1 uu____2149))
end
| uu____2158 -> begin
typ
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____2162) -> begin
(

let uu____2187 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____2187) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____2203 = (FStar_Options.print_implicits ())
in (match (uu____2203) with
| true -> begin
xs1
end
| uu____2214 -> begin
(filter_imp xs1)
end))
in (

let body_bv = (FStar_Syntax_Free.names body1)
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____2241 -> (match (uu____2241) with
| (x, qual) -> begin
(resugar_bv_as_pat env x qual body_bv)
end))))
in (

let body2 = (resugar_term' env body1)
in (mk1 (FStar_Parser_AST.Abs (((patterns), (body2)))))))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, body) -> begin
(

let uu____2281 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____2281) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____2291 = (FStar_Options.print_implicits ())
in (match (uu____2291) with
| true -> begin
xs1
end
| uu____2296 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp' env body1)
in (

let xs3 = (

let uu____2302 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____2302 FStar_List.rev))
in (

let rec aux = (fun body3 uu___2_2327 -> (match (uu___2_2327) with
| [] -> begin
body3
end
| (hd1)::tl1 -> begin
(

let body4 = (mk1 (FStar_Parser_AST.Product ((((hd1)::[]), (body3)))))
in (aux body4 tl1))
end))
in (aux body2 xs3)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let uu____2343 = (

let uu____2348 = (

let uu____2349 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2349)::[])
in (FStar_Syntax_Subst.open_term uu____2348 phi))
in (match (uu____2343) with
| (x1, phi1) -> begin
(

let b = (

let uu____2371 = (

let uu____2374 = (FStar_List.hd x1)
in (resugar_binder' env uu____2374 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____2371))
in (

let uu____2381 = (

let uu____2382 = (

let uu____2387 = (resugar_term' env phi1)
in ((b), (uu____2387)))
in FStar_Parser_AST.Refine (uu____2382))
in (mk1 uu____2381)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2389; FStar_Syntax_Syntax.vars = uu____2390}, ((e, uu____2392))::[]) when ((

let uu____2433 = (FStar_Options.print_implicits ())
in (not (uu____2433))) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___3_2482 -> (match (uu___3_2482) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____2552 -> begin
(failwith "last of an empty list")
end))
in (

let rec last_two = (fun uu___4_2591 -> (match (uu___4_2591) with
| [] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (uu____2623)::[] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (a1)::(a2)::[] -> begin
(a1)::(a2)::[]
end
| (uu____2701)::t1 -> begin
(last_two t1)
end))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_List.map (fun uu____2772 -> (match (uu____2772) with
| (e2, qual) -> begin
(

let uu____2789 = (resugar_term' env e2)
in (

let uu____2790 = (resugar_imp env qual)
in ((uu____2789), (uu____2790))))
end)) args1)
in (

let uu____2791 = (resugar_term' env e1)
in (match (uu____2791) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, previous_args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), ((FStar_List.append previous_args args2))))) r l)
end
| e2 -> begin
(FStar_List.fold_left (fun acc uu____2828 -> (match (uu____2828) with
| (x, qual) -> begin
(mk1 (FStar_Parser_AST.App (((acc), (x), (qual)))))
end)) e2 args2)
end))))
in (

let args1 = (

let uu____2844 = (FStar_Options.print_implicits ())
in (match (uu____2844) with
| true -> begin
args
end
| uu____2855 -> begin
(filter_imp args)
end))
in (

let uu____2859 = (resugar_term_as_op e)
in (match (uu____2859) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____2872) -> begin
(

let out = (FStar_List.fold_left (fun out uu____2897 -> (match (uu____2897) with
| (x, uu____2909) -> begin
(

let x1 = (resugar_term' env x)
in (match (out) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (x1)
end
| FStar_Pervasives_Native.Some (prefix1) -> begin
(

let uu____2918 = (

let uu____2919 = (

let uu____2920 = (

let uu____2927 = (FStar_Ident.id_of_text "*")
in ((uu____2927), ((prefix1)::(x1)::[])))
in FStar_Parser_AST.Op (uu____2920))
in (mk1 uu____2919))
in FStar_Pervasives_Native.Some (uu____2918))
end))
end)) FStar_Pervasives_Native.None args1)
in (FStar_Option.get out))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____2931) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____2957))::[] -> begin
b
end
| uu____2974 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____2984 = (

let uu____2985 = (FStar_Syntax_Subst.compress body)
in uu____2985.FStar_Syntax_Syntax.n)
in (match (uu____2984) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2990) -> begin
(

let uu____3015 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____3015) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____3025 = (FStar_Options.print_implicits ())
in (match (uu____3025) with
| true -> begin
xs1
end
| uu____3030 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term' env body2)
in (

let uu____3042 = (

let uu____3043 = (

let uu____3054 = (FStar_List.map (fun _3065 -> FStar_Util.Inl (_3065)) xs3)
in ((uu____3054), (body3)))
in FStar_Parser_AST.Sum (uu____3043))
in (mk1 uu____3042)))))
end))
end
| uu____3072 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____3095 -> (match (uu____3095) with
| (e1, qual) -> begin
(resugar_term' env e1)
end))))
in (

let e1 = (resugar_term' env e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____3113) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____3122) when (Prims.op_Equality ref_read FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____3131 = (FStar_List.hd args1)
in (match (uu____3131) with
| (t1, uu____3145) -> begin
(

let uu____3150 = (

let uu____3151 = (FStar_Syntax_Subst.compress t1)
in uu____3151.FStar_Syntax_Syntax.n)
in (match (uu____3150) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____3158 = (

let uu____3159 = (

let uu____3164 = (resugar_term' env t1)
in ((uu____3164), (f)))
in FStar_Parser_AST.Project (uu____3159))
in (mk1 uu____3158)))
end
| uu____3165 -> begin
(resugar_term' env t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____3166) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(

let new_args = (last_two args1)
in (

let uu____3190 = (match (new_args) with
| ((a1, uu____3200))::((a2, uu____3202))::[] -> begin
((a1), (a2))
end
| uu____3229 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____3190) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____3251 = (

let uu____3252 = (FStar_Syntax_Subst.compress term)
in uu____3252.FStar_Syntax_Syntax.n)
in (match (uu____3251) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____3257) -> begin
(

let uu____3282 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____3282) with
| (x1, e2) -> begin
e2
end))
end
| uu____3289 -> begin
(failwith "wrong argument format to try_with")
end)))
in (

let body1 = (

let uu____3292 = (decomp body)
in (resugar_term' env uu____3292))
in (

let handler1 = (

let uu____3294 = (decomp handler)
in (resugar_term' env uu____3294))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____3302, uu____3303, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____3335, uu____3336, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____3373 = (

let uu____3374 = (

let uu____3383 = (resugar_body t11)
in ((uu____3383), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____3374))
in (mk1 uu____3373))
end
| uu____3386 -> begin
(failwith "unexpected body format to try_with")
end))
in (

let e1 = (resugar_body body1)
in (

let rec resugar_branches = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e2, branches) -> begin
branches
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(resugar_branches t11)
end
| uu____3444 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____3474) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____3483) when (((((((Prims.op_Equality op "=") || (Prims.op_Equality op "==")) || (Prims.op_Equality op "===")) || (Prims.op_Equality op "@")) || (Prims.op_Equality op ":=")) || (Prims.op_Equality op "|>")) && (FStar_Options.print_implicits ())) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____3504) when ((Prims.op_Equality op "forall") || (Prims.op_Equality op "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, (uu____3569, p), body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, (uu____3601, p), body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____3632 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____3645 = (

let uu____3646 = (FStar_Syntax_Subst.compress body)
in uu____3646.FStar_Syntax_Syntax.n)
in (match (uu____3645) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3651) -> begin
(

let uu____3676 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____3676) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____3686 = (FStar_Options.print_implicits ())
in (match (uu____3686) with
| true -> begin
xs1
end
| uu____3691 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let uu____3702 = (

let uu____3711 = (

let uu____3712 = (FStar_Syntax_Subst.compress body2)
in uu____3712.FStar_Syntax_Syntax.n)
in (match (uu____3711) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term' env e1)
in (

let uu____3730 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____3747, pats) -> begin
(

let uu____3781 = (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____3825 -> (match (uu____3825) with
| (e2, uu____3833) -> begin
(resugar_term' env e2)
end))))) pats)
in ((uu____3781), (body3)))
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, p) -> begin
(

let uu____3849 = (mk1 (FStar_Parser_AST.Labeled (((body3), (s), (p)))))
in (([]), (uu____3849)))
end
| uu____3858 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in (match (uu____3730) with
| (pats, body4) -> begin
((pats), (body4))
end)))
end
| uu____3890 -> begin
(

let uu____3891 = (resugar_term' env body2)
in (([]), (uu____3891)))
end))
in (match (uu____3702) with
| (pats, body3) -> begin
(

let uu____3908 = (uncurry xs3 pats body3)
in (match (uu____3908) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____3946 = (

let uu____3947 = (

let uu____3966 = (

let uu____3977 = (FStar_Parser_AST.idents_of_binders xs5 t.FStar_Syntax_Syntax.pos)
in ((uu____3977), (pats1)))
in ((xs5), (uu____3966), (body4)))
in FStar_Parser_AST.QForall (uu____3947))
in (mk1 uu____3946))
end
| uu____3998 -> begin
(

let uu____4000 = (

let uu____4001 = (

let uu____4020 = (

let uu____4031 = (FStar_Parser_AST.idents_of_binders xs5 t.FStar_Syntax_Syntax.pos)
in ((uu____4031), (pats1)))
in ((xs5), (uu____4020), (body4)))
in FStar_Parser_AST.QExists (uu____4001))
in (mk1 uu____4000))
end))
end))
end))))
end))
end
| uu____4052 -> begin
(match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____4056 = (

let uu____4057 = (

let uu____4076 = (resugar_term' env body)
in (([]), ((([]), ([]))), (uu____4076)))
in FStar_Parser_AST.QForall (uu____4057))
in (mk1 uu____4056))
end
| uu____4097 -> begin
(

let uu____4099 = (

let uu____4100 = (

let uu____4119 = (resugar_term' env body)
in (([]), ((([]), ([]))), (uu____4119)))
in FStar_Parser_AST.QExists (uu____4100))
in (mk1 uu____4099))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____4158))::[] -> begin
(resugar b)
end
| uu____4175 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____4185 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____4187) -> begin
(

let uu____4195 = (FStar_List.hd args1)
in (match (uu____4195) with
| (e1, uu____4209) -> begin
(resugar_term' env e1)
end))
end
| FStar_Pervasives_Native.Some (op, expected_arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____4281 -> (match (uu____4281) with
| (e1, qual) -> begin
(

let uu____4298 = (resugar_term' env e1)
in (

let uu____4299 = (resugar_imp env qual)
in ((uu____4298), (uu____4299))))
end)))))
in (match (expected_arity) with
| FStar_Pervasives_Native.None -> begin
(

let resugared_args = (resugar args1)
in (

let expect_n = (FStar_Parser_ToDocument.handleable_args_length op1)
in (match (((FStar_List.length resugared_args) >= expect_n)) with
| true -> begin
(

let uu____4315 = (FStar_Util.first_N expect_n resugared_args)
in (match (uu____4315) with
| (op_args, rest) -> begin
(

let head1 = (

let uu____4363 = (

let uu____4364 = (

let uu____4371 = (FStar_List.map FStar_Pervasives_Native.fst op_args)
in ((op1), (uu____4371)))
in FStar_Parser_AST.Op (uu____4364))
in (mk1 uu____4363))
in (FStar_List.fold_left (fun head2 uu____4389 -> (match (uu____4389) with
| (arg, qual) -> begin
(mk1 (FStar_Parser_AST.App (((head2), (arg), (qual)))))
end)) head1 rest))
end))
end
| uu____4396 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some (n1) when (Prims.op_Equality (FStar_List.length args1) n1) -> begin
(

let uu____4408 = (

let uu____4409 = (

let uu____4416 = (

let uu____4419 = (resugar args1)
in (FStar_List.map FStar_Pervasives_Native.fst uu____4419))
in ((op1), (uu____4416)))
in FStar_Parser_AST.Op (uu____4409))
in (mk1 uu____4408))
end
| uu____4432 -> begin
(resugar_as_app e args1)
end)))
end))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, wopt, t1))::[]) -> begin
(

let uu____4501 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (t1)))
in (match (uu____4501) with
| (pat1, wopt1, t2) -> begin
(

let branch_bv = (FStar_Syntax_Free.names t2)
in (

let bnds = (

let uu____4547 = (

let uu____4560 = (

let uu____4565 = (resugar_pat' env pat1 branch_bv)
in (

let uu____4566 = (resugar_term' env e)
in ((uu____4565), (uu____4566))))
in ((FStar_Pervasives_Native.None), (uu____4560)))
in (uu____4547)::[])
in (

let body = (resugar_term' env t2)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body))))))))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____4618, t1))::((pat2, uu____4621, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____4717 = (

let uu____4718 = (

let uu____4725 = (resugar_term' env e)
in (

let uu____4726 = (resugar_term' env t1)
in (

let uu____4727 = (resugar_term' env t2)
in ((uu____4725), (uu____4726), (uu____4727)))))
in FStar_Parser_AST.If (uu____4718))
in (mk1 uu____4717))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____4793 -> (match (uu____4793) with
| (pat, wopt, b) -> begin
(

let uu____4835 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (b)))
in (match (uu____4835) with
| (pat1, wopt1, b1) -> begin
(

let branch_bv = (FStar_Syntax_Free.names b1)
in (

let pat2 = (resugar_pat' env pat1 branch_bv)
in (

let wopt2 = (match (wopt1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____4887 = (resugar_term' env e1)
in FStar_Pervasives_Native.Some (uu____4887))
end)
in (

let b2 = (resugar_term' env b1)
in ((pat2), (wopt2), (b2))))))
end))
end))
in (

let uu____4891 = (

let uu____4892 = (

let uu____4907 = (resugar_term' env e)
in (

let uu____4908 = (FStar_List.map resugar_branch branches)
in ((uu____4907), (uu____4908))))
in FStar_Parser_AST.Match (uu____4892))
in (mk1 uu____4891)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____4954) -> begin
(

let term = (match (asc) with
| FStar_Util.Inl (n1) -> begin
(resugar_term' env n1)
end
| FStar_Util.Inr (n1) -> begin
(resugar_comp' env n1)
end)
in (

let tac_opt1 = (FStar_Option.map (resugar_term' env) tac_opt)
in (

let uu____5023 = (

let uu____5024 = (

let uu____5033 = (resugar_term' env e)
in ((uu____5033), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____5024))
in (mk1 uu____5023))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____5062 = (FStar_Syntax_Subst.open_let_rec source_lbs body)
in (match (uu____5062) with
| (source_lbs1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let attrs_opt = (match (bnd.FStar_Syntax_Syntax.lbattrs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| tms -> begin
(

let uu____5116 = (FStar_List.map (resugar_term' env) tms)
in FStar_Pervasives_Native.Some (uu____5116))
end)
in (

let uu____5123 = (

let uu____5128 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____5128))
in (match (uu____5123) with
| (univs1, td) -> begin
(

let uu____5148 = (

let uu____5155 = (

let uu____5156 = (FStar_Syntax_Subst.compress td)
in uu____5156.FStar_Syntax_Syntax.n)
in (match (uu____5155) with
| FStar_Syntax_Syntax.Tm_app (uu____5165, ((t1, uu____5167))::((d, uu____5169))::[]) -> begin
((t1), (d))
end
| uu____5226 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____5148) with
| (typ, def) -> begin
(

let uu____5257 = (

let uu____5273 = (

let uu____5274 = (FStar_Syntax_Subst.compress def)
in uu____5274.FStar_Syntax_Syntax.n)
in (match (uu____5273) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____5294) -> begin
(

let uu____5319 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____5319) with
| (b1, t2) -> begin
(

let b2 = (

let uu____5350 = (FStar_Options.print_implicits ())
in (match (uu____5350) with
| true -> begin
b1
end
| uu____5361 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____5373 -> begin
(([]), (def), (false))
end))
in (match (uu____5257) with
| (binders, term, is_pat_app) -> begin
(

let uu____5428 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____5439 = (

let uu____5440 = (

let uu____5441 = (

let uu____5448 = (bv_as_unique_ident bv)
in ((uu____5448), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____5441))
in (mk_pat uu____5440))
in ((uu____5439), (term)))
end)
in (match (uu____5428) with
| (pat, term1) -> begin
(

let uu____5470 = (match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders ((map_opt ()) (fun uu____5513 -> (match (uu____5513) with
| (bv, q) -> begin
(

let uu____5528 = (resugar_arg_qual env q)
in (FStar_Util.map_opt uu____5528 (fun q1 -> (

let uu____5540 = (

let uu____5541 = (

let uu____5548 = (bv_as_unique_ident bv)
in ((uu____5548), (q1)))
in FStar_Parser_AST.PatVar (uu____5541))
in (mk_pat uu____5540)))))
end))))
in (

let uu____5551 = (

let uu____5556 = (resugar_term' env term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____5556)))
in (

let uu____5559 = (universe_to_string univs1)
in ((uu____5551), (uu____5559)))))
end
| uu____5566 -> begin
(

let uu____5568 = (

let uu____5573 = (resugar_term' env term1)
in ((pat), (uu____5573)))
in (

let uu____5574 = (universe_to_string univs1)
in ((uu____5568), (uu____5574))))
end)
in ((attrs_opt), (uu____5470)))
end))
end))
end))
end))))
in (

let r = (FStar_List.map resugar_one_binding source_lbs1)
in (

let bnds = (

let f = (fun uu____5680 -> (match (uu____5680) with
| (attrs, (pb, univs1)) -> begin
(

let uu____5740 = (

let uu____5742 = (FStar_Options.print_universes ())
in (not (uu____5742)))
in (match (uu____5740) with
| true -> begin
((attrs), (pb))
end
| uu____5765 -> begin
((attrs), ((((FStar_Pervasives_Native.fst pb)), ((label univs1 (FStar_Pervasives_Native.snd pb))))))
end))
end))
in (FStar_List.map f r))
in (

let body2 = (resugar_term' env body1)
in (mk1 (FStar_Parser_AST.Let ((((match (is_rec) with
| true -> begin
FStar_Parser_AST.Rec
end
| uu____5820 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____5823) -> begin
(

let s = (

let uu____5842 = (

let uu____5844 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____5844 FStar_Util.string_of_int))
in (Prims.op_Hat "?u" uu____5842))
in (

let uu____5849 = (mk1 FStar_Parser_AST.Wild)
in (label s uu____5849)))
end
| FStar_Syntax_Syntax.Tm_quoted (tm, qi) -> begin
(

let qi1 = (match (qi.FStar_Syntax_Syntax.qkind) with
| FStar_Syntax_Syntax.Quote_static -> begin
FStar_Parser_AST.Static
end
| FStar_Syntax_Syntax.Quote_dynamic -> begin
FStar_Parser_AST.Dynamic
end)
in (

let uu____5857 = (

let uu____5858 = (

let uu____5863 = (resugar_term' env tm)
in ((uu____5863), (qi1)))
in FStar_Parser_AST.Quote (uu____5858))
in (mk1 uu____5857)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___5_5875 -> (match (uu___5_5875) with
| FStar_Syntax_Syntax.Sequence -> begin
(

let term = (resugar_term' env e)
in (

let rec resugar_seq = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (uu____5883, ((uu____5884, (p, t11)))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____5945 = (

let uu____5946 = (

let uu____5955 = (resugar_seq t11)
in ((uu____5955), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____5946))
in (mk1 uu____5945))
end
| uu____5958 -> begin
t1
end))
in (resugar_seq term)))
end
| FStar_Syntax_Syntax.Primop -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Masked_effect -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Meta_smt_pat -> begin
(resugar_term' env e)
end))
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____5959, pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____6023 -> (match (uu____6023) with
| (x, uu____6031) -> begin
(resugar_term' env x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____6036) -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Meta_desugared (i) -> begin
(resugar_meta_desugared i)
end
| FStar_Syntax_Syntax.Meta_named (t1) -> begin
(mk1 (FStar_Parser_AST.Name (t1)))
end
| FStar_Syntax_Syntax.Meta_monadic (name1, t1) -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____6054, t1) -> begin
(resugar_term' env e)
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(mk1 FStar_Parser_AST.Wild)
end)))))
and resugar_comp' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Parser_AST.term = (fun env c -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let t = (resugar_term' env typ)
in (match (u) with
| FStar_Pervasives_Native.None -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end
| FStar_Pervasives_Native.Some (u1) -> begin
(

let uu____6094 = (FStar_Options.print_universes ())
in (match (uu____6094) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____6116 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let t = (resugar_term' env typ)
in (match (u) with
| FStar_Pervasives_Native.None -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end
| FStar_Pervasives_Native.Some (u1) -> begin
(

let uu____6158 = (FStar_Options.print_universes ())
in (match (uu____6158) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____6180 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____6202 = (resugar_term' env c1.FStar_Syntax_Syntax.result_typ)
in ((uu____6202), (FStar_Parser_AST.Nothing)))
in (

let uu____6203 = ((FStar_Options.print_effect_args ()) || (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid))
in (match (uu____6203) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (

let uu____6226 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____6226) with
| true -> begin
(match (c1.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::(pats)::[] -> begin
(

let post1 = (

let uu____6311 = (FStar_Syntax_Util.unthunk_lemma_post (FStar_Pervasives_Native.fst post))
in ((uu____6311), ((FStar_Pervasives_Native.snd post))))
in (

let uu____6322 = (

let uu____6331 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid (FStar_Pervasives_Native.fst pre))
in (match (uu____6331) with
| true -> begin
[]
end
| uu____6352 -> begin
(pre)::[]
end))
in (

let uu____6366 = (

let uu____6375 = (

let uu____6384 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid (FStar_Pervasives_Native.fst pats))
in (match (uu____6384) with
| true -> begin
[]
end
| uu____6405 -> begin
(pats)::[]
end))
in (FStar_List.append ((post1)::[]) uu____6375))
in (FStar_List.append uu____6322 uu____6366))))
end
| uu____6443 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
end
| uu____6454 -> begin
c1.FStar_Syntax_Syntax.effect_args
end))
in (

let args1 = (FStar_List.map (fun uu____6477 -> (match (uu____6477) with
| (e, uu____6489) -> begin
(

let uu____6494 = (resugar_term' env e)
in ((uu____6494), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___6_6519 -> (match (uu___6_6519) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____6552 = (resugar_term' env e)
in ((uu____6552), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____6557 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____6583 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun env b r -> (

let uu____6604 = b
in (match (uu____6604) with
| (x, aq) -> begin
(

let uu____6613 = (resugar_arg_qual env aq)
in (FStar_Util.map_opt uu____6613 (fun imp -> (

let e = (resugar_term' env x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____6627 = (

let uu____6628 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____6628))
in (FStar_Parser_AST.mk_binder uu____6627 r FStar_Parser_AST.Type_level imp))
end
| uu____6629 -> begin
(

let uu____6630 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____6630) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____6633 -> begin
(

let uu____6635 = (

let uu____6636 = (

let uu____6641 = (bv_as_unique_ident x)
in ((uu____6641), (e)))
in FStar_Parser_AST.Annotated (uu____6636))
in (FStar_Parser_AST.mk_binder uu____6635 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Parser_AST.pattern = (fun env v1 aqual body_bv typ_opt -> (

let mk1 = (fun a -> (

let uu____6661 = (FStar_Syntax_Syntax.range_of_bv v1)
in (FStar_Parser_AST.mk_pattern a uu____6661)))
in (

let used = (FStar_Util.set_mem v1 body_bv)
in (

let pat = (

let uu____6665 = (match (used) with
| true -> begin
(

let uu____6667 = (

let uu____6674 = (bv_as_unique_ident v1)
in ((uu____6674), (aqual)))
in FStar_Parser_AST.PatVar (uu____6667))
end
| uu____6677 -> begin
FStar_Parser_AST.PatWild (aqual)
end)
in (mk1 uu____6665))
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
pat
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____6681; FStar_Syntax_Syntax.vars = uu____6682}) -> begin
pat
end
| FStar_Pervasives_Native.Some (typ) -> begin
(

let uu____6692 = (FStar_Options.print_bound_var_types ())
in (match (uu____6692) with
| true -> begin
(

let uu____6695 = (

let uu____6696 = (

let uu____6707 = (

let uu____6714 = (resugar_term' env typ)
in ((uu____6714), (FStar_Pervasives_Native.None)))
in ((pat), (uu____6707)))
in FStar_Parser_AST.PatAscribed (uu____6696))
in (mk1 uu____6695))
end
| uu____6723 -> begin
pat
end))
end)))))
and resugar_bv_as_pat : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun env x qual body_bv -> (

let uu____6735 = (resugar_arg_qual env qual)
in (FStar_Util.map_opt uu____6735 (fun aqual -> (

let uu____6747 = (

let uu____6752 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_left (fun _6763 -> FStar_Pervasives_Native.Some (_6763)) uu____6752))
in (resugar_bv_as_pat' env x aqual body_bv uu____6747))))))
and resugar_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun env p branch_bv -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p))
in (

let to_arg_qual = (fun bopt -> (FStar_Util.bind_opt bopt (fun b -> (match (b) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)
end
| uu____6796 -> begin
FStar_Pervasives_Native.None
end))))
in (

let may_drop_implicits = (fun args -> ((

let uu____6825 = (FStar_Options.print_implicits ())
in (not (uu____6825))) && (

let uu____6828 = (FStar_List.existsML (fun uu____6841 -> (match (uu____6841) with
| (pattern, is_implicit1) -> begin
(

let might_be_used = (match (pattern.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, uu____6863) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_wild (uu____6868) -> begin
false
end
| uu____6870 -> begin
true
end)
in (is_implicit1 && might_be_used))
end)) args)
in (not (uu____6828)))))
in (

let resugar_plain_pat_cons' = (fun fv args -> (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args))))))
in (

let rec resugar_plain_pat_cons = (fun fv args -> (

let args1 = (

let uu____6938 = (may_drop_implicits args)
in (match (uu____6938) with
| true -> begin
(filter_pattern_imp args)
end
| uu____6950 -> begin
args
end))
in (

let args2 = (FStar_List.map (fun uu____6963 -> (match (uu____6963) with
| (p1, b) -> begin
(aux p1 (FStar_Pervasives_Native.Some (b)))
end)) args1)
in (resugar_plain_pat_cons' fv args2))))
and aux = (fun p1 imp_opt -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(mk1 (FStar_Parser_AST.PatConst (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, []) -> begin
(mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.nil_lid) && (may_drop_implicits args)) -> begin
((

let uu____7018 = (

let uu____7020 = (

let uu____7022 = (filter_pattern_imp args)
in (FStar_List.isEmpty uu____7022))
in (not (uu____7020)))
in (match (uu____7018) with
| true -> begin
(FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p ((FStar_Errors.Warning_NilGivenExplicitArgs), ("Prims.Nil given explicit arguments")))
end
| uu____7044 -> begin
()
end));
(mk1 (FStar_Parser_AST.PatList ([])));
)
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.cons_lid) && (may_drop_implicits args)) -> begin
(

let uu____7066 = (filter_pattern_imp args)
in (match (uu____7066) with
| ((hd1, false))::((tl1, false))::[] -> begin
(

let hd' = (aux hd1 (FStar_Pervasives_Native.Some (false)))
in (

let uu____7116 = (aux tl1 (FStar_Pervasives_Native.Some (false)))
in (match (uu____7116) with
| {FStar_Parser_AST.pat = FStar_Parser_AST.PatList (tl'); FStar_Parser_AST.prange = p2} -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatList ((hd')::tl')) p2)
end
| tl' -> begin
(resugar_plain_pat_cons' fv ((hd')::(tl')::[]))
end)))
end
| args' -> begin
((

let uu____7135 = (

let uu____7141 = (

let uu____7143 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args'))
in (FStar_Util.format1 "Prims.Cons applied to %s explicit arguments" uu____7143))
in ((FStar_Errors.Warning_ConsAppliedExplicitArgs), (uu____7141)))
in (FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p uu____7135));
(resugar_plain_pat_cons fv args);
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((is_tuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) && (may_drop_implicits args)) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.filter_map (fun uu____7196 -> (match (uu____7196) with
| (p2, is_implicit1) -> begin
(match (is_implicit1) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7211 -> begin
(

let uu____7213 = (aux p2 (FStar_Pervasives_Native.Some (false)))
in FStar_Pervasives_Native.Some (uu____7213))
end)
end))))
in (

let is_dependent_tuple = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mk1 (FStar_Parser_AST.PatTuple (((args1), (is_dependent_tuple)))))))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____7221; FStar_Syntax_Syntax.fv_delta = uu____7222; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____7251 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____7251 FStar_List.rev))
in (

let args1 = (

let uu____7267 = (FStar_All.pipe_right args (FStar_List.map (fun uu____7287 -> (match (uu____7287) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____7267 FStar_List.rev))
in (

let rec map21 = (fun l1 l2 -> (match (((l1), (l2))) with
| ([], []) -> begin
[]
end
| ([], (hd1)::tl1) -> begin
[]
end
| ((hd1)::tl1, []) -> begin
(

let uu____7365 = (map21 tl1 [])
in (((hd1), ((mk1 (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None))))))::uu____7365)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____7388 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____7388)
end))
in (

let args2 = (

let uu____7406 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____7406 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(resugar_plain_pat_cons fv args)
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____7450 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____7450) with
| FStar_Pervasives_Native.Some (op, uu____7462) -> begin
(

let uu____7479 = (

let uu____7480 = (FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in FStar_Parser_AST.PatOp (uu____7480))
in (mk1 uu____7479))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7490 = (to_arg_qual imp_opt)
in (resugar_bv_as_pat' env v1 uu____7490 branch_bv FStar_Pervasives_Native.None))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____7495) -> begin
(

let uu____7496 = (

let uu____7497 = (to_arg_qual imp_opt)
in FStar_Parser_AST.PatWild (uu____7497))
in (mk1 uu____7496))
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, term) -> begin
(resugar_bv_as_pat' env bv (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) branch_bv (FStar_Pervasives_Native.Some (term)))
end))
in (aux p FStar_Pervasives_Native.None)))))))
and resugar_arg_qual : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option FStar_Pervasives_Native.option = (fun env q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7528 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
end)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____7537 = (

let uu____7540 = (

let uu____7541 = (resugar_term' env t)
in FStar_Parser_AST.Meta (uu____7541))
in FStar_Pervasives_Native.Some (uu____7540))
in FStar_Pervasives_Native.Some (uu____7537))
end))
and resugar_imp : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.imp = (fun env q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Parser_AST.Nothing
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
FStar_Parser_AST.Hash
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Parser_AST.Nothing
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
FStar_Parser_AST.Nothing
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____7553 = (resugar_term' env t)
in FStar_Parser_AST.HashBrace (uu____7553))
end))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___7_7561 -> (match (uu___7_7561) with
| FStar_Syntax_Syntax.Assumption -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Assumption)
end
| FStar_Syntax_Syntax.New -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.New)
end
| FStar_Syntax_Syntax.Private -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Private)
end
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Unfold_for_unification_and_vcgen)
end
| FStar_Syntax_Syntax.Visible_default -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Irreducible -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Irreducible)
end
| FStar_Syntax_Syntax.Abstract -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Abstract)
end
| FStar_Syntax_Syntax.Inline_for_extraction -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Inline_for_extraction)
end
| FStar_Syntax_Syntax.NoExtract -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.NoExtract)
end
| FStar_Syntax_Syntax.Noeq -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Noeq)
end
| FStar_Syntax_Syntax.Unopteq -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Unopteq)
end
| FStar_Syntax_Syntax.TotalEffect -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.TotalEffect)
end
| FStar_Syntax_Syntax.Logic -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reifiable)
end
| FStar_Syntax_Syntax.Reflectable (uu____7568) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____7569) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____7570) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____7575) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7584) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____7593) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.ExceptionConstructor -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Effect -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Effect_qual)
end
| FStar_Syntax_Syntax.OnlyName -> begin
FStar_Pervasives_Native.None
end))


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___8_7599 -> (match (uu___8_7599) with
| FStar_Syntax_Syntax.SetOptions (s) -> begin
FStar_Parser_AST.SetOptions (s)
end
| FStar_Syntax_Syntax.ResetOptions (s) -> begin
FStar_Parser_AST.ResetOptions (s)
end
| FStar_Syntax_Syntax.PushOptions (s) -> begin
FStar_Parser_AST.PushOptions (s)
end
| FStar_Syntax_Syntax.PopOptions -> begin
FStar_Parser_AST.PopOptions
end
| FStar_Syntax_Syntax.LightOff -> begin
FStar_Parser_AST.LightOff
end))


let resugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon) = (fun env datacon_ses se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____7642, datacons) -> begin
(

let uu____7652 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____7680, uu____7681, uu____7682, inductive_lid, uu____7684, uu____7685) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____7692 -> begin
(failwith "unexpected")
end))))
in (match (uu____7652) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____7713 = (FStar_Options.print_implicits ())
in (match (uu____7713) with
| true -> begin
bs
end
| uu____7718 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____7730 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___9_7737 -> (match (uu___9_7737) with
| FStar_Syntax_Syntax.RecordType (uu____7739) -> begin
true
end
| uu____7749 -> begin
false
end))))
in (match (uu____7730) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____7803, univs1, term, uu____7806, num, uu____7808) -> begin
(

let uu____7815 = (

let uu____7816 = (FStar_Syntax_Subst.compress term)
in uu____7816.FStar_Syntax_Syntax.n)
in (match (uu____7815) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____7830) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____7899 -> (match (uu____7899) with
| (b, qual) -> begin
(

let uu____7920 = (bv_as_unique_ident b)
in (

let uu____7921 = (resugar_term' env b.FStar_Syntax_Syntax.sort)
in ((uu____7920), (uu____7921), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____7932 -> begin
(failwith "unexpected")
end))
end
| uu____7944 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____7999 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____8075, num, uu____8077) -> begin
(

let c = (

let uu____8098 = (

let uu____8101 = (resugar_term' env term)
in FStar_Pervasives_Native.Some (uu____8101))
in ((l.FStar_Ident.ident), (uu____8098), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____8121 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____8201 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____8227 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____8227; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme'' : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env name ts -> (

let uu____8257 = ts
in (match (uu____8257) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____8270 = (

let uu____8271 = (

let uu____8288 = (

let uu____8297 = (

let uu____8304 = (

let uu____8305 = (

let uu____8318 = (resugar_term' env typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____8318)))
in FStar_Parser_AST.TyconAbbrev (uu____8305))
in ((uu____8304), (FStar_Pervasives_Native.None)))
in (uu____8297)::[])
in ((false), (false), (uu____8288)))
in FStar_Parser_AST.Tycon (uu____8271))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8270)))
end)))


let resugar_tscheme' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env ts -> (resugar_tscheme'' env "tscheme" ts))


let resugar_eff_decl' : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun env for_free r q ed -> (

let resugar_action = (fun d for_free1 -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____8407 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____8407) with
| (bs, action_defn) -> begin
(

let uu____8414 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____8414) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____8424 = (FStar_Options.print_implicits ())
in (match (uu____8424) with
| true -> begin
action_params
end
| uu____8429 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____8434 = (FStar_All.pipe_right action_params1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____8434 FStar_List.rev))
in (

let action_defn1 = (resugar_term' env action_defn)
in (

let action_typ1 = (resugar_term' env action_typ)
in (match (for_free1) with
| true -> begin
(

let a = (

let uu____8451 = (

let uu____8462 = (FStar_Ident.lid_of_str "construct")
in ((uu____8462), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____8451))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), (false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____8513 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), (false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____8546 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____8546) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____8556 = (FStar_Options.print_implicits ())
in (match (uu____8556) with
| true -> begin
eff_binders
end
| uu____8561 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____8566 = (FStar_All.pipe_right eff_binders1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____8566 FStar_List.rev))
in (

let eff_typ1 = (resugar_term' env eff_typ)
in (

let ret_wp = (resugar_tscheme'' env "ret_wp" ed.FStar_Syntax_Syntax.ret_wp)
in (

let bind_wp = (resugar_tscheme'' env "bind_wp" ed.FStar_Syntax_Syntax.bind_wp)
in (

let if_then_else1 = (resugar_tscheme'' env "if_then_else" ed.FStar_Syntax_Syntax.if_then_else)
in (

let ite_wp = (resugar_tscheme'' env "ite_wp" ed.FStar_Syntax_Syntax.ite_wp)
in (

let stronger = (resugar_tscheme'' env "stronger" ed.FStar_Syntax_Syntax.stronger)
in (

let close_wp = (resugar_tscheme'' env "close_wp" ed.FStar_Syntax_Syntax.close_wp)
in (

let assert_p = (resugar_tscheme'' env "assert_p" ed.FStar_Syntax_Syntax.assert_p)
in (

let assume_p = (resugar_tscheme'' env "assume_p" ed.FStar_Syntax_Syntax.assume_p)
in (

let null_wp = (resugar_tscheme'' env "null_wp" ed.FStar_Syntax_Syntax.null_wp)
in (

let trivial = (resugar_tscheme'' env "trivial" ed.FStar_Syntax_Syntax.trivial)
in (

let repr = (resugar_tscheme'' env "repr" (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let return_repr = (resugar_tscheme'' env "return_repr" ed.FStar_Syntax_Syntax.return_repr)
in (

let bind_repr = (resugar_tscheme'' env "bind_repr" ed.FStar_Syntax_Syntax.bind_repr)
in (

let mandatory_members_decls = (match (for_free) with
| true -> begin
(repr)::(return_repr)::(bind_repr)::[]
end
| uu____8616 -> begin
(repr)::(return_repr)::(bind_repr)::(ret_wp)::(bind_wp)::(if_then_else1)::(ite_wp)::(stronger)::(close_wp)::(assert_p)::(assume_p)::(null_wp)::(trivial)::[]
end)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls)))))))))))))))))))))))))
end)))))


let resugar_sigelt' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8651) -> begin
(

let uu____8660 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8683) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____8701) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____8709) -> begin
false
end
| uu____8726 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____8660) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____8764 se1 -> (match (uu____8764) with
| (datacon_ses1, tycons) -> begin
(

let uu____8790 = (resugar_typ env datacon_ses1 se1)
in (match (uu____8790) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____8805 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____8805) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____8840 = (

let uu____8841 = (

let uu____8842 = (

let uu____8859 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (false), (uu____8859)))
in FStar_Parser_AST.Tycon (uu____8842))
in (decl'_to_decl se uu____8841))
in FStar_Pervasives_Native.Some (uu____8840))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____8894, uu____8895, uu____8896, uu____8897, uu____8898) -> begin
(

let uu____8905 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____8905))
end
| uu____8908 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____8912 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____8919) -> begin
(

let uu____8924 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___10_8932 -> (match (uu___10_8932) with
| FStar_Syntax_Syntax.Projector (uu____8934, uu____8935) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____8937) -> begin
true
end
| uu____8939 -> begin
false
end))))
in (match (uu____8924) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8944 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term' env desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____8974) -> begin
(

let uu____9003 = (

let uu____9004 = (

let uu____9005 = (

let uu____9016 = (FStar_List.map FStar_Pervasives_Native.snd lets)
in ((isrec), (uu____9016)))
in FStar_Parser_AST.TopLevelLet (uu____9005))
in (decl'_to_decl se uu____9004))
in FStar_Pervasives_Native.Some (uu____9003))
end
| uu____9053 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____9058, fml) -> begin
(

let uu____9060 = (

let uu____9061 = (

let uu____9062 = (

let uu____9067 = (resugar_term' env fml)
in ((lid.FStar_Ident.ident), (uu____9067)))
in FStar_Parser_AST.Assume (uu____9062))
in (decl'_to_decl se uu____9061))
in FStar_Pervasives_Native.Some (uu____9060))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____9069 = (resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____9069))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let uu____9072 = (resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____9072))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____9082, t) -> begin
(

let uu____9092 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____9092))
end
| uu____9093 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____9101, t) -> begin
(

let uu____9111 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____9111))
end
| uu____9112 -> begin
FStar_Pervasives_Native.None
end)
in (

let op = (match (((lift_wp), (lift))) with
| (FStar_Pervasives_Native.Some (t), FStar_Pervasives_Native.None) -> begin
FStar_Parser_AST.NonReifiableLift (t)
end
| (FStar_Pervasives_Native.Some (wp), FStar_Pervasives_Native.Some (t)) -> begin
FStar_Parser_AST.ReifiableLift (((wp), (t)))
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (t)) -> begin
FStar_Parser_AST.LiftForFree (t)
end
| uu____9136 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____9146 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____9146)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) -> begin
(

let uu____9156 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9156) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____9168 = (FStar_Options.print_implicits ())
in (match (uu____9168) with
| true -> begin
bs1
end
| uu____9173 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 ((map_opt ()) (fun b -> (resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____9184 = (

let uu____9185 = (

let uu____9186 = (

let uu____9203 = (

let uu____9212 = (

let uu____9219 = (

let uu____9220 = (

let uu____9233 = (resugar_comp' env c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____9233)))
in FStar_Parser_AST.TyconAbbrev (uu____9220))
in ((uu____9219), (FStar_Pervasives_Native.None)))
in (uu____9212)::[])
in ((false), (false), (uu____9203)))
in FStar_Parser_AST.Tycon (uu____9186))
in (decl'_to_decl se uu____9185))
in FStar_Pervasives_Native.Some (uu____9184))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____9265 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____9265))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____9269 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___11_9277 -> (match (uu___11_9277) with
| FStar_Syntax_Syntax.Projector (uu____9279, uu____9280) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____9282) -> begin
true
end
| uu____9284 -> begin
false
end))))
in (match (uu____9269) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9289 -> begin
(

let t' = (

let uu____9292 = ((

let uu____9296 = (FStar_Options.print_universes ())
in (not (uu____9296))) || (FStar_List.isEmpty uvs))
in (match (uu____9292) with
| true -> begin
(resugar_term' env t)
end
| uu____9299 -> begin
(

let uu____9301 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____9301) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____9310 = (resugar_term' env t1)
in (label universes uu____9310)))
end))
end))
in (

let uu____9311 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____9311)))
end))
end
| FStar_Syntax_Syntax.Sig_splice (ids, t) -> begin
(

let uu____9318 = (

let uu____9319 = (

let uu____9320 = (

let uu____9327 = (FStar_List.map (fun l -> l.FStar_Ident.ident) ids)
in (

let uu____9332 = (resugar_term' env t)
in ((uu____9327), (uu____9332))))
in FStar_Parser_AST.Splice (uu____9320))
in (decl'_to_decl se uu____9319))
in FStar_Pervasives_Native.Some (uu____9318))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9335) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9352) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____9368) -> begin
FStar_Pervasives_Native.None
end))


let empty_env : FStar_Syntax_DsEnv.env = (FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps)


let noenv : 'a . (FStar_Syntax_DsEnv.env  ->  'a)  ->  'a = (fun f -> (f empty_env))


let resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____9392 = (noenv resugar_term')
in (uu____9392 t)))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (

let uu____9410 = (noenv resugar_sigelt')
in (uu____9410 se)))


let resugar_comp : FStar_Syntax_Syntax.comp  ->  FStar_Parser_AST.term = (fun c -> (

let uu____9428 = (noenv resugar_comp')
in (uu____9428 c)))


let resugar_pat : FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun p branch_bv -> (

let uu____9451 = (noenv resugar_pat')
in (uu____9451 p branch_bv)))


let resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____9485 = (noenv resugar_binder')
in (uu____9485 b r)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (

let uu____9510 = (noenv resugar_tscheme')
in (uu____9510 ts)))


let resugar_eff_decl : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun for_free r q ed -> (

let uu____9545 = (noenv resugar_eff_decl')
in (uu____9545 for_free r q ed)))





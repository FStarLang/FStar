
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


let rec resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____327) -> begin
(

let uu____328 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____328) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____339 = (

let uu____340 = (

let uu____341 = (

let uu____353 = (FStar_Util.string_of_int n1)
in ((uu____353), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____341))
in FStar_Parser_AST.Const (uu____340))
in (mk1 uu____339 r))
end
| uu____366 -> begin
(

let e1 = (

let uu____368 = (

let uu____369 = (

let uu____370 = (

let uu____382 = (FStar_Util.string_of_int n1)
in ((uu____382), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____370))
in FStar_Parser_AST.Const (uu____369))
in (mk1 uu____368 r))
in (

let e2 = (resugar_universe u1 r)
in (

let uu____396 = (

let uu____397 = (

let uu____404 = (FStar_Ident.id_of_text "+")
in ((uu____404), ((e1)::(e2)::[])))
in FStar_Parser_AST.Op (uu____397))
in (mk1 uu____396 r))))
end)
end))
end
| FStar_Syntax_Syntax.U_max (l) -> begin
(match (l) with
| [] -> begin
(failwith "Impossible: U_max without arguments")
end
| uu____412 -> begin
(

let t = (

let uu____416 = (

let uu____417 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____417))
in (mk1 uu____416 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____426 = (

let uu____427 = (

let uu____434 = (resugar_universe x r)
in ((acc), (uu____434), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____427))
in (mk1 uu____426 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____436) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id1 = (

let uu____448 = (

let uu____454 = (

let uu____456 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____456))
in ((uu____454), (r)))
in (FStar_Ident.mk_ident uu____448))
in (mk1 (FStar_Parser_AST.Uvar (id1)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let resugar_universe' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun env u r -> (resugar_universe u r))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___1_510 -> (match (uu___1_510) with
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
| uu____838 -> begin
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
| uu____978 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____996 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____996 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____1014 -> begin
(

let maybeop = (

let uu____1022 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (acc) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (acc1) -> begin
(match (x) with
| FStar_Pervasives_Native.Some (op, uu____1088) -> begin
FStar_Pervasives_Native.Some ((Prims.op_Hat acc1 op))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)
end)) (FStar_Pervasives_Native.Some ("")) uu____1022))
in (FStar_Util.map_opt maybeop (fun o -> ((o), (FStar_Pervasives_Native.None)))))
end))
end
| uu____1134 -> begin
FStar_Pervasives_Native.None
end)
end)))


type expected_arity =
Prims.int FStar_Pervasives_Native.option


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * expected_arity) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____1420 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____1420) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), (FStar_Pervasives_Native.None)))
end
| uu____1490 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1505 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), (FStar_Pervasives_Native.None)))
end
| uu____1534 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), (FStar_Pervasives_Native.None)))
end
| uu____1562 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), (FStar_Pervasives_Native.None)))
end
| uu____1590 -> begin
(

let uu____1592 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____1592) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), (FStar_Pervasives_Native.None)))
end
| uu____1618 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____1628 = (

let uu____1629 = (FStar_Syntax_Subst.compress t)
in uu____1629.FStar_Syntax_Syntax.n)
in (match (uu____1628) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1647 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____1650 = (string_to_op s)
in (match (uu____1650) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____1690 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____1707 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____1724 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____1735) -> begin
true
end
| uu____1737 -> begin
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
| uu____1758 -> begin
(

let uu____1760 = (is_tuple_constructor_lid lid)
in (not (uu____1760)))
end))


let maybe_shorten_fv : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Ident.lident = (fun env fv -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____1774 = (may_shorten lid)
in (match (uu____1774) with
| true -> begin
(FStar_Syntax_DsEnv.shorten_lid env lid)
end
| uu____1777 -> begin
lid
end))))


let rec resugar_term' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun env t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____1919 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____1919)))
in (

let uu____1922 = (

let uu____1923 = (FStar_Syntax_Subst.compress t)
in uu____1923.FStar_Syntax_Syntax.n)
in (match (uu____1922) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1926) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1951 = (FStar_Syntax_Util.unfold_lazy i)
in (resugar_term' env uu____1951))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____1954 = (

let uu____1957 = (bv_as_unique_ident x)
in (uu____1957)::[])
in (FStar_Ident.lid_of_ids uu____1954))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____1960 = (

let uu____1963 = (bv_as_unique_ident x)
in (uu____1963)::[])
in (FStar_Ident.lid_of_ids uu____1960))
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
| uu____1973 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.op_Hat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____1982 = (

let uu____1983 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____1983))
in (mk1 uu____1982)))
end
| uu____1986 -> begin
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
| uu____2007 -> begin
(failwith "wrong projector format")
end)))
end
| uu____2012 -> begin
(

let uu____2014 = (FStar_Ident.lid_equals a FStar_Parser_Const.smtpat_lid)
in (match (uu____2014) with
| true -> begin
(

let uu____2017 = (

let uu____2018 = (

let uu____2019 = (

let uu____2025 = (FStar_Ident.range_of_lid a)
in (("SMTPat"), (uu____2025)))
in (FStar_Ident.mk_ident uu____2019))
in FStar_Parser_AST.Tvar (uu____2018))
in (mk1 uu____2017))
end
| uu____2028 -> begin
(

let uu____2030 = (FStar_Ident.lid_equals a FStar_Parser_Const.smtpatOr_lid)
in (match (uu____2030) with
| true -> begin
(

let uu____2033 = (

let uu____2034 = (

let uu____2035 = (

let uu____2041 = (FStar_Ident.range_of_lid a)
in (("SMTPatOr"), (uu____2041)))
in (FStar_Ident.mk_ident uu____2035))
in FStar_Parser_AST.Tvar (uu____2034))
in (mk1 uu____2033))
end
| uu____2044 -> begin
(

let uu____2046 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____2050 = (

let uu____2052 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____2052))
in (

let uu____2055 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____2050 uu____2055))))
in (match (uu____2046) with
| true -> begin
(

let uu____2060 = (

let uu____2061 = (maybe_shorten_fv env fv)
in FStar_Parser_AST.Var (uu____2061))
in (mk1 uu____2060))
end
| uu____2062 -> begin
(

let uu____2064 = (

let uu____2065 = (

let uu____2076 = (maybe_shorten_fv env fv)
in ((uu____2076), ([])))
in FStar_Parser_AST.Construct (uu____2065))
in (mk1 uu____2064))
end))
end))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let e1 = (resugar_term' env e)
in (

let uu____2094 = (FStar_Options.print_universes ())
in (match (uu____2094) with
| true -> begin
(

let univs1 = (FStar_List.map (fun x -> (resugar_universe x t.FStar_Syntax_Syntax.pos)) universes)
in (match (e1) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(

let args1 = (

let uu____2125 = (FStar_List.map (fun u -> ((u), (FStar_Parser_AST.UnivApp))) univs1)
in (FStar_List.append args uu____2125))
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), (args1)))) r l))
end
| uu____2148 -> begin
(FStar_List.fold_left (fun acc u -> (mk1 (FStar_Parser_AST.App (((acc), (u), (FStar_Parser_AST.UnivApp)))))) e1 univs1)
end))
end
| uu____2153 -> begin
e1
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2156 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____2156) with
| true -> begin
(

let uu____2159 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____2159))
end
| uu____2161 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____2164 = (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(("Type0"), (false))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(("Type"), (false))
end
| uu____2185 -> begin
(("Type"), (true))
end)
in (match (uu____2164) with
| (nm, needs_app) -> begin
(

let typ = (

let uu____2197 = (name nm t.FStar_Syntax_Syntax.pos)
in (mk1 uu____2197))
in (

let uu____2198 = (needs_app && (FStar_Options.print_universes ()))
in (match (uu____2198) with
| true -> begin
(

let uu____2201 = (

let uu____2202 = (

let uu____2209 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((typ), (uu____2209), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____2202))
in (mk1 uu____2201))
end
| uu____2210 -> begin
typ
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____2214) -> begin
(

let uu____2239 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____2239) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____2255 = (FStar_Options.print_implicits ())
in (match (uu____2255) with
| true -> begin
xs1
end
| uu____2266 -> begin
(filter_imp xs1)
end))
in (

let body_bv = (FStar_Syntax_Free.names body1)
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____2293 -> (match (uu____2293) with
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

let uu____2333 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____2333) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____2343 = (FStar_Options.print_implicits ())
in (match (uu____2343) with
| true -> begin
xs1
end
| uu____2348 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp' env body1)
in (

let xs3 = (

let uu____2354 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____2354 FStar_List.rev))
in (

let rec aux = (fun body3 uu___2_2379 -> (match (uu___2_2379) with
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

let uu____2395 = (

let uu____2400 = (

let uu____2401 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____2401)::[])
in (FStar_Syntax_Subst.open_term uu____2400 phi))
in (match (uu____2395) with
| (x1, phi1) -> begin
(

let b = (

let uu____2423 = (

let uu____2426 = (FStar_List.hd x1)
in (resugar_binder' env uu____2426 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____2423))
in (

let uu____2433 = (

let uu____2434 = (

let uu____2439 = (resugar_term' env phi1)
in ((b), (uu____2439)))
in FStar_Parser_AST.Refine (uu____2434))
in (mk1 uu____2433)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____2441; FStar_Syntax_Syntax.vars = uu____2442}, ((e, uu____2444))::[]) when ((

let uu____2485 = (FStar_Options.print_implicits ())
in (not (uu____2485))) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid)) -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___3_2534 -> (match (uu___3_2534) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____2604 -> begin
(failwith "last of an empty list")
end))
in (

let first_two_explicit = (fun args1 -> (

let rec drop_implicits = (fun args2 -> (match (args2) with
| ((uu____2690, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____2691))))::tl1 -> begin
(drop_implicits tl1)
end
| uu____2710 -> begin
args2
end))
in (

let uu____2719 = (drop_implicits args1)
in (match (uu____2719) with
| [] -> begin
(failwith "not_enough explicit_arguments")
end
| (uu____2751)::[] -> begin
(failwith "not_enough explicit_arguments")
end
| (a1)::(a2)::uu____2781 -> begin
(a1)::(a2)::[]
end))))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_List.map (fun uu____2881 -> (match (uu____2881) with
| (e2, qual) -> begin
(

let uu____2898 = (resugar_term' env e2)
in (

let uu____2899 = (resugar_imp env qual)
in ((uu____2898), (uu____2899))))
end)) args1)
in (

let uu____2900 = (resugar_term' env e1)
in (match (uu____2900) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, previous_args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), ((FStar_List.append previous_args args2))))) r l)
end
| e2 -> begin
(FStar_List.fold_left (fun acc uu____2937 -> (match (uu____2937) with
| (x, qual) -> begin
(mk1 (FStar_Parser_AST.App (((acc), (x), (qual)))))
end)) e2 args2)
end))))
in (

let args1 = (

let uu____2953 = (FStar_Options.print_implicits ())
in (match (uu____2953) with
| true -> begin
args
end
| uu____2964 -> begin
(filter_imp args)
end))
in (

let uu____2968 = (resugar_term_as_op e)
in (match (uu____2968) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____2981) -> begin
(

let out = (FStar_List.fold_left (fun out uu____3006 -> (match (uu____3006) with
| (x, uu____3018) -> begin
(

let x1 = (resugar_term' env x)
in (match (out) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (x1)
end
| FStar_Pervasives_Native.Some (prefix1) -> begin
(

let uu____3027 = (

let uu____3028 = (

let uu____3029 = (

let uu____3036 = (FStar_Ident.id_of_text "*")
in ((uu____3036), ((prefix1)::(x1)::[])))
in FStar_Parser_AST.Op (uu____3029))
in (mk1 uu____3028))
in FStar_Pervasives_Native.Some (uu____3027))
end))
end)) FStar_Pervasives_Native.None args1)
in (FStar_Option.get out))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____3040) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____3066))::[] -> begin
b
end
| uu____3083 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____3093 = (

let uu____3094 = (FStar_Syntax_Subst.compress body)
in uu____3094.FStar_Syntax_Syntax.n)
in (match (uu____3093) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3099) -> begin
(

let uu____3124 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____3124) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____3134 = (FStar_Options.print_implicits ())
in (match (uu____3134) with
| true -> begin
xs1
end
| uu____3139 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term' env body2)
in (

let uu____3151 = (

let uu____3152 = (

let uu____3163 = (FStar_List.map (fun _3174 -> FStar_Util.Inl (_3174)) xs3)
in ((uu____3163), (body3)))
in FStar_Parser_AST.Sum (uu____3152))
in (mk1 uu____3151)))))
end))
end
| uu____3181 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____3204 -> (match (uu____3204) with
| (e1, qual) -> begin
(resugar_term' env e1)
end))))
in (

let e1 = (resugar_term' env e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____3222) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____3231) when (Prims.op_Equality ref_read FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____3240 = (FStar_List.hd args1)
in (match (uu____3240) with
| (t1, uu____3254) -> begin
(

let uu____3259 = (

let uu____3260 = (FStar_Syntax_Subst.compress t1)
in uu____3260.FStar_Syntax_Syntax.n)
in (match (uu____3259) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____3267 = (

let uu____3268 = (

let uu____3273 = (resugar_term' env t1)
in ((uu____3273), (f)))
in FStar_Parser_AST.Project (uu____3268))
in (mk1 uu____3267)))
end
| uu____3274 -> begin
(resugar_term' env t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____3275) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(FStar_All.try_with (fun uu___426_3302 -> (match (()) with
| () -> begin
(

let new_args = (first_two_explicit args1)
in (

let uu____3312 = (match (new_args) with
| ((a1, uu____3322))::((a2, uu____3324))::[] -> begin
((a1), (a2))
end
| uu____3351 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____3312) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____3373 = (

let uu____3374 = (FStar_Syntax_Subst.compress term)
in uu____3374.FStar_Syntax_Syntax.n)
in (match (uu____3373) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____3379) -> begin
(

let uu____3404 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____3404) with
| (x1, e2) -> begin
e2
end))
end
| uu____3411 -> begin
(

let uu____3412 = (

let uu____3414 = (

let uu____3416 = (resugar_term' env term)
in (FStar_Parser_AST.term_to_string uu____3416))
in (Prims.op_Hat "wrong argument format to try_with: " uu____3414))
in (failwith uu____3412))
end)))
in (

let body1 = (

let uu____3419 = (decomp body)
in (resugar_term' env uu____3419))
in (

let handler1 = (

let uu____3421 = (decomp handler)
in (resugar_term' env uu____3421))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____3429, uu____3430, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____3462, uu____3463, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____3500 = (

let uu____3501 = (

let uu____3510 = (resugar_body t11)
in ((uu____3510), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____3501))
in (mk1 uu____3500))
end
| uu____3513 -> begin
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
| uu____3571 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end)) (fun uu___425_3603 -> (match (uu___425_3603) with
| uu____3604 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____3605) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____3614) when (((((((Prims.op_Equality op "=") || (Prims.op_Equality op "==")) || (Prims.op_Equality op "===")) || (Prims.op_Equality op "@")) || (Prims.op_Equality op ":=")) || (Prims.op_Equality op "|>")) && (FStar_Options.print_implicits ())) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____3635) when ((Prims.op_Equality op "forall") || (Prims.op_Equality op "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, (uu____3700, p), body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, (uu____3732, p), body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____3763 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____3776 = (

let uu____3777 = (FStar_Syntax_Subst.compress body)
in uu____3777.FStar_Syntax_Syntax.n)
in (match (uu____3776) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3782) -> begin
(

let uu____3807 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____3807) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____3817 = (FStar_Options.print_implicits ())
in (match (uu____3817) with
| true -> begin
xs1
end
| uu____3822 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let uu____3833 = (

let uu____3842 = (

let uu____3843 = (FStar_Syntax_Subst.compress body2)
in uu____3843.FStar_Syntax_Syntax.n)
in (match (uu____3842) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term' env e1)
in (

let uu____3861 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (uu____3878, pats) -> begin
(

let uu____3912 = (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____3956 -> (match (uu____3956) with
| (e2, uu____3964) -> begin
(resugar_term' env e2)
end))))) pats)
in ((uu____3912), (body3)))
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, p) -> begin
(

let uu____3980 = (mk1 (FStar_Parser_AST.Labeled (((body3), (s), (p)))))
in (([]), (uu____3980)))
end
| uu____3989 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in (match (uu____3861) with
| (pats, body4) -> begin
((pats), (body4))
end)))
end
| uu____4021 -> begin
(

let uu____4022 = (resugar_term' env body2)
in (([]), (uu____4022)))
end))
in (match (uu____3833) with
| (pats, body3) -> begin
(

let uu____4039 = (uncurry xs3 pats body3)
in (match (uu____4039) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____4077 = (

let uu____4078 = (

let uu____4097 = (

let uu____4108 = (FStar_Parser_AST.idents_of_binders xs5 t.FStar_Syntax_Syntax.pos)
in ((uu____4108), (pats1)))
in ((xs5), (uu____4097), (body4)))
in FStar_Parser_AST.QForall (uu____4078))
in (mk1 uu____4077))
end
| uu____4129 -> begin
(

let uu____4131 = (

let uu____4132 = (

let uu____4151 = (

let uu____4162 = (FStar_Parser_AST.idents_of_binders xs5 t.FStar_Syntax_Syntax.pos)
in ((uu____4162), (pats1)))
in ((xs5), (uu____4151), (body4)))
in FStar_Parser_AST.QExists (uu____4132))
in (mk1 uu____4131))
end))
end))
end))))
end))
end
| uu____4183 -> begin
(match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____4187 = (

let uu____4188 = (

let uu____4207 = (resugar_term' env body)
in (([]), ((([]), ([]))), (uu____4207)))
in FStar_Parser_AST.QForall (uu____4188))
in (mk1 uu____4187))
end
| uu____4228 -> begin
(

let uu____4230 = (

let uu____4231 = (

let uu____4250 = (resugar_term' env body)
in (([]), ((([]), ([]))), (uu____4250)))
in FStar_Parser_AST.QExists (uu____4231))
in (mk1 uu____4230))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____4289))::[] -> begin
(resugar b)
end
| uu____4306 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____4316 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____4318) -> begin
(

let uu____4326 = (FStar_List.hd args1)
in (match (uu____4326) with
| (e1, uu____4340) -> begin
(resugar_term' env e1)
end))
end
| FStar_Pervasives_Native.Some (op, expected_arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____4412 -> (match (uu____4412) with
| (e1, qual) -> begin
(

let uu____4429 = (resugar_term' env e1)
in (

let uu____4430 = (resugar_imp env qual)
in ((uu____4429), (uu____4430))))
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

let uu____4446 = (FStar_Util.first_N expect_n resugared_args)
in (match (uu____4446) with
| (op_args, rest) -> begin
(

let head1 = (

let uu____4494 = (

let uu____4495 = (

let uu____4502 = (FStar_List.map FStar_Pervasives_Native.fst op_args)
in ((op1), (uu____4502)))
in FStar_Parser_AST.Op (uu____4495))
in (mk1 uu____4494))
in (FStar_List.fold_left (fun head2 uu____4520 -> (match (uu____4520) with
| (arg, qual) -> begin
(mk1 (FStar_Parser_AST.App (((head2), (arg), (qual)))))
end)) head1 rest))
end))
end
| uu____4527 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some (n1) when (Prims.op_Equality (FStar_List.length args1) n1) -> begin
(

let uu____4539 = (

let uu____4540 = (

let uu____4547 = (

let uu____4550 = (resugar args1)
in (FStar_List.map FStar_Pervasives_Native.fst uu____4550))
in ((op1), (uu____4547)))
in FStar_Parser_AST.Op (uu____4540))
in (mk1 uu____4539))
end
| uu____4563 -> begin
(resugar_as_app e args1)
end)))
end))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, wopt, t1))::[]) -> begin
(

let uu____4632 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (t1)))
in (match (uu____4632) with
| (pat1, wopt1, t2) -> begin
(

let branch_bv = (FStar_Syntax_Free.names t2)
in (

let bnds = (

let uu____4678 = (

let uu____4691 = (

let uu____4696 = (resugar_pat' env pat1 branch_bv)
in (

let uu____4697 = (resugar_term' env e)
in ((uu____4696), (uu____4697))))
in ((FStar_Pervasives_Native.None), (uu____4691)))
in (uu____4678)::[])
in (

let body = (resugar_term' env t2)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body))))))))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____4749, t1))::((pat2, uu____4752, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____4848 = (

let uu____4849 = (

let uu____4856 = (resugar_term' env e)
in (

let uu____4857 = (resugar_term' env t1)
in (

let uu____4858 = (resugar_term' env t2)
in ((uu____4856), (uu____4857), (uu____4858)))))
in FStar_Parser_AST.If (uu____4849))
in (mk1 uu____4848))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____4924 -> (match (uu____4924) with
| (pat, wopt, b) -> begin
(

let uu____4966 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (b)))
in (match (uu____4966) with
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

let uu____5018 = (resugar_term' env e1)
in FStar_Pervasives_Native.Some (uu____5018))
end)
in (

let b2 = (resugar_term' env b1)
in ((pat2), (wopt2), (b2))))))
end))
end))
in (

let uu____5022 = (

let uu____5023 = (

let uu____5038 = (resugar_term' env e)
in (

let uu____5039 = (FStar_List.map resugar_branch branches)
in ((uu____5038), (uu____5039))))
in FStar_Parser_AST.Match (uu____5023))
in (mk1 uu____5022)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____5085) -> begin
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

let uu____5154 = (

let uu____5155 = (

let uu____5164 = (resugar_term' env e)
in ((uu____5164), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____5155))
in (mk1 uu____5154))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____5193 = (FStar_Syntax_Subst.open_let_rec source_lbs body)
in (match (uu____5193) with
| (source_lbs1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let attrs_opt = (match (bnd.FStar_Syntax_Syntax.lbattrs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| tms -> begin
(

let uu____5247 = (FStar_List.map (resugar_term' env) tms)
in FStar_Pervasives_Native.Some (uu____5247))
end)
in (

let uu____5254 = (

let uu____5259 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____5259))
in (match (uu____5254) with
| (univs1, td) -> begin
(

let uu____5279 = (

let uu____5286 = (

let uu____5287 = (FStar_Syntax_Subst.compress td)
in uu____5287.FStar_Syntax_Syntax.n)
in (match (uu____5286) with
| FStar_Syntax_Syntax.Tm_app (uu____5296, ((t1, uu____5298))::((d, uu____5300))::[]) -> begin
((t1), (d))
end
| uu____5357 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____5279) with
| (typ, def) -> begin
(

let uu____5388 = (

let uu____5404 = (

let uu____5405 = (FStar_Syntax_Subst.compress def)
in uu____5405.FStar_Syntax_Syntax.n)
in (match (uu____5404) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____5425) -> begin
(

let uu____5450 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____5450) with
| (b1, t2) -> begin
(

let b2 = (

let uu____5481 = (FStar_Options.print_implicits ())
in (match (uu____5481) with
| true -> begin
b1
end
| uu____5492 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____5504 -> begin
(([]), (def), (false))
end))
in (match (uu____5388) with
| (binders, term, is_pat_app) -> begin
(

let uu____5559 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____5570 = (

let uu____5571 = (

let uu____5572 = (

let uu____5579 = (bv_as_unique_ident bv)
in ((uu____5579), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____5572))
in (mk_pat uu____5571))
in ((uu____5570), (term)))
end)
in (match (uu____5559) with
| (pat, term1) -> begin
(

let uu____5601 = (match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders ((map_opt ()) (fun uu____5644 -> (match (uu____5644) with
| (bv, q) -> begin
(

let uu____5659 = (resugar_arg_qual env q)
in (FStar_Util.map_opt uu____5659 (fun q1 -> (

let uu____5671 = (

let uu____5672 = (

let uu____5679 = (bv_as_unique_ident bv)
in ((uu____5679), (q1)))
in FStar_Parser_AST.PatVar (uu____5672))
in (mk_pat uu____5671)))))
end))))
in (

let uu____5682 = (

let uu____5687 = (resugar_term' env term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____5687)))
in (

let uu____5690 = (universe_to_string univs1)
in ((uu____5682), (uu____5690)))))
end
| uu____5697 -> begin
(

let uu____5699 = (

let uu____5704 = (resugar_term' env term1)
in ((pat), (uu____5704)))
in (

let uu____5705 = (universe_to_string univs1)
in ((uu____5699), (uu____5705))))
end)
in ((attrs_opt), (uu____5601)))
end))
end))
end))
end))))
in (

let r = (FStar_List.map resugar_one_binding source_lbs1)
in (

let bnds = (

let f = (fun uu____5811 -> (match (uu____5811) with
| (attrs, (pb, univs1)) -> begin
(

let uu____5871 = (

let uu____5873 = (FStar_Options.print_universes ())
in (not (uu____5873)))
in (match (uu____5871) with
| true -> begin
((attrs), (pb))
end
| uu____5896 -> begin
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
| uu____5951 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____5954) -> begin
(

let s = (

let uu____5973 = (

let uu____5975 = (FStar_Syntax_Unionfind.uvar_id u.FStar_Syntax_Syntax.ctx_uvar_head)
in (FStar_All.pipe_right uu____5975 FStar_Util.string_of_int))
in (Prims.op_Hat "?u" uu____5973))
in (

let uu____5980 = (mk1 FStar_Parser_AST.Wild)
in (label s uu____5980)))
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

let uu____5988 = (

let uu____5989 = (

let uu____5994 = (resugar_term' env tm)
in ((uu____5994), (qi1)))
in FStar_Parser_AST.Quote (uu____5989))
in (mk1 uu____5988)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___4_6006 -> (match (uu___4_6006) with
| FStar_Syntax_Syntax.Sequence -> begin
(

let term = (resugar_term' env e)
in (

let rec resugar_seq = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (uu____6014, ((uu____6015, (p, t11)))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____6076 = (

let uu____6077 = (

let uu____6086 = (resugar_seq t11)
in ((uu____6086), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____6077))
in (mk1 uu____6076))
end
| uu____6089 -> begin
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
| FStar_Syntax_Syntax.Meta_pattern (uu____6090, pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____6154 -> (match (uu____6154) with
| (x, uu____6162) -> begin
(resugar_term' env x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (uu____6167) -> begin
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
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____6185, t1) -> begin
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

let uu____6225 = (FStar_Options.print_universes ())
in (match (uu____6225) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____6247 -> begin
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

let uu____6289 = (FStar_Options.print_universes ())
in (match (uu____6289) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____6311 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____6333 = (resugar_term' env c1.FStar_Syntax_Syntax.result_typ)
in ((uu____6333), (FStar_Parser_AST.Nothing)))
in (

let uu____6334 = ((FStar_Options.print_effect_args ()) || (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid))
in (match (uu____6334) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (

let uu____6357 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____6357) with
| true -> begin
(match (c1.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::(pats)::[] -> begin
(

let post1 = (

let uu____6442 = (FStar_Syntax_Util.unthunk_lemma_post (FStar_Pervasives_Native.fst post))
in ((uu____6442), ((FStar_Pervasives_Native.snd post))))
in (

let uu____6453 = (

let uu____6462 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid (FStar_Pervasives_Native.fst pre))
in (match (uu____6462) with
| true -> begin
[]
end
| uu____6483 -> begin
(pre)::[]
end))
in (

let uu____6497 = (

let uu____6506 = (

let uu____6515 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid (FStar_Pervasives_Native.fst pats))
in (match (uu____6515) with
| true -> begin
[]
end
| uu____6536 -> begin
(pats)::[]
end))
in (FStar_List.append ((post1)::[]) uu____6506))
in (FStar_List.append uu____6453 uu____6497))))
end
| uu____6574 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
end
| uu____6585 -> begin
c1.FStar_Syntax_Syntax.effect_args
end))
in (

let args1 = (FStar_List.map (fun uu____6608 -> (match (uu____6608) with
| (e, uu____6620) -> begin
(

let uu____6625 = (resugar_term' env e)
in ((uu____6625), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___5_6650 -> (match (uu___5_6650) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____6683 = (resugar_term' env e)
in ((uu____6683), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____6688 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____6714 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun env b r -> (

let uu____6735 = b
in (match (uu____6735) with
| (x, aq) -> begin
(

let uu____6744 = (resugar_arg_qual env aq)
in (FStar_Util.map_opt uu____6744 (fun imp -> (

let e = (resugar_term' env x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____6758 = (

let uu____6759 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____6759))
in (FStar_Parser_AST.mk_binder uu____6758 r FStar_Parser_AST.Type_level imp))
end
| uu____6760 -> begin
(

let uu____6761 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____6761) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____6764 -> begin
(

let uu____6766 = (

let uu____6767 = (

let uu____6772 = (bv_as_unique_ident x)
in ((uu____6772), (e)))
in FStar_Parser_AST.Annotated (uu____6767))
in (FStar_Parser_AST.mk_binder uu____6766 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Parser_AST.pattern = (fun env v1 aqual body_bv typ_opt -> (

let mk1 = (fun a -> (

let uu____6792 = (FStar_Syntax_Syntax.range_of_bv v1)
in (FStar_Parser_AST.mk_pattern a uu____6792)))
in (

let used = (FStar_Util.set_mem v1 body_bv)
in (

let pat = (

let uu____6796 = (match (used) with
| true -> begin
(

let uu____6798 = (

let uu____6805 = (bv_as_unique_ident v1)
in ((uu____6805), (aqual)))
in FStar_Parser_AST.PatVar (uu____6798))
end
| uu____6808 -> begin
FStar_Parser_AST.PatWild (aqual)
end)
in (mk1 uu____6796))
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
pat
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____6812; FStar_Syntax_Syntax.vars = uu____6813}) -> begin
pat
end
| FStar_Pervasives_Native.Some (typ) -> begin
(

let uu____6823 = (FStar_Options.print_bound_var_types ())
in (match (uu____6823) with
| true -> begin
(

let uu____6826 = (

let uu____6827 = (

let uu____6838 = (

let uu____6845 = (resugar_term' env typ)
in ((uu____6845), (FStar_Pervasives_Native.None)))
in ((pat), (uu____6838)))
in FStar_Parser_AST.PatAscribed (uu____6827))
in (mk1 uu____6826))
end
| uu____6854 -> begin
pat
end))
end)))))
and resugar_bv_as_pat : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun env x qual body_bv -> (

let uu____6866 = (resugar_arg_qual env qual)
in (FStar_Util.map_opt uu____6866 (fun aqual -> (

let uu____6878 = (

let uu____6883 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_left (fun _6894 -> FStar_Pervasives_Native.Some (_6894)) uu____6883))
in (resugar_bv_as_pat' env x aqual body_bv uu____6878))))))
and resugar_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun env p branch_bv -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p))
in (

let to_arg_qual = (fun bopt -> (FStar_Util.bind_opt bopt (fun b -> (match (b) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)
end
| uu____6927 -> begin
FStar_Pervasives_Native.None
end))))
in (

let may_drop_implicits = (fun args -> ((

let uu____6956 = (FStar_Options.print_implicits ())
in (not (uu____6956))) && (

let uu____6959 = (FStar_List.existsML (fun uu____6972 -> (match (uu____6972) with
| (pattern, is_implicit1) -> begin
(

let might_be_used = (match (pattern.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, uu____6994) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_wild (uu____6999) -> begin
false
end
| uu____7001 -> begin
true
end)
in (is_implicit1 && might_be_used))
end)) args)
in (not (uu____6959)))))
in (

let resugar_plain_pat_cons' = (fun fv args -> (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args))))))
in (

let rec resugar_plain_pat_cons = (fun fv args -> (

let args1 = (

let uu____7069 = (may_drop_implicits args)
in (match (uu____7069) with
| true -> begin
(filter_pattern_imp args)
end
| uu____7081 -> begin
args
end))
in (

let args2 = (FStar_List.map (fun uu____7094 -> (match (uu____7094) with
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

let uu____7149 = (

let uu____7151 = (

let uu____7153 = (filter_pattern_imp args)
in (FStar_List.isEmpty uu____7153))
in (not (uu____7151)))
in (match (uu____7149) with
| true -> begin
(FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p ((FStar_Errors.Warning_NilGivenExplicitArgs), ("Prims.Nil given explicit arguments")))
end
| uu____7175 -> begin
()
end));
(mk1 (FStar_Parser_AST.PatList ([])));
)
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.cons_lid) && (may_drop_implicits args)) -> begin
(

let uu____7197 = (filter_pattern_imp args)
in (match (uu____7197) with
| ((hd1, false))::((tl1, false))::[] -> begin
(

let hd' = (aux hd1 (FStar_Pervasives_Native.Some (false)))
in (

let uu____7247 = (aux tl1 (FStar_Pervasives_Native.Some (false)))
in (match (uu____7247) with
| {FStar_Parser_AST.pat = FStar_Parser_AST.PatList (tl'); FStar_Parser_AST.prange = p2} -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatList ((hd')::tl')) p2)
end
| tl' -> begin
(resugar_plain_pat_cons' fv ((hd')::(tl')::[]))
end)))
end
| args' -> begin
((

let uu____7266 = (

let uu____7272 = (

let uu____7274 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args'))
in (FStar_Util.format1 "Prims.Cons applied to %s explicit arguments" uu____7274))
in ((FStar_Errors.Warning_ConsAppliedExplicitArgs), (uu____7272)))
in (FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p uu____7266));
(resugar_plain_pat_cons fv args);
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((is_tuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) && (may_drop_implicits args)) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.filter_map (fun uu____7327 -> (match (uu____7327) with
| (p2, is_implicit1) -> begin
(match (is_implicit1) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7342 -> begin
(

let uu____7344 = (aux p2 (FStar_Pervasives_Native.Some (false)))
in FStar_Pervasives_Native.Some (uu____7344))
end)
end))))
in (

let is_dependent_tuple = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mk1 (FStar_Parser_AST.PatTuple (((args1), (is_dependent_tuple)))))))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____7352; FStar_Syntax_Syntax.fv_delta = uu____7353; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____7382 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____7382 FStar_List.rev))
in (

let args1 = (

let uu____7398 = (FStar_All.pipe_right args (FStar_List.map (fun uu____7418 -> (match (uu____7418) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____7398 FStar_List.rev))
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

let uu____7496 = (map21 tl1 [])
in (((hd1), ((mk1 (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None))))))::uu____7496)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____7519 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____7519)
end))
in (

let args2 = (

let uu____7537 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____7537 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(resugar_plain_pat_cons fv args)
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____7581 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____7581) with
| FStar_Pervasives_Native.Some (op, uu____7593) -> begin
(

let uu____7610 = (

let uu____7611 = (FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in FStar_Parser_AST.PatOp (uu____7611))
in (mk1 uu____7610))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7621 = (to_arg_qual imp_opt)
in (resugar_bv_as_pat' env v1 uu____7621 branch_bv FStar_Pervasives_Native.None))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____7626) -> begin
(

let uu____7627 = (

let uu____7628 = (to_arg_qual imp_opt)
in FStar_Parser_AST.PatWild (uu____7628))
in (mk1 uu____7627))
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
| uu____7659 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
end)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta (t)) -> begin
(

let uu____7668 = (

let uu____7671 = (

let uu____7672 = (resugar_term' env t)
in FStar_Parser_AST.Meta (uu____7672))
in FStar_Pervasives_Native.Some (uu____7671))
in FStar_Pervasives_Native.Some (uu____7668))
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

let uu____7684 = (resugar_term' env t)
in FStar_Parser_AST.HashBrace (uu____7684))
end))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___6_7692 -> (match (uu___6_7692) with
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
| FStar_Syntax_Syntax.Reflectable (uu____7699) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____7700) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____7701) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____7706) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____7715) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____7724) -> begin
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


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___7_7730 -> (match (uu___7_7730) with
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
| FStar_Syntax_Syntax.RestartSolver -> begin
FStar_Parser_AST.RestartSolver
end
| FStar_Syntax_Syntax.LightOff -> begin
FStar_Parser_AST.LightOff
end))


let resugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon) = (fun env datacon_ses se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____7773, datacons) -> begin
(

let uu____7783 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____7811, uu____7812, uu____7813, inductive_lid, uu____7815, uu____7816) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____7823 -> begin
(failwith "unexpected")
end))))
in (match (uu____7783) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____7844 = (FStar_Options.print_implicits ())
in (match (uu____7844) with
| true -> begin
bs
end
| uu____7849 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____7861 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___8_7868 -> (match (uu___8_7868) with
| FStar_Syntax_Syntax.RecordType (uu____7870) -> begin
true
end
| uu____7880 -> begin
false
end))))
in (match (uu____7861) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____7934, univs1, term, uu____7937, num, uu____7939) -> begin
(

let uu____7946 = (

let uu____7947 = (FStar_Syntax_Subst.compress term)
in uu____7947.FStar_Syntax_Syntax.n)
in (match (uu____7946) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____7961) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____8030 -> (match (uu____8030) with
| (b, qual) -> begin
(

let uu____8051 = (bv_as_unique_ident b)
in (

let uu____8052 = (resugar_term' env b.FStar_Syntax_Syntax.sort)
in ((uu____8051), (uu____8052), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____8063 -> begin
(failwith "unexpected")
end))
end
| uu____8075 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____8130 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____8206, num, uu____8208) -> begin
(

let c = (

let uu____8229 = (

let uu____8232 = (resugar_term' env term)
in FStar_Pervasives_Native.Some (uu____8232))
in ((l.FStar_Ident.ident), (uu____8229), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____8252 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____8332 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____8358 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____8358; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme'' : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env name ts -> (

let uu____8388 = ts
in (match (uu____8388) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____8401 = (

let uu____8402 = (

let uu____8419 = (

let uu____8428 = (

let uu____8435 = (

let uu____8436 = (

let uu____8449 = (resugar_term' env typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____8449)))
in FStar_Parser_AST.TyconAbbrev (uu____8436))
in ((uu____8435), (FStar_Pervasives_Native.None)))
in (uu____8428)::[])
in ((false), (false), (uu____8419)))
in FStar_Parser_AST.Tycon (uu____8402))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____8401)))
end)))


let resugar_tscheme' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env ts -> (resugar_tscheme'' env "tscheme" ts))


let resugar_wp_eff_combinators : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Syntax_Syntax.wp_eff_combinators  ->  FStar_Parser_AST.decl Prims.list = (fun env for_free combs -> (

let resugar_opt = (fun name tsopt -> (match (tsopt) with
| FStar_Pervasives_Native.Some (ts) -> begin
(

let uu____8534 = (resugar_tscheme'' env name ts)
in (uu____8534)::[])
end
| FStar_Pervasives_Native.None -> begin
[]
end))
in (

let repr = (resugar_opt "repr" combs.FStar_Syntax_Syntax.repr)
in (

let return_repr = (resugar_opt "return_repr" combs.FStar_Syntax_Syntax.return_repr)
in (

let bind_repr = (resugar_opt "bind_repr" combs.FStar_Syntax_Syntax.bind_repr)
in (match (for_free) with
| true -> begin
(FStar_List.append repr (FStar_List.append return_repr bind_repr))
end
| uu____8550 -> begin
(

let uu____8552 = (resugar_tscheme'' env "ret_wp" combs.FStar_Syntax_Syntax.ret_wp)
in (

let uu____8554 = (

let uu____8557 = (resugar_tscheme'' env "bind_wp" combs.FStar_Syntax_Syntax.bind_wp)
in (

let uu____8559 = (

let uu____8562 = (resugar_tscheme'' env "stronger" combs.FStar_Syntax_Syntax.stronger)
in (

let uu____8564 = (

let uu____8567 = (resugar_tscheme'' env "if_then_else" combs.FStar_Syntax_Syntax.if_then_else)
in (

let uu____8569 = (

let uu____8572 = (resugar_tscheme'' env "ite_wp" combs.FStar_Syntax_Syntax.ite_wp)
in (

let uu____8574 = (

let uu____8577 = (resugar_tscheme'' env "close_wp" combs.FStar_Syntax_Syntax.close_wp)
in (

let uu____8579 = (

let uu____8582 = (resugar_tscheme'' env "trivial" combs.FStar_Syntax_Syntax.trivial)
in (uu____8582)::(FStar_List.append repr (FStar_List.append return_repr bind_repr)))
in (uu____8577)::uu____8579))
in (uu____8572)::uu____8574))
in (uu____8567)::uu____8569))
in (uu____8562)::uu____8564))
in (uu____8557)::uu____8559))
in (uu____8552)::uu____8554))
end))))))


let resugar_layered_eff_combinators : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.layered_eff_combinators  ->  FStar_Parser_AST.decl Prims.list = (fun env combs -> (

let resugar = (fun name uu____8612 -> (match (uu____8612) with
| (ts, uu____8619) -> begin
(resugar_tscheme'' env name ts)
end))
in (

let uu____8620 = (resugar "repr" combs.FStar_Syntax_Syntax.l_repr)
in (

let uu____8622 = (

let uu____8625 = (resugar "return" combs.FStar_Syntax_Syntax.l_return)
in (

let uu____8627 = (

let uu____8630 = (resugar "bind" combs.FStar_Syntax_Syntax.l_bind)
in (

let uu____8632 = (

let uu____8635 = (resugar "subcomp" combs.FStar_Syntax_Syntax.l_subcomp)
in (

let uu____8637 = (

let uu____8640 = (resugar "if_then_else" combs.FStar_Syntax_Syntax.l_if_then_else)
in (uu____8640)::[])
in (uu____8635)::uu____8637))
in (uu____8630)::uu____8632))
in (uu____8625)::uu____8627))
in (uu____8620)::uu____8622))))


let resugar_combinators : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.eff_combinators  ->  FStar_Parser_AST.decl Prims.list = (fun env combs -> (match (combs) with
| FStar_Syntax_Syntax.Primitive_eff (combs1) -> begin
(resugar_wp_eff_combinators env false combs1)
end
| FStar_Syntax_Syntax.DM4F_eff (combs1) -> begin
(resugar_wp_eff_combinators env true combs1)
end
| FStar_Syntax_Syntax.Layered_eff (combs1) -> begin
(resugar_layered_eff_combinators env combs1)
end))


let resugar_eff_decl' : FStar_Syntax_DsEnv.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun env r q ed -> (

let resugar_action = (fun d for_free -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____8701 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____8701) with
| (bs, action_defn) -> begin
(

let uu____8708 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____8708) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____8718 = (FStar_Options.print_implicits ())
in (match (uu____8718) with
| true -> begin
action_params
end
| uu____8723 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____8728 = (FStar_All.pipe_right action_params1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____8728 FStar_List.rev))
in (

let action_defn1 = (resugar_term' env action_defn)
in (

let action_typ1 = (resugar_term' env action_typ)
in (match (for_free) with
| true -> begin
(

let a = (

let uu____8745 = (

let uu____8756 = (FStar_Ident.lid_of_str "construct")
in ((uu____8756), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____8745))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), (false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____8807 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), (false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____8840 = (

let uu____8845 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.signature FStar_Pervasives_Native.snd)
in (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders uu____8845))
in (match (uu____8840) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____8863 = (FStar_Options.print_implicits ())
in (match (uu____8863) with
| true -> begin
eff_binders
end
| uu____8868 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____8873 = (FStar_All.pipe_right eff_binders1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____8873 FStar_List.rev))
in (

let eff_typ1 = (resugar_term' env eff_typ)
in (

let mandatory_members_decls = (resugar_combinators env ed.FStar_Syntax_Syntax.combinators)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls))))))))))))
end)))))


let resugar_sigelt' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____8923) -> begin
(

let uu____8932 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8955) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____8973) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____8981) -> begin
false
end
| uu____8998 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____8932) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____9036 se1 -> (match (uu____9036) with
| (datacon_ses1, tycons) -> begin
(

let uu____9062 = (resugar_typ env datacon_ses1 se1)
in (match (uu____9062) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____9077 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____9077) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____9112 = (

let uu____9113 = (

let uu____9114 = (

let uu____9131 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (false), (uu____9131)))
in FStar_Parser_AST.Tycon (uu____9114))
in (decl'_to_decl se uu____9113))
in FStar_Pervasives_Native.Some (uu____9112))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____9166, uu____9167, uu____9168, uu____9169, uu____9170) -> begin
(

let uu____9177 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____9177))
end
| uu____9180 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____9184 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____9191) -> begin
(

let uu____9196 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___9_9204 -> (match (uu___9_9204) with
| FStar_Syntax_Syntax.Projector (uu____9206, uu____9207) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____9209) -> begin
true
end
| uu____9211 -> begin
false
end))))
in (match (uu____9196) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9216 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term' env desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____9246) -> begin
(

let uu____9275 = (

let uu____9276 = (

let uu____9277 = (

let uu____9288 = (FStar_List.map FStar_Pervasives_Native.snd lets)
in ((isrec), (uu____9288)))
in FStar_Parser_AST.TopLevelLet (uu____9277))
in (decl'_to_decl se uu____9276))
in FStar_Pervasives_Native.Some (uu____9275))
end
| uu____9325 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____9330, fml) -> begin
(

let uu____9332 = (

let uu____9333 = (

let uu____9334 = (

let uu____9339 = (resugar_term' env fml)
in ((lid.FStar_Ident.ident), (uu____9339)))
in FStar_Parser_AST.Assume (uu____9334))
in (decl'_to_decl se uu____9333))
in FStar_Pervasives_Native.Some (uu____9332))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____9341 = (resugar_eff_decl' env se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____9341))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____9350, t) -> begin
(

let uu____9360 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____9360))
end
| uu____9361 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____9369, t) -> begin
(

let uu____9379 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____9379))
end
| uu____9380 -> begin
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
| uu____9404 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____9414 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____9414)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) -> begin
(

let uu____9424 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____9424) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____9436 = (FStar_Options.print_implicits ())
in (match (uu____9436) with
| true -> begin
bs1
end
| uu____9441 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 ((map_opt ()) (fun b -> (resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____9452 = (

let uu____9453 = (

let uu____9454 = (

let uu____9471 = (

let uu____9480 = (

let uu____9487 = (

let uu____9488 = (

let uu____9501 = (resugar_comp' env c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____9501)))
in FStar_Parser_AST.TyconAbbrev (uu____9488))
in ((uu____9487), (FStar_Pervasives_Native.None)))
in (uu____9480)::[])
in ((false), (false), (uu____9471)))
in FStar_Parser_AST.Tycon (uu____9454))
in (decl'_to_decl se uu____9453))
in FStar_Pervasives_Native.Some (uu____9452))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____9533 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____9533))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____9537 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___10_9545 -> (match (uu___10_9545) with
| FStar_Syntax_Syntax.Projector (uu____9547, uu____9548) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____9550) -> begin
true
end
| uu____9552 -> begin
false
end))))
in (match (uu____9537) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____9557 -> begin
(

let t' = (

let uu____9560 = ((

let uu____9564 = (FStar_Options.print_universes ())
in (not (uu____9564))) || (FStar_List.isEmpty uvs))
in (match (uu____9560) with
| true -> begin
(resugar_term' env t)
end
| uu____9567 -> begin
(

let uu____9569 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____9569) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____9578 = (resugar_term' env t1)
in (label universes uu____9578)))
end))
end))
in (

let uu____9579 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____9579)))
end))
end
| FStar_Syntax_Syntax.Sig_splice (ids, t) -> begin
(

let uu____9586 = (

let uu____9587 = (

let uu____9588 = (

let uu____9595 = (FStar_List.map (fun l -> l.FStar_Ident.ident) ids)
in (

let uu____9600 = (resugar_term' env t)
in ((uu____9595), (uu____9600))))
in FStar_Parser_AST.Splice (uu____9588))
in (decl'_to_decl se uu____9587))
in FStar_Pervasives_Native.Some (uu____9586))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____9603) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____9620) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____9636) -> begin
FStar_Pervasives_Native.None
end))


let empty_env : FStar_Syntax_DsEnv.env = (FStar_Syntax_DsEnv.empty_env FStar_Parser_Dep.empty_deps)


let noenv : 'a . (FStar_Syntax_DsEnv.env  ->  'a)  ->  'a = (fun f -> (f empty_env))


let resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____9660 = (noenv resugar_term')
in (uu____9660 t)))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (

let uu____9678 = (noenv resugar_sigelt')
in (uu____9678 se)))


let resugar_comp : FStar_Syntax_Syntax.comp  ->  FStar_Parser_AST.term = (fun c -> (

let uu____9696 = (noenv resugar_comp')
in (uu____9696 c)))


let resugar_pat : FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun p branch_bv -> (

let uu____9719 = (noenv resugar_pat')
in (uu____9719 p branch_bv)))


let resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____9753 = (noenv resugar_binder')
in (uu____9753 b r)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (

let uu____9778 = (noenv resugar_tscheme')
in (uu____9778 ts)))


let resugar_eff_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun r q ed -> (

let uu____9806 = (noenv resugar_eff_decl')
in (uu____9806 r q ed)))






open Prims
open FStar_Pervasives

let doc_to_string : FStar_Pprint.document  ->  Prims.string = (fun doc1 -> (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1))


let parser_term_to_string : FStar_Parser_AST.term  ->  Prims.string = (fun t -> (

let uu____9 = (FStar_Parser_ToDocument.term_to_document t)
in (doc_to_string uu____9)))


let map_opt : 'Auu____18 'Auu____19 . Prims.unit  ->  ('Auu____19  ->  'Auu____18 FStar_Pervasives_Native.option)  ->  'Auu____19 Prims.list  ->  'Auu____18 Prims.list = (fun uu____33 -> FStar_List.filter_map)


let bv_as_unique_ident : FStar_Syntax_Syntax.bv  ->  FStar_Ident.ident = (fun x -> (

let unique_name = (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)) with
| true -> begin
(

let uu____39 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____39))
end
| uu____40 -> begin
x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)
in (FStar_Ident.mk_ident ((unique_name), (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))))


let filter_imp : 'Auu____45 . ('Auu____45 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____45 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___185_99 -> (match (uu___185_99) with
| (uu____106, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____107))) -> begin
false
end
| uu____110 -> begin
true
end)))))


let label : Prims.string  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun s t -> (match ((Prims.op_Equality s "")) with
| true -> begin
t
end
| uu____125 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled (((t), (s), (true)))) t.FStar_Parser_AST.range FStar_Parser_AST.Un)
end))


let resugar_arg_qual : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option FStar_Pervasives_Native.option = (fun q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____155 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
end)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality))
end))


let resugar_imp : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.imp FStar_Pervasives_Native.option = (fun q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Nothing)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Hash)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
FStar_Pervasives_Native.None
end))


let rec universe_to_int : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe) = (fun n1 u -> (match (u) with
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(universe_to_int (n1 + (Prims.parse_int "1")) u1)
end
| uu____191 -> begin
((n1), (u))
end))


let universe_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun univs1 -> (

let uu____200 = (FStar_Options.print_universes ())
in (match (uu____200) with
| true -> begin
(

let uu____201 = (FStar_List.map (fun x -> x.FStar_Ident.idText) univs1)
in (FStar_All.pipe_right uu____201 (FStar_String.concat ", ")))
end
| uu____208 -> begin
""
end)))


let rec resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____234) -> begin
(

let uu____235 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____235) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____242 = (

let uu____243 = (

let uu____244 = (

let uu____255 = (FStar_Util.string_of_int n1)
in ((uu____255), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____244))
in FStar_Parser_AST.Const (uu____243))
in (mk1 uu____242 r))
end
| uu____266 -> begin
(

let e1 = (

let uu____268 = (

let uu____269 = (

let uu____270 = (

let uu____281 = (FStar_Util.string_of_int n1)
in ((uu____281), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____270))
in FStar_Parser_AST.Const (uu____269))
in (mk1 uu____268 r))
in (

let e2 = (resugar_universe u1 r)
in (mk1 (FStar_Parser_AST.Op ((((FStar_Ident.id_of_text "+")), ((e1)::(e2)::[])))) r)))
end)
end))
end
| FStar_Syntax_Syntax.U_max (l) -> begin
(match (l) with
| [] -> begin
(failwith "Impossible: U_max without arguments")
end
| uu____298 -> begin
(

let t = (

let uu____302 = (

let uu____303 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____303))
in (mk1 uu____302 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____309 = (

let uu____310 = (

let uu____317 = (resugar_universe x r)
in ((acc), (uu____317), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____310))
in (mk1 uu____309 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____319) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id = (

let uu____330 = (

let uu____335 = (

let uu____336 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____336))
in ((uu____335), (r)))
in (FStar_Ident.mk_ident uu____330))
in (mk1 (FStar_Parser_AST.Uvar (id)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___186_356 -> (match (uu___186_356) with
| "Amp" -> begin
FStar_Pervasives_Native.Some ((("&"), ((Prims.parse_int "0"))))
end
| "At" -> begin
FStar_Pervasives_Native.Some ((("@"), ((Prims.parse_int "0"))))
end
| "Plus" -> begin
FStar_Pervasives_Native.Some ((("+"), ((Prims.parse_int "0"))))
end
| "Minus" -> begin
FStar_Pervasives_Native.Some ((("-"), ((Prims.parse_int "0"))))
end
| "Subtraction" -> begin
FStar_Pervasives_Native.Some ((("-"), ((Prims.parse_int "2"))))
end
| "Tilde" -> begin
FStar_Pervasives_Native.Some ((("~"), ((Prims.parse_int "0"))))
end
| "Slash" -> begin
FStar_Pervasives_Native.Some ((("/"), ((Prims.parse_int "0"))))
end
| "Backslash" -> begin
FStar_Pervasives_Native.Some ((("\\"), ((Prims.parse_int "0"))))
end
| "Less" -> begin
FStar_Pervasives_Native.Some ((("<"), ((Prims.parse_int "0"))))
end
| "Equals" -> begin
FStar_Pervasives_Native.Some ((("="), ((Prims.parse_int "0"))))
end
| "Greater" -> begin
FStar_Pervasives_Native.Some (((">"), ((Prims.parse_int "0"))))
end
| "Underscore" -> begin
FStar_Pervasives_Native.Some ((("_"), ((Prims.parse_int "0"))))
end
| "Bar" -> begin
FStar_Pervasives_Native.Some ((("|"), ((Prims.parse_int "0"))))
end
| "Bang" -> begin
FStar_Pervasives_Native.Some ((("!"), ((Prims.parse_int "0"))))
end
| "Hat" -> begin
FStar_Pervasives_Native.Some ((("^"), ((Prims.parse_int "0"))))
end
| "Percent" -> begin
FStar_Pervasives_Native.Some ((("%"), ((Prims.parse_int "0"))))
end
| "Star" -> begin
FStar_Pervasives_Native.Some ((("*"), ((Prims.parse_int "0"))))
end
| "Question" -> begin
FStar_Pervasives_Native.Some ((("?"), ((Prims.parse_int "0"))))
end
| "Colon" -> begin
FStar_Pervasives_Native.Some (((":"), ((Prims.parse_int "0"))))
end
| "Dollar" -> begin
FStar_Pervasives_Native.Some ((("$"), ((Prims.parse_int "0"))))
end
| "Dot" -> begin
FStar_Pervasives_Native.Some ((("."), ((Prims.parse_int "0"))))
end
| uu____447 -> begin
FStar_Pervasives_Native.None
end))
in (match (s) with
| "op_String_Assignment" -> begin
FStar_Pervasives_Native.Some (((".[]<-"), ((Prims.parse_int "0"))))
end
| "op_Array_Assignment" -> begin
FStar_Pervasives_Native.Some (((".()<-"), ((Prims.parse_int "0"))))
end
| "op_String_Access" -> begin
FStar_Pervasives_Native.Some (((".[]"), ((Prims.parse_int "0"))))
end
| "op_Array_Access" -> begin
FStar_Pervasives_Native.Some (((".()"), ((Prims.parse_int "0"))))
end
| uu____474 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____484 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____484 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____492 -> begin
(

let op = (

let uu____496 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (x) with
| FStar_Pervasives_Native.Some (op, uu____530) -> begin
(Prims.strcat acc op)
end
| FStar_Pervasives_Native.None -> begin
(failwith "wrong composed operator format")
end)) "" uu____496))
in FStar_Pervasives_Native.Some (((op), ((Prims.parse_int "0")))))
end))
end
| uu____543 -> begin
FStar_Pervasives_Native.None
end)
end)))


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.strcat_lid), ("^")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____717 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____717) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), ((Prims.parse_int "0"))))
end
| uu____765 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____778 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), ((Prims.parse_int "0"))))
end
| uu____795 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), ((Prims.parse_int "0"))))
end
| uu____806 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), ((Prims.parse_int "0"))))
end
| uu____817 -> begin
(

let uu____818 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____818) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), ((Prims.parse_int "0"))))
end
| uu____829 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____834 = (

let uu____835 = (FStar_Syntax_Subst.compress t)
in uu____835.FStar_Syntax_Syntax.n)
in (match (uu____834) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____851 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____858 = (string_to_op s)
in (match (uu____858) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____884 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____897 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____906 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____911) -> begin
true
end
| uu____912 -> begin
false
end))


let rec resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____943 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____943)))
in (

let var = (fun a r -> (

let uu____951 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Var (uu____951)))
in (

let uu____952 = (

let uu____953 = (FStar_Syntax_Subst.compress t)
in uu____953.FStar_Syntax_Syntax.n)
in (match (uu____952) with
| FStar_Syntax_Syntax.Tm_delayed (uu____956) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____983 = (

let uu____986 = (bv_as_unique_ident x)
in (uu____986)::[])
in (FStar_Ident.lid_of_ids uu____983))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____989 = (

let uu____992 = (bv_as_unique_ident x)
in (uu____992)::[])
in (FStar_Ident.lid_of_ids uu____989))
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
| uu____1001 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.strcat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____1010 = (

let uu____1011 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____1011))
in (mk1 uu____1010)))
end
| uu____1012 -> begin
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
| uu____1021 -> begin
(failwith "wrong projector format")
end)))
end
| uu____1024 -> begin
(

let uu____1025 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____1028 = (

let uu____1029 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____1029))
in (

let uu____1030 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____1028 uu____1030))))
in (match (uu____1025) with
| true -> begin
(

let uu____1031 = (var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1031))
end
| uu____1032 -> begin
(

let uu____1033 = (name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1033))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let uu____1040 = (FStar_Options.print_universes ())
in (match (uu____1040) with
| true -> begin
(

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (

let uu____1047 = (

let uu____1048 = (

let uu____1055 = (resugar_universe x t.FStar_Syntax_Syntax.pos)
in ((acc), (uu____1055), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____1048))
in (mk1 uu____1047))) e1 universes))
end
| uu____1056 -> begin
(resugar_term e)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1058 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____1058) with
| true -> begin
(

let uu____1059 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1059))
end
| uu____1060 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____1062 = (name "Type0" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1062))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____1063 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1063))
end
| uu____1064 -> begin
(

let uu____1065 = (FStar_Options.print_universes ())
in (match (uu____1065) with
| true -> begin
(

let u1 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in (

let l = (FStar_Ident.lid_of_path (("Type")::[]) t.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((l), ((((u1), (FStar_Parser_AST.UnivApp)))::[])))))))
end
| uu____1082 -> begin
(

let uu____1083 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1083))
end))
end)
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1086) -> begin
(

let uu____1107 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____1107) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1115 = (FStar_Options.print_implicits ())
in (match (uu____1115) with
| true -> begin
xs1
end
| uu____1116 -> begin
(filter_imp xs1)
end))
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____1129 -> (match (uu____1129) with
| (x, qual) -> begin
(resugar_bv_as_pat x qual)
end))))
in (

let body2 = (resugar_term body1)
in (mk1 (FStar_Parser_AST.Abs (((patterns), (body2))))))))
end))
end
| FStar_Syntax_Syntax.Tm_arrow (xs, body) -> begin
(

let uu____1159 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____1159) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1167 = (FStar_Options.print_implicits ())
in (match (uu____1167) with
| true -> begin
xs1
end
| uu____1168 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp body1)
in (

let xs3 = (

let uu____1173 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____1173 FStar_List.rev))
in (

let rec aux = (fun body3 uu___187_1192 -> (match (uu___187_1192) with
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

let uu____1208 = (

let uu____1213 = (

let uu____1214 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1214)::[])
in (FStar_Syntax_Subst.open_term uu____1213 phi))
in (match (uu____1208) with
| (x1, phi1) -> begin
(

let b = (

let uu____1218 = (

let uu____1221 = (FStar_List.hd x1)
in (resugar_binder uu____1221 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____1218))
in (

let uu____1226 = (

let uu____1227 = (

let uu____1232 = (resugar_term phi1)
in ((b), (uu____1232)))
in FStar_Parser_AST.Refine (uu____1227))
in (mk1 uu____1226)))
end))
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___188_1274 -> (match (uu___188_1274) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____1344 -> begin
(failwith "last of an empty list")
end))
in (

let rec last_two = (fun uu___189_1380 -> (match (uu___189_1380) with
| [] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (uu____1411)::[] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (a1)::(a2)::[] -> begin
(a1)::(a2)::[]
end
| (uu____1488)::t1 -> begin
(last_two t1)
end))
in (

let rec last_three = (fun uu___190_1529 -> (match (uu___190_1529) with
| [] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1560)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1587)::(uu____1588)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (a1)::(a2)::(a3)::[] -> begin
(a1)::(a2)::(a3)::[]
end
| (uu____1696)::t1 -> begin
(last_three t1)
end))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_All.pipe_right args1 (FStar_List.map (fun uu____1782 -> (match (uu____1782) with
| (e2, qual) -> begin
(

let uu____1801 = (resugar_term e2)
in ((uu____1801), (qual)))
end))))
in (

let e2 = (resugar_term e1)
in (

let res_impl = (fun desugared_tm qual -> (

let uu____1816 = (resugar_imp qual)
in (match (uu____1816) with
| FStar_Pervasives_Native.Some (imp) -> begin
imp
end
| FStar_Pervasives_Native.None -> begin
((

let uu____1821 = (

let uu____1822 = (parser_term_to_string desugared_tm)
in (FStar_Util.format1 "Inaccessible argument %s in function application" uu____1822))
in (FStar_Errors.warn t.FStar_Syntax_Syntax.pos uu____1821));
FStar_Parser_AST.Nothing;
)
end)))
in (FStar_List.fold_left (fun acc uu____1835 -> (match (uu____1835) with
| (x, qual) -> begin
(

let uu____1848 = (

let uu____1849 = (

let uu____1856 = (res_impl x qual)
in ((acc), (x), (uu____1856)))
in FStar_Parser_AST.App (uu____1849))
in (mk1 uu____1848))
end)) e2 args2)))))
in (

let args1 = (

let uu____1866 = (FStar_Options.print_implicits ())
in (match (uu____1866) with
| true -> begin
args
end
| uu____1875 -> begin
(filter_imp args)
end))
in (

let uu____1878 = (resugar_term_as_op e)
in (match (uu____1878) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____1889) -> begin
(match (args1) with
| ((fst1, uu____1895))::((snd1, uu____1897))::rest -> begin
(

let e1 = (

let uu____1928 = (

let uu____1929 = (

let uu____1936 = (

let uu____1939 = (resugar_term fst1)
in (

let uu____1940 = (

let uu____1943 = (resugar_term snd1)
in (uu____1943)::[])
in (uu____1939)::uu____1940))
in (((FStar_Ident.id_of_text "*")), (uu____1936)))
in FStar_Parser_AST.Op (uu____1929))
in (mk1 uu____1928))
in (FStar_List.fold_left (fun acc uu____1956 -> (match (uu____1956) with
| (x, uu____1962) -> begin
(

let uu____1963 = (

let uu____1964 = (

let uu____1971 = (

let uu____1974 = (

let uu____1977 = (resugar_term x)
in (uu____1977)::[])
in (e1)::uu____1974)
in (((FStar_Ident.id_of_text "*")), (uu____1971)))
in FStar_Parser_AST.Op (uu____1964))
in (mk1 uu____1963))
end)) e1 rest))
end
| uu____1980 -> begin
(resugar_as_app e args1)
end)
end
| FStar_Pervasives_Native.Some ("dtuple", uu____1989) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____2015))::[] -> begin
b
end
| uu____2032 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____2043 = (

let uu____2044 = (FStar_Syntax_Subst.compress body)
in uu____2044.FStar_Syntax_Syntax.n)
in (match (uu____2043) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2049) -> begin
(

let uu____2070 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____2070) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____2078 = (FStar_Options.print_implicits ())
in (match (uu____2078) with
| true -> begin
xs1
end
| uu____2079 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term body2)
in (mk1 (FStar_Parser_AST.Sum (((xs3), (body3))))))))
end))
end
| uu____2090 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____2111 -> (match (uu____2111) with
| (e1, qual) -> begin
(resugar_term e1)
end))))
in (

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____2123) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____2129) when (Prims.op_Equality ref_read FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____2134 = (FStar_List.hd args1)
in (match (uu____2134) with
| (t1, uu____2148) -> begin
(

let uu____2153 = (

let uu____2154 = (FStar_Syntax_Subst.compress t1)
in uu____2154.FStar_Syntax_Syntax.n)
in (match (uu____2153) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____2159 = (

let uu____2160 = (

let uu____2165 = (resugar_term t1)
in ((uu____2165), (f)))
in FStar_Parser_AST.Project (uu____2160))
in (mk1 uu____2159)))
end
| uu____2166 -> begin
(resugar_term t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2167) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(

let new_args = (last_two args1)
in (

let uu____2187 = (match (new_args) with
| ((a1, uu____2205))::((a2, uu____2207))::[] -> begin
((a1), (a2))
end
| uu____2238 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____2187) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____2269 = (

let uu____2270 = (FStar_Syntax_Subst.compress term)
in uu____2270.FStar_Syntax_Syntax.n)
in (match (uu____2269) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____2275) -> begin
(

let uu____2296 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____2296) with
| (x1, e2) -> begin
e2
end))
end
| uu____2303 -> begin
(failwith "wrong argument format to try_with")
end)))
in (

let body1 = (

let uu____2305 = (decomp body)
in (resugar_term uu____2305))
in (

let handler1 = (

let uu____2307 = (decomp handler)
in (resugar_term uu____2307))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____2313, uu____2314, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____2346, uu____2347, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____2368 = (

let uu____2369 = (

let uu____2378 = (resugar_body t11)
in ((uu____2378), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____2369))
in (mk1 uu____2368))
end
| uu____2381 -> begin
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
| uu____2436 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2466) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____2472) when ((Prims.op_Equality op "forall") || (Prims.op_Equality op "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____2557 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____2568 = (

let uu____2569 = (FStar_Syntax_Subst.compress body)
in uu____2569.FStar_Syntax_Syntax.n)
in (match (uu____2568) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2574) -> begin
(

let uu____2595 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____2595) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____2603 = (FStar_Options.print_implicits ())
in (match (uu____2603) with
| true -> begin
xs1
end
| uu____2604 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let uu____2612 = (

let uu____2621 = (

let uu____2622 = (FStar_Syntax_Subst.compress body2)
in uu____2622.FStar_Syntax_Syntax.n)
in (match (uu____2621) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term e1)
in (

let pats = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____2691 -> (match (uu____2691) with
| (e2, uu____2697) -> begin
(resugar_term e2)
end))))) pats)
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, uu____2700) -> begin
(

let uu____2701 = (

let uu____2704 = (

let uu____2705 = (name s r)
in (mk1 uu____2705))
in (uu____2704)::[])
in (uu____2701)::[])
end
| uu____2710 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in ((pats), (body3))))
end
| uu____2719 -> begin
(

let uu____2720 = (resugar_term body2)
in (([]), (uu____2720)))
end))
in (match (uu____2612) with
| (pats, body3) -> begin
(

let uu____2737 = (uncurry xs3 pats body3)
in (match (uu____2737) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((Prims.op_Equality op "forall")) with
| true -> begin
(mk1 (FStar_Parser_AST.QForall (((xs5), (pats1), (body4)))))
end
| uu____2778 -> begin
(mk1 (FStar_Parser_AST.QExists (((xs5), (pats1), (body4)))))
end))
end))
end))))
end))
end
| uu____2785 -> begin
(match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____2786 = (

let uu____2787 = (

let uu____2800 = (resugar_term body)
in (([]), (([])::[]), (uu____2800)))
in FStar_Parser_AST.QForall (uu____2787))
in (mk1 uu____2786))
end
| uu____2811 -> begin
(

let uu____2812 = (

let uu____2813 = (

let uu____2826 = (resugar_term body)
in (([]), (([])::[]), (uu____2826)))
in FStar_Parser_AST.QExists (uu____2813))
in (mk1 uu____2812))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____2853))::[] -> begin
(resugar b)
end
| uu____2870 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____2879 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____2880) -> begin
(

let uu____2885 = (FStar_List.hd args1)
in (match (uu____2885) with
| (e1, uu____2899) -> begin
(resugar_term e1)
end))
end
| FStar_Pervasives_Native.Some (op, arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____2944 -> (match (uu____2944) with
| (e1, qual) -> begin
(resugar_term e1)
end)))))
in (match (arity) with
| _0_40 when (_0_40 = (Prims.parse_int "0")) -> begin
(

let uu____2951 = (FStar_Parser_ToDocument.handleable_args_length op1)
in (match (uu____2951) with
| _0_41 when ((_0_41 = (Prims.parse_int "1")) && ((FStar_List.length args1) > (Prims.parse_int "0"))) -> begin
(

let uu____2958 = (

let uu____2959 = (

let uu____2966 = (

let uu____2969 = (last1 args1)
in (resugar uu____2969))
in ((op1), (uu____2966)))
in FStar_Parser_AST.Op (uu____2959))
in (mk1 uu____2958))
end
| _0_42 when ((_0_42 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____2984 = (

let uu____2985 = (

let uu____2992 = (

let uu____2995 = (last_two args1)
in (resugar uu____2995))
in ((op1), (uu____2992)))
in FStar_Parser_AST.Op (uu____2985))
in (mk1 uu____2984))
end
| _0_43 when ((_0_43 = (Prims.parse_int "3")) && ((FStar_List.length args1) > (Prims.parse_int "2"))) -> begin
(

let uu____3010 = (

let uu____3011 = (

let uu____3018 = (

let uu____3021 = (last_three args1)
in (resugar uu____3021))
in ((op1), (uu____3018)))
in FStar_Parser_AST.Op (uu____3011))
in (mk1 uu____3010))
end
| uu____3030 -> begin
(resugar_as_app e args1)
end))
end
| _0_44 when ((_0_44 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____3037 = (

let uu____3038 = (

let uu____3045 = (

let uu____3048 = (last_two args1)
in (resugar uu____3048))
in ((op1), (uu____3045)))
in FStar_Parser_AST.Op (uu____3038))
in (mk1 uu____3037))
end
| uu____3057 -> begin
(resugar_as_app e args1)
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, uu____3060, t1))::[]) -> begin
(

let bnds = (

let uu____3133 = (

let uu____3138 = (resugar_pat pat)
in (

let uu____3139 = (resugar_term e)
in ((uu____3138), (uu____3139))))
in (uu____3133)::[])
in (

let body = (resugar_term t1)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____3157, t1))::((pat2, uu____3160, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____3256 = (

let uu____3257 = (

let uu____3264 = (resugar_term e)
in (

let uu____3265 = (resugar_term t1)
in (

let uu____3266 = (resugar_term t2)
in ((uu____3264), (uu____3265), (uu____3266)))))
in FStar_Parser_AST.If (uu____3257))
in (mk1 uu____3256))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____3324 -> (match (uu____3324) with
| (pat, wopt, b) -> begin
(

let pat1 = (resugar_pat pat)
in (

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____3355 = (resugar_term e1)
in FStar_Pervasives_Native.Some (uu____3355))
end)
in (

let b1 = (resugar_term b)
in ((pat1), (wopt1), (b1)))))
end))
in (

let uu____3359 = (

let uu____3360 = (

let uu____3375 = (resugar_term e)
in (

let uu____3376 = (FStar_List.map resugar_branch branches)
in ((uu____3375), (uu____3376))))
in FStar_Parser_AST.Match (uu____3360))
in (mk1 uu____3359)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____3416) -> begin
(

let term = (match (asc) with
| FStar_Util.Inl (n1) -> begin
(resugar_term n1)
end
| FStar_Util.Inr (n1) -> begin
(resugar_comp n1)
end)
in (

let tac_opt1 = (FStar_Option.map resugar_term tac_opt)
in (

let uu____3483 = (

let uu____3484 = (

let uu____3493 = (resugar_term e)
in ((uu____3493), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____3484))
in (mk1 uu____3483))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, bnds), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____3517 = (FStar_Syntax_Subst.open_let_rec bnds body)
in (match (uu____3517) with
| (bnds1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let uu____3542 = (

let uu____3547 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____3547))
in (match (uu____3542) with
| (univs1, td) -> begin
(

let uu____3558 = (

let uu____3567 = (

let uu____3568 = (FStar_Syntax_Subst.compress td)
in uu____3568.FStar_Syntax_Syntax.n)
in (match (uu____3567) with
| FStar_Syntax_Syntax.Tm_app (uu____3579, ((t1, uu____3581))::((d, uu____3583))::[]) -> begin
((t1), (d))
end
| uu____3626 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____3558) with
| (typ, def) -> begin
(

let uu____3653 = (

let uu____3660 = (

let uu____3661 = (FStar_Syntax_Subst.compress def)
in uu____3661.FStar_Syntax_Syntax.n)
in (match (uu____3660) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____3672) -> begin
(

let uu____3693 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____3693) with
| (b1, t2) -> begin
(

let b2 = (

let uu____3707 = (FStar_Options.print_implicits ())
in (match (uu____3707) with
| true -> begin
b1
end
| uu____3708 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____3709 -> begin
(([]), (def), (false))
end))
in (match (uu____3653) with
| (binders, term, is_pat_app) -> begin
(

let uu____3733 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____3744 = (

let uu____3745 = (

let uu____3746 = (

let uu____3753 = (bv_as_unique_ident bv)
in ((uu____3753), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____3746))
in (mk_pat uu____3745))
in ((uu____3744), (term)))
end)
in (match (uu____3733) with
| (pat, term1) -> begin
(match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders ((map_opt ()) (fun uu____3789 -> (match (uu____3789) with
| (bv, q) -> begin
(

let uu____3804 = (resugar_arg_qual q)
in (FStar_Util.map_opt uu____3804 (fun q1 -> (

let uu____3816 = (

let uu____3817 = (

let uu____3824 = (bv_as_unique_ident bv)
in ((uu____3824), (q1)))
in FStar_Parser_AST.PatVar (uu____3817))
in (mk_pat uu____3816)))))
end))))
in (

let uu____3827 = (

let uu____3832 = (resugar_term term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____3832)))
in (

let uu____3835 = (universe_to_string univs1)
in ((uu____3827), (uu____3835)))))
end
| uu____3840 -> begin
(

let uu____3841 = (

let uu____3846 = (resugar_term term1)
in ((pat), (uu____3846)))
in (

let uu____3847 = (universe_to_string univs1)
in ((uu____3841), (uu____3847))))
end)
end))
end))
end))
end)))
in (

let r = (FStar_List.map resugar_one_binding bnds1)
in (

let bnds2 = (

let f = (

let uu____3893 = (

let uu____3894 = (FStar_Options.print_universes ())
in (not (uu____3894)))
in (match (uu____3893) with
| true -> begin
FStar_Pervasives_Native.fst
end
| uu____3913 -> begin
(fun uu___191_3914 -> (match (uu___191_3914) with
| ((pat, body2), univs1) -> begin
((pat), ((label univs1 body2)))
end))
end))
in (FStar_List.map f r))
in (

let body2 = (resugar_term body1)
in (mk1 (FStar_Parser_AST.Let ((((match (is_rec) with
| true -> begin
FStar_Parser_AST.Rec
end
| uu____3953 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds2), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3955) -> begin
(

let s = (

let uu____3981 = (

let uu____3982 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____3982 FStar_Util.string_of_int))
in (Prims.strcat "?u" uu____3981))
in (

let uu____3983 = (mk1 FStar_Parser_AST.Wild)
in (label s uu____3983)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___192_3993 -> (match (uu___192_3993) with
| FStar_Syntax_Syntax.Data_app -> begin
(

let rec head_fv_universes_args = (fun h -> (

let uu____4014 = (

let uu____4015 = (FStar_Syntax_Subst.compress h)
in uu____4015.FStar_Syntax_Syntax.n)
in (match (uu____4014) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4035 = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((uu____4035), ([]), ([])))
end
| FStar_Syntax_Syntax.Tm_uinst (h1, u) -> begin
(

let uu____4058 = (head_fv_universes_args h1)
in (match (uu____4058) with
| (h2, uvs, args) -> begin
((h2), ((FStar_List.append uvs u)), (args))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____4146 = (head_fv_universes_args head1)
in (match (uu____4146) with
| (h1, uvs, args') -> begin
((h1), (uvs), ((FStar_List.append args' args)))
end))
end
| uu____4218 -> begin
(

let uu____4219 = (

let uu____4220 = (

let uu____4221 = (

let uu____4222 = (resugar_term h)
in (parser_term_to_string uu____4222))
in (FStar_Util.format1 "Not an application or a fv %s" uu____4221))
in FStar_Errors.Err (uu____4220))
in (FStar_Exn.raise uu____4219))
end)))
in (

let uu____4239 = (FStar_All.try_with (fun uu___200_4274 -> (match (()) with
| () -> begin
(

let uu____4291 = (FStar_Syntax_Util.unmeta e)
in (head_fv_universes_args uu____4291))
end)) (fun uu___199_4295 -> (match (uu___199_4295) with
| FStar_Errors.Err (uu____4312) -> begin
(

let uu____4313 = (

let uu____4314 = (

let uu____4319 = (

let uu____4320 = (

let uu____4321 = (resugar_term e)
in (parser_term_to_string uu____4321))
in (FStar_Util.format1 "wrong Data_app head format %s" uu____4320))
in ((uu____4319), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4314))
in (FStar_Exn.raise uu____4313))
end)))
in (match (uu____4239) with
| (head1, universes, args) -> begin
(

let universes1 = (FStar_List.map (fun u -> (

let uu____4375 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((uu____4375), (FStar_Parser_AST.UnivApp)))) universes)
in (

let args1 = (FStar_List.filter_map (fun uu____4399 -> (match (uu____4399) with
| (t1, q) -> begin
(

let uu____4418 = (resugar_imp q)
in (match (uu____4418) with
| FStar_Pervasives_Native.Some (rimp) -> begin
(

let uu____4428 = (

let uu____4433 = (resugar_term t1)
in ((uu____4433), (rimp)))
in FStar_Pervasives_Native.Some (uu____4428))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)) args)
in (

let args2 = (

let uu____4449 = ((FStar_Parser_Const.is_tuple_data_lid' head1) || (

let uu____4451 = (FStar_Options.print_universes ())
in (not (uu____4451))))
in (match (uu____4449) with
| true -> begin
args1
end
| uu____4458 -> begin
(FStar_List.append universes1 args1)
end))
in (mk1 (FStar_Parser_AST.Construct (((head1), (args2))))))))
end)))
end
| FStar_Syntax_Syntax.Sequence -> begin
(

let term = (resugar_term e)
in (

let rec resugar_seq = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (uu____4474, ((p, t11))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____4499 = (

let uu____4500 = (

let uu____4509 = (resugar_seq t11)
in ((uu____4509), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____4500))
in (mk1 uu____4499))
end
| uu____4512 -> begin
t1
end))
in (resugar_seq term)))
end
| FStar_Syntax_Syntax.Primop -> begin
(resugar_term e)
end
| FStar_Syntax_Syntax.Masked_effect -> begin
(resugar_term e)
end
| FStar_Syntax_Syntax.Meta_smt_pat -> begin
(resugar_term e)
end
| FStar_Syntax_Syntax.Mutable_alloc -> begin
(

let term = (resugar_term e)
in (match (term.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, l, t1) -> begin
(mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.Mutable), (l), (t1)))))
end
| uu____4534 -> begin
(failwith "mutable_alloc should have let term with no qualifier")
end))
end
| FStar_Syntax_Syntax.Mutable_rval -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____4536 = (

let uu____4537 = (FStar_Syntax_Subst.compress e)
in uu____4537.FStar_Syntax_Syntax.n)
in (match (uu____4536) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____4541; FStar_Syntax_Syntax.vars = uu____4542}, ((term, uu____4544))::[]) -> begin
(resugar_term term)
end
| uu____4573 -> begin
(failwith "mutable_rval should have app term")
end)))
end))
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____4611 -> (match (uu____4611) with
| (x, uu____4617) -> begin
(resugar_term x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (l, uu____4619, p) -> begin
(

let uu____4621 = (

let uu____4622 = (

let uu____4629 = (resugar_term e)
in ((uu____4629), (l), (p)))
in FStar_Parser_AST.Labeled (uu____4622))
in (mk1 uu____4621))
end
| FStar_Syntax_Syntax.Meta_desugared (i) -> begin
(resugar_meta_desugared i)
end
| FStar_Syntax_Syntax.Meta_alien (uu____4631, s, uu____4633) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_string ((((Prims.strcat "(alien:" (Prims.strcat s ")"))), (e.FStar_Syntax_Syntax.pos))))))
end
| uu____4638 -> begin
((FStar_Errors.warn e.FStar_Syntax_Syntax.pos "Meta_alien was not a Tm_unknown");
(resugar_term e);
)
end)
end
| FStar_Syntax_Syntax.Meta_named (t1) -> begin
(mk1 (FStar_Parser_AST.Name (t1)))
end
| FStar_Syntax_Syntax.Meta_monadic (name1, t1) -> begin
(

let uu____4647 = (

let uu____4648 = (

let uu____4657 = (resugar_term e)
in (

let uu____4658 = (

let uu____4659 = (

let uu____4660 = (

let uu____4671 = (

let uu____4678 = (

let uu____4683 = (resugar_term t1)
in ((uu____4683), (FStar_Parser_AST.Nothing)))
in (uu____4678)::[])
in ((name1), (uu____4671)))
in FStar_Parser_AST.Construct (uu____4660))
in (mk1 uu____4659))
in ((uu____4657), (uu____4658), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____4648))
in (mk1 uu____4647))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____4701, t1) -> begin
(

let uu____4707 = (

let uu____4708 = (

let uu____4717 = (resugar_term e)
in (

let uu____4718 = (

let uu____4719 = (

let uu____4720 = (

let uu____4731 = (

let uu____4738 = (

let uu____4743 = (resugar_term t1)
in ((uu____4743), (FStar_Parser_AST.Nothing)))
in (uu____4738)::[])
in ((name1), (uu____4731)))
in FStar_Parser_AST.Construct (uu____4720))
in (mk1 uu____4719))
in ((uu____4717), (uu____4718), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____4708))
in (mk1 uu____4707))
end))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(mk1 FStar_Parser_AST.Wild)
end))))))
and resugar_comp : FStar_Syntax_Syntax.comp  ->  FStar_Parser_AST.term = (fun c -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a c.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (typ, u) -> begin
(

let t = (resugar_term typ)
in (match (u) with
| FStar_Pervasives_Native.None -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end
| FStar_Pervasives_Native.Some (u1) -> begin
(

let uu____4791 = (FStar_Options.print_universes ())
in (match (uu____4791) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____4811 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.GTotal (typ, u) -> begin
(

let t = (resugar_term typ)
in (match (u) with
| FStar_Pervasives_Native.None -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end
| FStar_Pervasives_Native.Some (u1) -> begin
(

let uu____4852 = (FStar_Options.print_universes ())
in (match (uu____4852) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____4872 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____4893 = (resugar_term c1.FStar_Syntax_Syntax.result_typ)
in ((uu____4893), (FStar_Parser_AST.Nothing)))
in (

let uu____4894 = (FStar_Options.print_effect_args ())
in (match (uu____4894) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (match ((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(match (c1.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::(pats)::[] -> begin
(

let uu____4974 = (

let uu____4983 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid (FStar_Pervasives_Native.fst pre))
in (match (uu____4983) with
| true -> begin
[]
end
| uu____5000 -> begin
(pre)::[]
end))
in (

let uu____5013 = (

let uu____5022 = (

let uu____5031 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid (FStar_Pervasives_Native.fst pats))
in (match (uu____5031) with
| true -> begin
[]
end
| uu____5048 -> begin
(pats)::[]
end))
in (FStar_List.append ((post)::[]) uu____5022))
in (FStar_List.append uu____4974 uu____5013)))
end
| uu____5085 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
end
| uu____5094 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
in (

let args1 = (FStar_List.map (fun uu____5114 -> (match (uu____5114) with
| (e, uu____5124) -> begin
(

let uu____5125 = (resugar_term e)
in ((uu____5125), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___193_5146 -> (match (uu___193_5146) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____5179 = (resugar_term e)
in ((uu____5179), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____5184 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____5210 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____5229 = b
in (match (uu____5229) with
| (x, aq) -> begin
(

let uu____5234 = (resugar_arg_qual aq)
in (FStar_Util.map_opt uu____5234 (fun imp -> (

let e = (resugar_term x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____5248 = (

let uu____5249 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____5249))
in (FStar_Parser_AST.mk_binder uu____5248 r FStar_Parser_AST.Type_level imp))
end
| uu____5250 -> begin
(

let uu____5251 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5251) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____5252 -> begin
(

let uu____5253 = (

let uu____5254 = (

let uu____5259 = (bv_as_unique_ident x)
in ((uu____5259), (e)))
in FStar_Parser_AST.Annotated (uu____5254))
in (FStar_Parser_AST.mk_binder uu____5253 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun x qual -> (

let mk1 = (fun a -> (

let uu____5268 = (FStar_Syntax_Syntax.range_of_bv x)
in (FStar_Parser_AST.mk_pattern a uu____5268)))
in (

let uu____5269 = (

let uu____5270 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in uu____5270.FStar_Syntax_Syntax.n)
in (match (uu____5269) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let i = (FStar_String.compare x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix)
in (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5278 = (mk1 FStar_Parser_AST.PatWild)
in FStar_Pervasives_Native.Some (uu____5278))
end
| uu____5279 -> begin
(

let uu____5280 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____5280 (fun aq -> (

let uu____5292 = (

let uu____5293 = (

let uu____5294 = (

let uu____5301 = (bv_as_unique_ident x)
in ((uu____5301), (aq)))
in FStar_Parser_AST.PatVar (uu____5294))
in (mk1 uu____5293))
in FStar_Pervasives_Native.Some (uu____5292)))))
end))
end
| uu____5304 -> begin
(

let uu____5305 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____5305 (fun aq -> (

let pat = (

let uu____5320 = (

let uu____5321 = (

let uu____5328 = (bv_as_unique_ident x)
in ((uu____5328), (aq)))
in FStar_Parser_AST.PatVar (uu____5321))
in (mk1 uu____5320))
in (

let uu____5331 = (FStar_Options.print_bound_var_types ())
in (match (uu____5331) with
| true -> begin
(

let uu____5334 = (

let uu____5335 = (

let uu____5336 = (

let uu____5341 = (resugar_term x.FStar_Syntax_Syntax.sort)
in ((pat), (uu____5341)))
in FStar_Parser_AST.PatAscribed (uu____5336))
in (mk1 uu____5335))
in FStar_Pervasives_Native.Some (uu____5334))
end
| uu____5342 -> begin
FStar_Pervasives_Native.Some (pat)
end))))))
end))))
and resugar_pat : FStar_Syntax_Syntax.pat  ->  FStar_Parser_AST.pattern = (fun p -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p))
in (

let to_arg_qual = (fun bopt -> (FStar_Util.bind_opt bopt (fun b -> (match (b) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)
end
| uu____5362 -> begin
FStar_Pervasives_Native.None
end))))
in (

let rec aux = (fun p1 imp_opt -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(mk1 (FStar_Parser_AST.PatConst (c)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, []) -> begin
(mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.cons_lid) -> begin
(

let args1 = (FStar_List.map (fun uu____5418 -> (match (uu____5418) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatList (args1))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Parser_Const.is_tuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) || (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) -> begin
(

let args1 = (FStar_List.map (fun uu____5453 -> (match (uu____5453) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (

let uu____5460 = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5460) with
| true -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (true)))))
end
| uu____5463 -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (false)))))
end)))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____5466; FStar_Syntax_Syntax.fv_delta = uu____5467; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____5494 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____5494 FStar_List.rev))
in (

let args1 = (

let uu____5510 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5530 -> (match (uu____5530) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____5510 FStar_List.rev))
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

let uu____5600 = (map21 tl1 [])
in (((hd1), ((mk1 FStar_Parser_AST.PatWild))))::uu____5600)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____5623 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____5623)
end))
in (

let args2 = (

let uu____5641 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____5641 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(

let args1 = (FStar_List.map (fun uu____5692 -> (match (uu____5692) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args1))))))
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____5702 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____5702) with
| FStar_Pervasives_Native.Some (op, uu____5710) -> begin
(mk1 (FStar_Parser_AST.PatOp ((FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5719 = (

let uu____5720 = (

let uu____5727 = (bv_as_unique_ident v1)
in (

let uu____5728 = (to_arg_qual imp_opt)
in ((uu____5727), (uu____5728))))
in FStar_Parser_AST.PatVar (uu____5720))
in (mk1 uu____5719))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____5733) -> begin
(mk1 FStar_Parser_AST.PatWild)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, term) -> begin
(

let pat = (

let uu____5741 = (

let uu____5742 = (

let uu____5749 = (bv_as_unique_ident bv)
in ((uu____5749), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))
in FStar_Parser_AST.PatVar (uu____5742))
in (mk1 uu____5741))
in (

let uu____5752 = (FStar_Options.print_bound_var_types ())
in (match (uu____5752) with
| true -> begin
(

let uu____5753 = (

let uu____5754 = (

let uu____5759 = (resugar_term term)
in ((pat), (uu____5759)))
in FStar_Parser_AST.PatAscribed (uu____5754))
in (mk1 uu____5753))
end
| uu____5760 -> begin
pat
end)))
end))
in (aux p FStar_Pervasives_Native.None)))))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___194_5766 -> (match (uu___194_5766) with
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
(match (true) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5771 -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Visible)
end)
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
(match (true) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____5774 -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Logic)
end)
end
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reifiable)
end
| FStar_Syntax_Syntax.Reflectable (uu____5775) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____5776) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____5777) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____5782) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____5791) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____5800) -> begin
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


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___195_5804 -> (match (uu___195_5804) with
| FStar_Syntax_Syntax.SetOptions (s) -> begin
FStar_Parser_AST.SetOptions (s)
end
| FStar_Syntax_Syntax.ResetOptions (s) -> begin
FStar_Parser_AST.ResetOptions (s)
end
| FStar_Syntax_Syntax.LightOff -> begin
FStar_Parser_AST.LightOff
end))


let resugar_typ : FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon) = (fun datacon_ses se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____5833, datacons) -> begin
(

let uu____5843 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5870, uu____5871, uu____5872, inductive_lid, uu____5874, uu____5875) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____5880 -> begin
(failwith "unexpected")
end))))
in (match (uu____5843) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____5899 = (FStar_Options.print_implicits ())
in (match (uu____5899) with
| true -> begin
bs
end
| uu____5900 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 ((map_opt ()) (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____5909 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___196_5914 -> (match (uu___196_5914) with
| FStar_Syntax_Syntax.RecordType (uu____5915) -> begin
true
end
| uu____5924 -> begin
false
end))))
in (match (uu____5909) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5972, univs1, term, uu____5975, num, uu____5977) -> begin
(

let uu____5982 = (

let uu____5983 = (FStar_Syntax_Subst.compress term)
in uu____5983.FStar_Syntax_Syntax.n)
in (match (uu____5982) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____5997) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____6058 -> (match (uu____6058) with
| (b, qual) -> begin
(

let uu____6073 = (

let uu____6074 = (bv_as_unique_ident b)
in (FStar_Syntax_Util.unmangle_field_name uu____6074))
in (

let uu____6075 = (resugar_term b.FStar_Syntax_Syntax.sort)
in ((uu____6073), (uu____6075), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____6086 -> begin
(failwith "unexpected")
end))
end
| uu____6097 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____6151 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____6218, num, uu____6220) -> begin
(

let c = (

let uu____6238 = (

let uu____6241 = (resugar_term term)
in FStar_Pervasives_Native.Some (uu____6241))
in ((l.FStar_Ident.ident), (uu____6238), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____6258 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____6334 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____6355 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____6355; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme' : Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun name ts -> (

let uu____6372 = ts
in (match (uu____6372) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____6380 = (

let uu____6381 = (

let uu____6394 = (

let uu____6403 = (

let uu____6410 = (

let uu____6411 = (

let uu____6424 = (resugar_term typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____6424)))
in FStar_Parser_AST.TyconAbbrev (uu____6411))
in ((uu____6410), (FStar_Pervasives_Native.None)))
in (uu____6403)::[])
in ((false), (uu____6394)))
in FStar_Parser_AST.Tycon (uu____6381))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6380)))
end)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (resugar_tscheme' "tsheme" ts))


let resugar_eff_decl : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun for_free r q ed -> (

let resugar_action = (fun d for_free1 -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____6483 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____6483) with
| (bs, action_defn) -> begin
(

let uu____6490 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____6490) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____6498 = (FStar_Options.print_implicits ())
in (match (uu____6498) with
| true -> begin
action_params
end
| uu____6499 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____6503 = (FStar_All.pipe_right action_params1 ((map_opt ()) (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____6503 FStar_List.rev))
in (

let action_defn1 = (resugar_term action_defn)
in (

let action_typ1 = (resugar_term action_typ)
in (match (for_free1) with
| true -> begin
(

let a = (

let uu____6517 = (

let uu____6528 = (FStar_Ident.lid_of_str "construct")
in ((uu____6528), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____6517))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____6574 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____6602 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____6602) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____6610 = (FStar_Options.print_implicits ())
in (match (uu____6610) with
| true -> begin
eff_binders
end
| uu____6611 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____6615 = (FStar_All.pipe_right eff_binders1 ((map_opt ()) (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____6615 FStar_List.rev))
in (

let eff_typ1 = (resugar_term eff_typ)
in (

let ret_wp = (resugar_tscheme' "ret_wp" ed.FStar_Syntax_Syntax.ret_wp)
in (

let bind_wp = (resugar_tscheme' "bind_wp" ed.FStar_Syntax_Syntax.ret_wp)
in (

let if_then_else1 = (resugar_tscheme' "if_then_else" ed.FStar_Syntax_Syntax.if_then_else)
in (

let ite_wp = (resugar_tscheme' "ite_wp" ed.FStar_Syntax_Syntax.ite_wp)
in (

let stronger = (resugar_tscheme' "stronger" ed.FStar_Syntax_Syntax.stronger)
in (

let close_wp = (resugar_tscheme' "close_wp" ed.FStar_Syntax_Syntax.close_wp)
in (

let assert_p = (resugar_tscheme' "assert_p" ed.FStar_Syntax_Syntax.assert_p)
in (

let assume_p = (resugar_tscheme' "assume_p" ed.FStar_Syntax_Syntax.assume_p)
in (

let null_wp = (resugar_tscheme' "null_wp" ed.FStar_Syntax_Syntax.null_wp)
in (

let trivial = (resugar_tscheme' "trivial" ed.FStar_Syntax_Syntax.trivial)
in (

let repr = (resugar_tscheme' "repr" (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let return_repr = (resugar_tscheme' "return_repr" ed.FStar_Syntax_Syntax.return_repr)
in (

let bind_repr = (resugar_tscheme' "bind_repr" ed.FStar_Syntax_Syntax.bind_repr)
in (

let mandatory_members_decls = (match (for_free) with
| true -> begin
(repr)::(return_repr)::(bind_repr)::[]
end
| uu____6647 -> begin
(repr)::(return_repr)::(bind_repr)::(ret_wp)::(bind_wp)::(if_then_else1)::(ite_wp)::(stronger)::(close_wp)::(assert_p)::(assume_p)::(null_wp)::(trivial)::[]
end)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls)))))))))))))))))))))))))
end)))))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____6673) -> begin
(

let uu____6682 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6704) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6721) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____6728) -> begin
false
end
| uu____6743 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____6682) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____6775 se1 -> (match (uu____6775) with
| (datacon_ses1, tycons) -> begin
(

let uu____6801 = (resugar_typ datacon_ses1 se1)
in (match (uu____6801) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____6816 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____6816) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____6851 = (

let uu____6852 = (

let uu____6853 = (

let uu____6866 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (uu____6866)))
in FStar_Parser_AST.Tycon (uu____6853))
in (decl'_to_decl se uu____6852))
in FStar_Pervasives_Native.Some (uu____6851))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____6897, uu____6898, uu____6899, uu____6900, uu____6901) -> begin
(

let uu____6906 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____6906))
end
| uu____6909 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____6912 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____6918) -> begin
(

let uu____6923 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___197_6929 -> (match (uu___197_6929) with
| FStar_Syntax_Syntax.Projector (uu____6930, uu____6931) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____6932) -> begin
true
end
| uu____6933 -> begin
false
end))))
in (match (uu____6923) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6936 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____6956) -> begin
(

let uu____6969 = (decl'_to_decl se (FStar_Parser_AST.TopLevelLet (((isrec), (lets)))))
in FStar_Pervasives_Native.Some (uu____6969))
end
| uu____6976 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____6980, fml) -> begin
(

let uu____6982 = (

let uu____6983 = (

let uu____6984 = (

let uu____6989 = (resugar_term fml)
in ((lid.FStar_Ident.ident), (uu____6989)))
in FStar_Parser_AST.Assume (uu____6984))
in (decl'_to_decl se uu____6983))
in FStar_Pervasives_Native.Some (uu____6982))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____6991 = (resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____6991))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let uu____6993 = (resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____6993))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____7002, t) -> begin
(

let uu____7014 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____7014))
end
| uu____7015 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____7023, t) -> begin
(

let uu____7035 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____7035))
end
| uu____7036 -> begin
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
| uu____7060 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____7069 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____7069)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) -> begin
(

let uu____7079 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____7079) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____7089 = (FStar_Options.print_implicits ())
in (match (uu____7089) with
| true -> begin
bs1
end
| uu____7090 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 ((map_opt ()) (fun b -> (resugar_binder b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____7098 = (

let uu____7099 = (

let uu____7100 = (

let uu____7113 = (

let uu____7122 = (

let uu____7129 = (

let uu____7130 = (

let uu____7143 = (resugar_comp c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____7143)))
in FStar_Parser_AST.TyconAbbrev (uu____7130))
in ((uu____7129), (FStar_Pervasives_Native.None)))
in (uu____7122)::[])
in ((false), (uu____7113)))
in FStar_Parser_AST.Tycon (uu____7100))
in (decl'_to_decl se uu____7099))
in FStar_Pervasives_Native.Some (uu____7098))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____7171 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____7171))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____7175 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___198_7181 -> (match (uu___198_7181) with
| FStar_Syntax_Syntax.Projector (uu____7182, uu____7183) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____7184) -> begin
true
end
| uu____7185 -> begin
false
end))))
in (match (uu____7175) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7188 -> begin
(

let t' = (

let uu____7190 = ((

let uu____7193 = (FStar_Options.print_universes ())
in (not (uu____7193))) || (FStar_List.isEmpty uvs))
in (match (uu____7190) with
| true -> begin
(resugar_term t)
end
| uu____7194 -> begin
(

let uu____7195 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____7195) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____7203 = (resugar_term t1)
in (label universes uu____7203)))
end))
end))
in (

let uu____7204 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____7204)))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7205) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7222) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____7237) -> begin
FStar_Pervasives_Native.None
end))





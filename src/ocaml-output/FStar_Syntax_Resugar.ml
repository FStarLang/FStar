
open Prims
open FStar_Pervasives

let doc_to_string : FStar_Pprint.document  ->  Prims.string = (fun doc1 -> (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1))


let parser_term_to_string : FStar_Parser_AST.term  ->  Prims.string = (fun t -> (

let uu____9 = (FStar_Parser_ToDocument.term_to_document t)
in (doc_to_string uu____9)))


let map_opt : 'a 'b . ('a  ->  'b FStar_Pervasives_Native.option)  ->  'a Prims.list  ->  'b Prims.list = (fun f l -> (

let uu____43 = (FStar_Util.choose_map (fun uu____53 x -> (

let uu____55 = (f x)
in ((()), (uu____55)))) () l)
in (FStar_Pervasives_Native.snd uu____43)))


let bv_as_unique_ident : FStar_Syntax_Syntax.bv  ->  FStar_Ident.ident = (fun x -> (

let unique_name = (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)) with
| true -> begin
(

let uu____67 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____67))
end
| uu____68 -> begin
x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)
in (FStar_Ident.mk_ident ((unique_name), (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))))


let filter_imp : 'Auu____73 . ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____73 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___186_127 -> (match (uu___186_127) with
| (uu____134, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____135))) -> begin
false
end
| uu____138 -> begin
true
end)))))


let label : Prims.string  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun s t -> (match ((s = "")) with
| true -> begin
t
end
| uu____153 -> begin
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
| uu____183 -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
end)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality))
end))


let resugar_imp : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.imp = (fun q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Parser_AST.Nothing
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) -> begin
FStar_Parser_AST.Hash
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> begin
(failwith "Not an imp")
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
(failwith "Not an imp")
end))


let rec universe_to_int : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe) = (fun n1 u -> (match (u) with
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(universe_to_int (n1 + (Prims.parse_int "1")) u1)
end
| uu____213 -> begin
((n1), (u))
end))


let universe_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun univs1 -> (

let uu____222 = (FStar_Options.print_universes ())
in (match (uu____222) with
| true -> begin
(

let uu____223 = (FStar_List.map (fun x -> x.FStar_Ident.idText) univs1)
in (FStar_All.pipe_right uu____223 (FStar_String.concat ", ")))
end
| uu____230 -> begin
""
end)))


let rec resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____256) -> begin
(

let uu____257 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____257) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____264 = (

let uu____265 = (

let uu____266 = (

let uu____277 = (FStar_Util.string_of_int n1)
in ((uu____277), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____266))
in FStar_Parser_AST.Const (uu____265))
in (mk1 uu____264 r))
end
| uu____288 -> begin
(

let e1 = (

let uu____290 = (

let uu____291 = (

let uu____292 = (

let uu____303 = (FStar_Util.string_of_int n1)
in ((uu____303), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____292))
in FStar_Parser_AST.Const (uu____291))
in (mk1 uu____290 r))
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
| uu____320 -> begin
(

let t = (

let uu____324 = (

let uu____325 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____325))
in (mk1 uu____324 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____331 = (

let uu____332 = (

let uu____339 = (resugar_universe x r)
in ((acc), (uu____339), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____332))
in (mk1 uu____331 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____341) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id = (

let uu____352 = (

let uu____357 = (

let uu____358 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____358))
in ((uu____357), (r)))
in (FStar_Ident.mk_ident uu____352))
in (mk1 (FStar_Parser_AST.Uvar (id)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___187_378 -> (match (uu___187_378) with
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
| uu____469 -> begin
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
| uu____496 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____506 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____506 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____514 -> begin
(

let op = (

let uu____518 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (x) with
| FStar_Pervasives_Native.Some (op, uu____552) -> begin
(Prims.strcat acc op)
end
| FStar_Pervasives_Native.None -> begin
(failwith "wrong composed operator format")
end)) "" uu____518))
in FStar_Pervasives_Native.Some (((op), ((Prims.parse_int "0")))))
end))
end
| uu____565 -> begin
FStar_Pervasives_Native.None
end)
end)))


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.strcat_lid), ("^")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____739 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____739) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), ((Prims.parse_int "0"))))
end
| uu____787 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((length1 = (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____800 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), ((Prims.parse_int "0"))))
end
| uu____817 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), ((Prims.parse_int "0"))))
end
| uu____828 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), ((Prims.parse_int "0"))))
end
| uu____839 -> begin
(

let uu____840 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____840) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), ((Prims.parse_int "0"))))
end
| uu____851 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____856 = (

let uu____857 = (FStar_Syntax_Subst.compress t)
in uu____857.FStar_Syntax_Syntax.n)
in (match (uu____856) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((length1 = (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____873 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____880 = (string_to_op s)
in (match (uu____880) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____906 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____919 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____928 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____933) -> begin
true
end
| uu____934 -> begin
false
end))


let rec resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____965 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____965)))
in (

let var = (fun a r -> (

let uu____973 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Var (uu____973)))
in (

let uu____974 = (

let uu____975 = (FStar_Syntax_Subst.compress t)
in uu____975.FStar_Syntax_Syntax.n)
in (match (uu____974) with
| FStar_Syntax_Syntax.Tm_delayed (uu____978) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____1005 = (

let uu____1008 = (bv_as_unique_ident x)
in (uu____1008)::[])
in (FStar_Ident.lid_of_ids uu____1005))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____1011 = (

let uu____1014 = (bv_as_unique_ident x)
in (uu____1014)::[])
in (FStar_Ident.lid_of_ids uu____1011))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let a = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((length1 = (Prims.parse_int "0"))) with
| true -> begin
a.FStar_Ident.str
end
| uu____1023 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.strcat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____1032 = (

let uu____1033 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____1033))
in (mk1 uu____1032)))
end
| uu____1034 -> begin
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
| uu____1043 -> begin
(failwith "wrong projector format")
end)))
end
| uu____1046 -> begin
(

let uu____1047 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____1050 = (

let uu____1051 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____1051))
in (

let uu____1052 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____1050 <> uu____1052))))
in (match (uu____1047) with
| true -> begin
(

let uu____1053 = (var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1053))
end
| uu____1054 -> begin
(

let uu____1055 = (name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1055))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let uu____1062 = (FStar_Options.print_universes ())
in (match (uu____1062) with
| true -> begin
(

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (

let uu____1069 = (

let uu____1070 = (

let uu____1077 = (resugar_universe x t.FStar_Syntax_Syntax.pos)
in ((acc), (uu____1077), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____1070))
in (mk1 uu____1069))) e1 universes))
end
| uu____1078 -> begin
(resugar_term e)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1080 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____1080) with
| true -> begin
(

let uu____1081 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1081))
end
| uu____1082 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____1084 = (name "Type0" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1084))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____1085 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1085))
end
| uu____1086 -> begin
(

let uu____1087 = (FStar_Options.print_universes ())
in (match (uu____1087) with
| true -> begin
(

let u1 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in (

let l = (FStar_Ident.lid_of_path (("Type")::[]) t.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((l), ((((u1), (FStar_Parser_AST.UnivApp)))::[])))))))
end
| uu____1104 -> begin
(

let uu____1105 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1105))
end))
end)
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1108) -> begin
(

let uu____1129 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____1129) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1137 = (FStar_Options.print_implicits ())
in (match (uu____1137) with
| true -> begin
xs1
end
| uu____1138 -> begin
(filter_imp xs1)
end))
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____1151 -> (match (uu____1151) with
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

let uu____1181 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____1181) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1189 = (FStar_Options.print_implicits ())
in (match (uu____1189) with
| true -> begin
xs1
end
| uu____1190 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp body1)
in (

let xs3 = (

let uu____1195 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____1195 FStar_List.rev))
in (

let rec aux = (fun body3 uu___188_1214 -> (match (uu___188_1214) with
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

let uu____1230 = (

let uu____1235 = (

let uu____1236 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1236)::[])
in (FStar_Syntax_Subst.open_term uu____1235 phi))
in (match (uu____1230) with
| (x1, phi1) -> begin
(

let b = (

let uu____1240 = (

let uu____1243 = (FStar_List.hd x1)
in (resugar_binder uu____1243 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____1240))
in (

let uu____1248 = (

let uu____1249 = (

let uu____1254 = (resugar_term phi1)
in ((b), (uu____1254)))
in FStar_Parser_AST.Refine (uu____1249))
in (mk1 uu____1248)))
end))
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___189_1296 -> (match (uu___189_1296) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____1366 -> begin
(failwith "last of an empty list")
end))
in (

let rec last_two = (fun uu___190_1402 -> (match (uu___190_1402) with
| [] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (uu____1433)::[] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (a1)::(a2)::[] -> begin
(a1)::(a2)::[]
end
| (uu____1510)::t1 -> begin
(last_two t1)
end))
in (

let rec last_three = (fun uu___191_1551 -> (match (uu___191_1551) with
| [] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1582)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1609)::(uu____1610)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (a1)::(a2)::(a3)::[] -> begin
(a1)::(a2)::(a3)::[]
end
| (uu____1718)::t1 -> begin
(last_three t1)
end))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_All.pipe_right args1 (FStar_List.map (fun uu____1804 -> (match (uu____1804) with
| (e2, qual) -> begin
(

let uu____1823 = (resugar_term e2)
in ((uu____1823), (qual)))
end))))
in (

let e2 = (resugar_term e1)
in (FStar_List.fold_left (fun acc uu____1839 -> (match (uu____1839) with
| (x, qual) -> begin
(

let uu____1852 = (

let uu____1853 = (

let uu____1860 = (resugar_imp qual)
in ((acc), (x), (uu____1860)))
in FStar_Parser_AST.App (uu____1853))
in (mk1 uu____1852))
end)) e2 args2))))
in (

let args1 = (

let uu____1870 = (FStar_Options.print_implicits ())
in (match (uu____1870) with
| true -> begin
args
end
| uu____1879 -> begin
(filter_imp args)
end))
in (

let uu____1882 = (resugar_term_as_op e)
in (match (uu____1882) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____1893) -> begin
(match (args1) with
| ((fst1, uu____1899))::((snd1, uu____1901))::rest -> begin
(

let e1 = (

let uu____1932 = (

let uu____1933 = (

let uu____1940 = (

let uu____1943 = (resugar_term fst1)
in (

let uu____1944 = (

let uu____1947 = (resugar_term snd1)
in (uu____1947)::[])
in (uu____1943)::uu____1944))
in (((FStar_Ident.id_of_text "*")), (uu____1940)))
in FStar_Parser_AST.Op (uu____1933))
in (mk1 uu____1932))
in (FStar_List.fold_left (fun acc uu____1960 -> (match (uu____1960) with
| (x, uu____1966) -> begin
(

let uu____1967 = (

let uu____1968 = (

let uu____1975 = (

let uu____1978 = (

let uu____1981 = (resugar_term x)
in (uu____1981)::[])
in (e1)::uu____1978)
in (((FStar_Ident.id_of_text "*")), (uu____1975)))
in FStar_Parser_AST.Op (uu____1968))
in (mk1 uu____1967))
end)) e1 rest))
end
| uu____1984 -> begin
(resugar_as_app e args1)
end)
end
| FStar_Pervasives_Native.Some ("dtuple", uu____1993) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____2019))::[] -> begin
b
end
| uu____2036 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____2047 = (

let uu____2048 = (FStar_Syntax_Subst.compress body)
in uu____2048.FStar_Syntax_Syntax.n)
in (match (uu____2047) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2053) -> begin
(

let uu____2074 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____2074) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____2082 = (FStar_Options.print_implicits ())
in (match (uu____2082) with
| true -> begin
xs1
end
| uu____2083 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term body2)
in (mk1 (FStar_Parser_AST.Sum (((xs3), (body3))))))))
end))
end
| uu____2094 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____2115 -> (match (uu____2115) with
| (e1, qual) -> begin
(resugar_term e1)
end))))
in (

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____2127) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____2133) when (ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____2138 = (FStar_List.hd args1)
in (match (uu____2138) with
| (t1, uu____2152) -> begin
(

let uu____2157 = (

let uu____2158 = (FStar_Syntax_Subst.compress t1)
in uu____2158.FStar_Syntax_Syntax.n)
in (match (uu____2157) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____2163 = (

let uu____2164 = (

let uu____2169 = (resugar_term t1)
in ((uu____2169), (f)))
in FStar_Parser_AST.Project (uu____2164))
in (mk1 uu____2163)))
end
| uu____2170 -> begin
(resugar_term t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2171) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(

let new_args = (last_two args1)
in (

let uu____2191 = (match (new_args) with
| ((a1, uu____2209))::((a2, uu____2211))::[] -> begin
((a1), (a2))
end
| uu____2242 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____2191) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____2273 = (

let uu____2274 = (FStar_Syntax_Subst.compress term)
in uu____2274.FStar_Syntax_Syntax.n)
in (match (uu____2273) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____2279) -> begin
(

let uu____2300 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____2300) with
| (x1, e2) -> begin
e2
end))
end
| uu____2307 -> begin
(failwith "wrong argument format to try_with")
end)))
in (

let body1 = (

let uu____2309 = (decomp body)
in (resugar_term uu____2309))
in (

let handler1 = (

let uu____2311 = (decomp handler)
in (resugar_term uu____2311))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____2317, uu____2318, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____2350, uu____2351, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____2372 = (

let uu____2373 = (

let uu____2382 = (resugar_body t11)
in ((uu____2382), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____2373))
in (mk1 uu____2372))
end
| uu____2385 -> begin
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
| uu____2440 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2470) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____2476) when ((op = "forall") || (op = "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____2561 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____2572 = (

let uu____2573 = (FStar_Syntax_Subst.compress body)
in uu____2573.FStar_Syntax_Syntax.n)
in (match (uu____2572) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2578) -> begin
(

let uu____2599 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____2599) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____2607 = (FStar_Options.print_implicits ())
in (match (uu____2607) with
| true -> begin
xs1
end
| uu____2608 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let uu____2616 = (

let uu____2625 = (

let uu____2626 = (FStar_Syntax_Subst.compress body2)
in uu____2626.FStar_Syntax_Syntax.n)
in (match (uu____2625) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term e1)
in (

let pats = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____2695 -> (match (uu____2695) with
| (e2, uu____2701) -> begin
(resugar_term e2)
end))))) pats)
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, uu____2704) -> begin
(

let uu____2705 = (

let uu____2708 = (

let uu____2709 = (name s r)
in (mk1 uu____2709))
in (uu____2708)::[])
in (uu____2705)::[])
end
| uu____2714 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in ((pats), (body3))))
end
| uu____2723 -> begin
(

let uu____2724 = (resugar_term body2)
in (([]), (uu____2724)))
end))
in (match (uu____2616) with
| (pats, body3) -> begin
(

let uu____2741 = (uncurry xs3 pats body3)
in (match (uu____2741) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((op = "forall")) with
| true -> begin
(mk1 (FStar_Parser_AST.QForall (((xs5), (pats1), (body4)))))
end
| uu____2782 -> begin
(mk1 (FStar_Parser_AST.QExists (((xs5), (pats1), (body4)))))
end))
end))
end))))
end))
end
| uu____2789 -> begin
(match ((op = "forall")) with
| true -> begin
(

let uu____2790 = (

let uu____2791 = (

let uu____2804 = (resugar_term body)
in (([]), (([])::[]), (uu____2804)))
in FStar_Parser_AST.QForall (uu____2791))
in (mk1 uu____2790))
end
| uu____2815 -> begin
(

let uu____2816 = (

let uu____2817 = (

let uu____2830 = (resugar_term body)
in (([]), (([])::[]), (uu____2830)))
in FStar_Parser_AST.QExists (uu____2817))
in (mk1 uu____2816))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____2857))::[] -> begin
(resugar b)
end
| uu____2874 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____2883 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____2884) -> begin
(

let uu____2889 = (FStar_List.hd args1)
in (match (uu____2889) with
| (e1, uu____2903) -> begin
(resugar_term e1)
end))
end
| FStar_Pervasives_Native.Some (op, arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____2948 -> (match (uu____2948) with
| (e1, qual) -> begin
(resugar_term e1)
end)))))
in (match (arity) with
| _0_40 when (_0_40 = (Prims.parse_int "0")) -> begin
(

let uu____2955 = (FStar_Parser_ToDocument.handleable_args_length op1)
in (match (uu____2955) with
| _0_41 when ((_0_41 = (Prims.parse_int "1")) && ((FStar_List.length args1) > (Prims.parse_int "0"))) -> begin
(

let uu____2962 = (

let uu____2963 = (

let uu____2970 = (

let uu____2973 = (last1 args1)
in (resugar uu____2973))
in ((op1), (uu____2970)))
in FStar_Parser_AST.Op (uu____2963))
in (mk1 uu____2962))
end
| _0_42 when ((_0_42 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____2988 = (

let uu____2989 = (

let uu____2996 = (

let uu____2999 = (last_two args1)
in (resugar uu____2999))
in ((op1), (uu____2996)))
in FStar_Parser_AST.Op (uu____2989))
in (mk1 uu____2988))
end
| _0_43 when ((_0_43 = (Prims.parse_int "3")) && ((FStar_List.length args1) > (Prims.parse_int "2"))) -> begin
(

let uu____3014 = (

let uu____3015 = (

let uu____3022 = (

let uu____3025 = (last_three args1)
in (resugar uu____3025))
in ((op1), (uu____3022)))
in FStar_Parser_AST.Op (uu____3015))
in (mk1 uu____3014))
end
| uu____3034 -> begin
(resugar_as_app e args1)
end))
end
| _0_44 when ((_0_44 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____3041 = (

let uu____3042 = (

let uu____3049 = (

let uu____3052 = (last_two args1)
in (resugar uu____3052))
in ((op1), (uu____3049)))
in FStar_Parser_AST.Op (uu____3042))
in (mk1 uu____3041))
end
| uu____3061 -> begin
(resugar_as_app e args1)
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, uu____3064, t1))::[]) -> begin
(

let bnds = (

let uu____3137 = (

let uu____3142 = (resugar_pat pat)
in (

let uu____3143 = (resugar_term e)
in ((uu____3142), (uu____3143))))
in (uu____3137)::[])
in (

let body = (resugar_term t1)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____3161, t1))::((pat2, uu____3164, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____3260 = (

let uu____3261 = (

let uu____3268 = (resugar_term e)
in (

let uu____3269 = (resugar_term t1)
in (

let uu____3270 = (resugar_term t2)
in ((uu____3268), (uu____3269), (uu____3270)))))
in FStar_Parser_AST.If (uu____3261))
in (mk1 uu____3260))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____3328 -> (match (uu____3328) with
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

let uu____3359 = (resugar_term e1)
in FStar_Pervasives_Native.Some (uu____3359))
end)
in (

let b1 = (resugar_term b)
in ((pat1), (wopt1), (b1)))))
end))
in (

let uu____3363 = (

let uu____3364 = (

let uu____3379 = (resugar_term e)
in (

let uu____3380 = (FStar_List.map resugar_branch branches)
in ((uu____3379), (uu____3380))))
in FStar_Parser_AST.Match (uu____3364))
in (mk1 uu____3363)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____3420) -> begin
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

let uu____3487 = (

let uu____3488 = (

let uu____3497 = (resugar_term e)
in ((uu____3497), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____3488))
in (mk1 uu____3487))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, bnds), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____3521 = (FStar_Syntax_Subst.open_let_rec bnds body)
in (match (uu____3521) with
| (bnds1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let uu____3546 = (

let uu____3551 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____3551))
in (match (uu____3546) with
| (univs1, td) -> begin
(

let uu____3562 = (

let uu____3571 = (

let uu____3572 = (FStar_Syntax_Subst.compress td)
in uu____3572.FStar_Syntax_Syntax.n)
in (match (uu____3571) with
| FStar_Syntax_Syntax.Tm_app (uu____3583, ((t1, uu____3585))::((d, uu____3587))::[]) -> begin
((t1), (d))
end
| uu____3630 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____3562) with
| (typ, def) -> begin
(

let uu____3657 = (

let uu____3664 = (

let uu____3665 = (FStar_Syntax_Subst.compress def)
in uu____3665.FStar_Syntax_Syntax.n)
in (match (uu____3664) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____3676) -> begin
(

let uu____3697 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____3697) with
| (b1, t2) -> begin
(

let b2 = (

let uu____3711 = (FStar_Options.print_implicits ())
in (match (uu____3711) with
| true -> begin
b1
end
| uu____3712 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____3713 -> begin
(([]), (def), (false))
end))
in (match (uu____3657) with
| (binders, term, is_pat_app) -> begin
(

let uu____3737 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____3748 = (

let uu____3749 = (

let uu____3750 = (

let uu____3757 = (bv_as_unique_ident bv)
in ((uu____3757), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____3750))
in (mk_pat uu____3749))
in ((uu____3748), (term)))
end)
in (match (uu____3737) with
| (pat, term1) -> begin
(match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders (map_opt (fun uu____3793 -> (match (uu____3793) with
| (bv, q) -> begin
(

let uu____3808 = (resugar_arg_qual q)
in (FStar_Util.map_opt uu____3808 (fun q1 -> (

let uu____3820 = (

let uu____3821 = (

let uu____3828 = (bv_as_unique_ident bv)
in ((uu____3828), (q1)))
in FStar_Parser_AST.PatVar (uu____3821))
in (mk_pat uu____3820)))))
end))))
in (

let uu____3831 = (

let uu____3836 = (resugar_term term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____3836)))
in (

let uu____3839 = (universe_to_string univs1)
in ((uu____3831), (uu____3839)))))
end
| uu____3844 -> begin
(

let uu____3845 = (

let uu____3850 = (resugar_term term1)
in ((pat), (uu____3850)))
in (

let uu____3851 = (universe_to_string univs1)
in ((uu____3845), (uu____3851))))
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

let uu____3897 = (

let uu____3898 = (FStar_Options.print_universes ())
in (not (uu____3898)))
in (match (uu____3897) with
| true -> begin
FStar_Pervasives_Native.fst
end
| uu____3917 -> begin
(fun uu___192_3918 -> (match (uu___192_3918) with
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
| uu____3957 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds2), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____3959) -> begin
(

let s = (

let uu____3985 = (

let uu____3986 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____3986 FStar_Util.string_of_int))
in (Prims.strcat "?u" uu____3985))
in (

let uu____3987 = (mk1 FStar_Parser_AST.Wild)
in (label s uu____3987)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___193_3997 -> (match (uu___193_3997) with
| FStar_Syntax_Syntax.Data_app -> begin
(

let rec head_fv_universes_args = (fun h -> (

let uu____4018 = (

let uu____4019 = (FStar_Syntax_Subst.compress h)
in uu____4019.FStar_Syntax_Syntax.n)
in (match (uu____4018) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____4039 = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((uu____4039), ([]), ([])))
end
| FStar_Syntax_Syntax.Tm_uinst (h1, u) -> begin
(

let uu____4062 = (head_fv_universes_args h1)
in (match (uu____4062) with
| (h2, uvs, args) -> begin
((h2), ((FStar_List.append uvs u)), (args))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____4150 = (head_fv_universes_args head1)
in (match (uu____4150) with
| (h1, uvs, args') -> begin
((h1), (uvs), ((FStar_List.append args' args)))
end))
end
| uu____4222 -> begin
(

let uu____4223 = (

let uu____4224 = (

let uu____4225 = (

let uu____4226 = (resugar_term h)
in (parser_term_to_string uu____4226))
in (FStar_Util.format1 "Not an application or a fv %s" uu____4225))
in FStar_Errors.Err (uu____4224))
in (FStar_Exn.raise uu____4223))
end)))
in (

let uu____4243 = try
(match (()) with
| () -> begin
(

let uu____4295 = (FStar_Syntax_Util.unmeta e)
in (head_fv_universes_args uu____4295))
end)
with
| FStar_Errors.Err (uu____4316) -> begin
(

let uu____4317 = (

let uu____4318 = (

let uu____4323 = (

let uu____4324 = (

let uu____4325 = (resugar_term e)
in (parser_term_to_string uu____4325))
in (FStar_Util.format1 "wrong Data_app head format %s" uu____4324))
in ((uu____4323), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____4318))
in (FStar_Exn.raise uu____4317))
end
in (match (uu____4243) with
| (head1, universes, args) -> begin
(

let universes1 = (FStar_List.map (fun u -> (

let uu____4379 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((uu____4379), (FStar_Parser_AST.UnivApp)))) universes)
in (

let args1 = (FStar_List.map (fun uu____4402 -> (match (uu____4402) with
| (t1, q) -> begin
(

let uu____4419 = (resugar_term t1)
in (

let uu____4420 = (resugar_imp q)
in ((uu____4419), (uu____4420))))
end)) args)
in (

let args2 = (

let uu____4428 = ((FStar_Parser_Const.is_tuple_data_lid' head1) || (

let uu____4430 = (FStar_Options.print_universes ())
in (not (uu____4430))))
in (match (uu____4428) with
| true -> begin
args1
end
| uu____4437 -> begin
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
| FStar_Parser_AST.Let (uu____4453, ((p, t11))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____4478 = (

let uu____4479 = (

let uu____4488 = (resugar_seq t11)
in ((uu____4488), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____4479))
in (mk1 uu____4478))
end
| uu____4491 -> begin
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
| uu____4513 -> begin
(failwith "mutable_alloc should have let term with no qualifier")
end))
end
| FStar_Syntax_Syntax.Mutable_rval -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____4515 = (

let uu____4516 = (FStar_Syntax_Subst.compress e)
in uu____4516.FStar_Syntax_Syntax.n)
in (match (uu____4515) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____4520; FStar_Syntax_Syntax.vars = uu____4521}, ((term, uu____4523))::[]) -> begin
(resugar_term term)
end
| uu____4552 -> begin
(failwith "mutable_rval should have app term")
end)))
end))
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____4590 -> (match (uu____4590) with
| (x, uu____4596) -> begin
(resugar_term x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (l, uu____4598, p) -> begin
(

let uu____4600 = (

let uu____4601 = (

let uu____4608 = (resugar_term e)
in ((uu____4608), (l), (p)))
in FStar_Parser_AST.Labeled (uu____4601))
in (mk1 uu____4600))
end
| FStar_Syntax_Syntax.Meta_desugared (i) -> begin
(resugar_meta_desugared i)
end
| FStar_Syntax_Syntax.Meta_alien (uu____4610, s) -> begin
(resugar_term e)
end
| FStar_Syntax_Syntax.Meta_named (t1) -> begin
(mk1 (FStar_Parser_AST.Name (t1)))
end
| FStar_Syntax_Syntax.Meta_monadic (name1, t1) -> begin
(

let uu____4619 = (

let uu____4620 = (

let uu____4629 = (resugar_term e)
in (

let uu____4630 = (

let uu____4631 = (

let uu____4632 = (

let uu____4643 = (

let uu____4650 = (

let uu____4655 = (resugar_term t1)
in ((uu____4655), (FStar_Parser_AST.Nothing)))
in (uu____4650)::[])
in ((name1), (uu____4643)))
in FStar_Parser_AST.Construct (uu____4632))
in (mk1 uu____4631))
in ((uu____4629), (uu____4630), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____4620))
in (mk1 uu____4619))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____4673, t1) -> begin
(

let uu____4679 = (

let uu____4680 = (

let uu____4689 = (resugar_term e)
in (

let uu____4690 = (

let uu____4691 = (

let uu____4692 = (

let uu____4703 = (

let uu____4710 = (

let uu____4715 = (resugar_term t1)
in ((uu____4715), (FStar_Parser_AST.Nothing)))
in (uu____4710)::[])
in ((name1), (uu____4703)))
in FStar_Parser_AST.Construct (uu____4692))
in (mk1 uu____4691))
in ((uu____4689), (uu____4690), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____4680))
in (mk1 uu____4679))
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

let uu____4763 = (FStar_Options.print_universes ())
in (match (uu____4763) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____4783 -> begin
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

let uu____4824 = (FStar_Options.print_universes ())
in (match (uu____4824) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____4844 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____4865 = (resugar_term c1.FStar_Syntax_Syntax.result_typ)
in ((uu____4865), (FStar_Parser_AST.Nothing)))
in (

let uu____4866 = (FStar_Options.print_effect_args ())
in (match (uu____4866) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (match ((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(

let rec aux = (fun l uu___194_4923 -> (match (uu___194_4923) with
| [] -> begin
l
end
| ((t, aq))::tl1 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(aux l tl1)
end
| FStar_Syntax_Syntax.Tm_meta (uu____4984) -> begin
(aux l tl1)
end
| uu____4991 -> begin
(aux ((((t), (aq)))::l) tl1)
end)
end))
in (aux [] c1.FStar_Syntax_Syntax.effect_args))
end
| uu____5006 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
in (

let args1 = (FStar_List.map (fun uu____5026 -> (match (uu____5026) with
| (e, uu____5036) -> begin
(

let uu____5037 = (resugar_term e)
in ((uu____5037), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___195_5058 -> (match (uu___195_5058) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____5091 = (resugar_term e)
in ((uu____5091), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____5096 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____5122 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____5141 = b
in (match (uu____5141) with
| (x, aq) -> begin
(

let uu____5146 = (resugar_arg_qual aq)
in (FStar_Util.map_opt uu____5146 (fun imp -> (

let e = (resugar_term x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____5160 = (

let uu____5161 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____5161))
in (FStar_Parser_AST.mk_binder uu____5160 r FStar_Parser_AST.Type_level imp))
end
| uu____5162 -> begin
(

let uu____5163 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5163) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____5164 -> begin
(

let uu____5165 = (

let uu____5166 = (

let uu____5171 = (bv_as_unique_ident x)
in ((uu____5171), (e)))
in FStar_Parser_AST.Annotated (uu____5166))
in (FStar_Parser_AST.mk_binder uu____5165 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun x qual -> (

let mk1 = (fun a -> (

let uu____5180 = (FStar_Syntax_Syntax.range_of_bv x)
in (FStar_Parser_AST.mk_pattern a uu____5180)))
in (

let uu____5181 = (

let uu____5182 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in uu____5182.FStar_Syntax_Syntax.n)
in (match (uu____5181) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let i = (FStar_String.compare x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix)
in (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5190 = (mk1 FStar_Parser_AST.PatWild)
in FStar_Pervasives_Native.Some (uu____5190))
end
| uu____5191 -> begin
(

let uu____5192 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____5192 (fun aq -> (

let uu____5204 = (

let uu____5205 = (

let uu____5206 = (

let uu____5213 = (bv_as_unique_ident x)
in ((uu____5213), (aq)))
in FStar_Parser_AST.PatVar (uu____5206))
in (mk1 uu____5205))
in FStar_Pervasives_Native.Some (uu____5204)))))
end))
end
| uu____5216 -> begin
(

let uu____5217 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____5217 (fun aq -> (

let pat = (

let uu____5232 = (

let uu____5233 = (

let uu____5240 = (bv_as_unique_ident x)
in ((uu____5240), (aq)))
in FStar_Parser_AST.PatVar (uu____5233))
in (mk1 uu____5232))
in (

let uu____5243 = (FStar_Options.print_bound_var_types ())
in (match (uu____5243) with
| true -> begin
(

let uu____5246 = (

let uu____5247 = (

let uu____5248 = (

let uu____5253 = (resugar_term x.FStar_Syntax_Syntax.sort)
in ((pat), (uu____5253)))
in FStar_Parser_AST.PatAscribed (uu____5248))
in (mk1 uu____5247))
in FStar_Pervasives_Native.Some (uu____5246))
end
| uu____5254 -> begin
FStar_Pervasives_Native.Some (pat)
end))))))
end))))
and resugar_pat : FStar_Syntax_Syntax.pat  ->  FStar_Parser_AST.pattern = (fun p -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p))
in (

let to_arg_qual = (fun bopt -> (FStar_Util.bind_opt bopt (fun b -> (match (true) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)
end
| uu____5274 -> begin
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

let args1 = (FStar_List.map (fun uu____5330 -> (match (uu____5330) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatList (args1))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Parser_Const.is_tuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) || (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) -> begin
(

let args1 = (FStar_List.map (fun uu____5365 -> (match (uu____5365) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (

let uu____5372 = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____5372) with
| true -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (true)))))
end
| uu____5375 -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (false)))))
end)))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____5378; FStar_Syntax_Syntax.fv_delta = uu____5379; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____5406 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____5406 FStar_List.rev))
in (

let args1 = (

let uu____5422 = (FStar_All.pipe_right args (FStar_List.map (fun uu____5442 -> (match (uu____5442) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____5422 FStar_List.rev))
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

let uu____5512 = (map21 tl1 [])
in (((hd1), ((mk1 FStar_Parser_AST.PatWild))))::uu____5512)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____5535 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____5535)
end))
in (

let args2 = (

let uu____5553 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____5553 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(

let args1 = (FStar_List.map (fun uu____5604 -> (match (uu____5604) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args1))))))
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____5614 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____5614) with
| FStar_Pervasives_Native.Some (op, uu____5622) -> begin
(mk1 (FStar_Parser_AST.PatOp ((FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5631 = (

let uu____5632 = (

let uu____5639 = (bv_as_unique_ident v1)
in (

let uu____5640 = (to_arg_qual imp_opt)
in ((uu____5639), (uu____5640))))
in FStar_Parser_AST.PatVar (uu____5632))
in (mk1 uu____5631))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____5645) -> begin
(mk1 FStar_Parser_AST.PatWild)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, term) -> begin
(

let pat = (

let uu____5653 = (

let uu____5654 = (

let uu____5661 = (bv_as_unique_ident bv)
in ((uu____5661), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))
in FStar_Parser_AST.PatVar (uu____5654))
in (mk1 uu____5653))
in (

let uu____5664 = (FStar_Options.print_bound_var_types ())
in (match (uu____5664) with
| true -> begin
(

let uu____5665 = (

let uu____5666 = (

let uu____5671 = (resugar_term term)
in ((pat), (uu____5671)))
in FStar_Parser_AST.PatAscribed (uu____5666))
in (mk1 uu____5665))
end
| uu____5672 -> begin
pat
end)))
end))
in (aux p FStar_Pervasives_Native.None)))))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___196_5678 -> (match (uu___196_5678) with
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
| uu____5683 -> begin
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
| uu____5686 -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Logic)
end)
end
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reifiable)
end
| FStar_Syntax_Syntax.Reflectable (uu____5687) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____5688) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____5689) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____5694) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____5703) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____5712) -> begin
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


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___197_5716 -> (match (uu___197_5716) with
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
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____5745, datacons) -> begin
(

let uu____5755 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5782, uu____5783, uu____5784, inductive_lid, uu____5786, uu____5787) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____5792 -> begin
(failwith "unexpected")
end))))
in (match (uu____5755) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____5811 = (FStar_Options.print_implicits ())
in (match (uu____5811) with
| true -> begin
bs
end
| uu____5812 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____5821 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___198_5826 -> (match (uu___198_5826) with
| FStar_Syntax_Syntax.RecordType (uu____5827) -> begin
true
end
| uu____5836 -> begin
false
end))))
in (match (uu____5821) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____5884, univs1, term, uu____5887, num, uu____5889) -> begin
(

let uu____5894 = (

let uu____5895 = (FStar_Syntax_Subst.compress term)
in uu____5895.FStar_Syntax_Syntax.n)
in (match (uu____5894) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____5909) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____5970 -> (match (uu____5970) with
| (b, qual) -> begin
(

let uu____5985 = (

let uu____5986 = (bv_as_unique_ident b)
in (FStar_Syntax_Util.unmangle_field_name uu____5986))
in (

let uu____5987 = (resugar_term b.FStar_Syntax_Syntax.sort)
in ((uu____5985), (uu____5987), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____5998 -> begin
(failwith "unexpected")
end))
end
| uu____6009 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____6063 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____6130, num, uu____6132) -> begin
(

let c = (

let uu____6150 = (

let uu____6153 = (resugar_term term)
in FStar_Pervasives_Native.Some (uu____6153))
in ((l.FStar_Ident.ident), (uu____6150), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____6170 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____6246 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____6267 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____6267; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme' : Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun name ts -> (

let uu____6284 = ts
in (match (uu____6284) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____6292 = (

let uu____6293 = (

let uu____6306 = (

let uu____6315 = (

let uu____6322 = (

let uu____6323 = (

let uu____6336 = (resugar_term typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____6336)))
in FStar_Parser_AST.TyconAbbrev (uu____6323))
in ((uu____6322), (FStar_Pervasives_Native.None)))
in (uu____6315)::[])
in ((false), (uu____6306)))
in FStar_Parser_AST.Tycon (uu____6293))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____6292)))
end)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (resugar_tscheme' "tsheme" ts))


let resugar_eff_decl : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun for_free r q ed -> (

let resugar_action = (fun d for_free1 -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____6395 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____6395) with
| (bs, action_defn) -> begin
(

let uu____6402 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____6402) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____6410 = (FStar_Options.print_implicits ())
in (match (uu____6410) with
| true -> begin
action_params
end
| uu____6411 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____6415 = (FStar_All.pipe_right action_params1 (map_opt (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____6415 FStar_List.rev))
in (

let action_defn1 = (resugar_term action_defn)
in (

let action_typ1 = (resugar_term action_typ)
in (match (for_free1) with
| true -> begin
(

let a = (

let uu____6429 = (

let uu____6440 = (FStar_Ident.lid_of_str "construct")
in ((uu____6440), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____6429))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____6486 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____6514 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____6514) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____6522 = (FStar_Options.print_implicits ())
in (match (uu____6522) with
| true -> begin
eff_binders
end
| uu____6523 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____6527 = (FStar_All.pipe_right eff_binders1 (map_opt (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____6527 FStar_List.rev))
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
| uu____6559 -> begin
(repr)::(return_repr)::(bind_repr)::(ret_wp)::(bind_wp)::(if_then_else1)::(ite_wp)::(stronger)::(close_wp)::(assert_p)::(assume_p)::(null_wp)::(trivial)::[]
end)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls)))))))))))))))))))))))))
end)))))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____6585) -> begin
(

let uu____6594 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____6616) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____6633) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____6640) -> begin
false
end
| uu____6655 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____6594) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____6687 se1 -> (match (uu____6687) with
| (datacon_ses1, tycons) -> begin
(

let uu____6713 = (resugar_typ datacon_ses1 se1)
in (match (uu____6713) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____6728 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____6728) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____6763 = (

let uu____6764 = (

let uu____6765 = (

let uu____6778 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (uu____6778)))
in FStar_Parser_AST.Tycon (uu____6765))
in (decl'_to_decl se uu____6764))
in FStar_Pervasives_Native.Some (uu____6763))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____6809, uu____6810, uu____6811, uu____6812, uu____6813) -> begin
(

let uu____6818 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____6818))
end
| uu____6821 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____6824 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____6830) -> begin
(

let uu____6835 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___199_6841 -> (match (uu___199_6841) with
| FStar_Syntax_Syntax.Projector (uu____6842, uu____6843) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____6844) -> begin
true
end
| uu____6845 -> begin
false
end))))
in (match (uu____6835) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6848 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____6868) -> begin
(

let uu____6881 = (decl'_to_decl se (FStar_Parser_AST.TopLevelLet (((isrec), (lets)))))
in FStar_Pervasives_Native.Some (uu____6881))
end
| uu____6888 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____6892, fml) -> begin
(

let uu____6894 = (

let uu____6895 = (

let uu____6896 = (

let uu____6901 = (resugar_term fml)
in ((lid.FStar_Ident.ident), (uu____6901)))
in FStar_Parser_AST.Assume (uu____6896))
in (decl'_to_decl se uu____6895))
in FStar_Pervasives_Native.Some (uu____6894))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____6903 = (resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____6903))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let uu____6905 = (resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____6905))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____6914, t) -> begin
(

let uu____6926 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____6926))
end
| uu____6927 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____6935, t) -> begin
(

let uu____6947 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____6947))
end
| uu____6948 -> begin
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
| uu____6972 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____6981 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____6981)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) -> begin
(

let uu____6991 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____6991) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____7001 = (FStar_Options.print_implicits ())
in (match (uu____7001) with
| true -> begin
bs1
end
| uu____7002 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 (map_opt (fun b -> (resugar_binder b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____7010 = (

let uu____7011 = (

let uu____7012 = (

let uu____7025 = (

let uu____7034 = (

let uu____7041 = (

let uu____7042 = (

let uu____7055 = (resugar_comp c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____7055)))
in FStar_Parser_AST.TyconAbbrev (uu____7042))
in ((uu____7041), (FStar_Pervasives_Native.None)))
in (uu____7034)::[])
in ((false), (uu____7025)))
in FStar_Parser_AST.Tycon (uu____7012))
in (decl'_to_decl se uu____7011))
in FStar_Pervasives_Native.Some (uu____7010))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____7083 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____7083))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____7087 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___200_7093 -> (match (uu___200_7093) with
| FStar_Syntax_Syntax.Projector (uu____7094, uu____7095) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____7096) -> begin
true
end
| uu____7097 -> begin
false
end))))
in (match (uu____7087) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7100 -> begin
(

let t' = (

let uu____7102 = ((

let uu____7105 = (FStar_Options.print_universes ())
in (not (uu____7105))) || (FStar_List.isEmpty uvs))
in (match (uu____7102) with
| true -> begin
(resugar_term t)
end
| uu____7106 -> begin
(

let uu____7107 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____7107) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____7115 = (resugar_term t1)
in (label universes uu____7115)))
end))
end))
in (

let uu____7116 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____7116)))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7117) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7134) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____7149) -> begin
FStar_Pervasives_Native.None
end))





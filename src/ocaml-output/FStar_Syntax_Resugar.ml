
open Prims
open FStar_Pervasives

let doc_to_string : FStar_Pprint.document  ->  Prims.string = (fun doc1 -> (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1))


let parser_term_to_string : FStar_Parser_AST.term  ->  Prims.string = (fun t -> (

let uu____11 = (FStar_Parser_ToDocument.term_to_document t)
in (doc_to_string uu____11)))


let parser_pat_to_string : FStar_Parser_AST.pattern  ->  Prims.string = (fun t -> (

let uu____17 = (FStar_Parser_ToDocument.pat_to_document t)
in (doc_to_string uu____17)))


let map_opt : 'Auu____26 'Auu____27 . unit  ->  ('Auu____26  ->  'Auu____27 FStar_Pervasives_Native.option)  ->  'Auu____26 Prims.list  ->  'Auu____27 Prims.list = (fun uu____43 -> FStar_List.filter_map)


let bv_as_unique_ident : FStar_Syntax_Syntax.bv  ->  FStar_Ident.ident = (fun x -> (

let unique_name = (

let uu____50 = ((FStar_Util.starts_with FStar_Ident.reserved_prefix x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) || (FStar_Options.print_real_names ()))
in (match (uu____50) with
| true -> begin
(

let uu____51 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____51))
end
| uu____52 -> begin
x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end))
in (FStar_Ident.mk_ident ((unique_name), (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))))


let filter_imp : 'Auu____57 . ('Auu____57 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  ('Auu____57 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___70_112 -> (match (uu___70_112) with
| (uu____119, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____120))) -> begin
false
end
| uu____123 -> begin
true
end)))))


let filter_pattern_imp : 'Auu____134 . ('Auu____134 * Prims.bool) Prims.list  ->  ('Auu____134 * Prims.bool) Prims.list = (fun xs -> (FStar_List.filter (fun uu____165 -> (match (uu____165) with
| (uu____170, is_implicit1) -> begin
(not (is_implicit1))
end)) xs))


let label : Prims.string  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun s t -> (match ((Prims.op_Equality s "")) with
| true -> begin
t
end
| uu____182 -> begin
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
| uu____213 -> begin
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
FStar_Parser_AST.Nothing
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) -> begin
FStar_Parser_AST.Nothing
end))


let rec universe_to_int : Prims.int  ->  FStar_Syntax_Syntax.universe  ->  (Prims.int * FStar_Syntax_Syntax.universe) = (fun n1 u -> (match (u) with
| FStar_Syntax_Syntax.U_succ (u1) -> begin
(universe_to_int (n1 + (Prims.parse_int "1")) u1)
end
| uu____246 -> begin
((n1), (u))
end))


let universe_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun univs1 -> (

let uu____256 = (FStar_Options.print_universes ())
in (match (uu____256) with
| true -> begin
(

let uu____257 = (FStar_List.map (fun x -> x.FStar_Ident.idText) univs1)
in (FStar_All.pipe_right uu____257 (FStar_String.concat ", ")))
end
| uu____264 -> begin
""
end)))


let rec resugar_universe' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun env u r -> (resugar_universe u r))
and resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____311) -> begin
(

let uu____312 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____312) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____319 = (

let uu____320 = (

let uu____321 = (

let uu____332 = (FStar_Util.string_of_int n1)
in ((uu____332), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____321))
in FStar_Parser_AST.Const (uu____320))
in (mk1 uu____319 r))
end
| uu____343 -> begin
(

let e1 = (

let uu____345 = (

let uu____346 = (

let uu____347 = (

let uu____358 = (FStar_Util.string_of_int n1)
in ((uu____358), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____347))
in FStar_Parser_AST.Const (uu____346))
in (mk1 uu____345 r))
in (

let e2 = (resugar_universe u1 r)
in (

let uu____370 = (

let uu____371 = (

let uu____378 = (FStar_Ident.id_of_text "+")
in ((uu____378), ((e1)::(e2)::[])))
in FStar_Parser_AST.Op (uu____371))
in (mk1 uu____370 r))))
end)
end))
end
| FStar_Syntax_Syntax.U_max (l) -> begin
(match (l) with
| [] -> begin
(failwith "Impossible: U_max without arguments")
end
| uu____384 -> begin
(

let t = (

let uu____388 = (

let uu____389 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____389))
in (mk1 uu____388 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____395 = (

let uu____396 = (

let uu____403 = (resugar_universe x r)
in ((acc), (uu____403), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____396))
in (mk1 uu____395 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____405) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id1 = (

let uu____416 = (

let uu____421 = (

let uu____422 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____422))
in ((uu____421), (r)))
in (FStar_Ident.mk_ident uu____416))
in (mk1 (FStar_Parser_AST.Uvar (id1)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___71_449 -> (match (uu___71_449) with
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
| uu____626 -> begin
FStar_Pervasives_Native.None
end))
in (match (s) with
| "op_String_Assignment" -> begin
FStar_Pervasives_Native.Some (((".[]<-"), (FStar_Pervasives_Native.None)))
end
| "op_Array_Assignment" -> begin
FStar_Pervasives_Native.Some (((".()<-"), (FStar_Pervasives_Native.None)))
end
| "op_String_Access" -> begin
FStar_Pervasives_Native.Some (((".[]"), (FStar_Pervasives_Native.None)))
end
| "op_Array_Access" -> begin
FStar_Pervasives_Native.Some (((".()"), (FStar_Pervasives_Native.None)))
end
| uu____673 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____685 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____685 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____695 -> begin
(

let op = (

let uu____699 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (x) with
| FStar_Pervasives_Native.Some (op, uu____741) -> begin
(Prims.strcat acc op)
end
| FStar_Pervasives_Native.None -> begin
(failwith "wrong composed operator format")
end)) "" uu____699))
in FStar_Pervasives_Native.Some (((op), (FStar_Pervasives_Native.None))))
end))
end
| uu____766 -> begin
FStar_Pervasives_Native.None
end)
end)))


type expected_arity =
Prims.int FStar_Pervasives_Native.option


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * expected_arity) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.strcat_lid), ("^")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____949 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____949) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), (FStar_Pervasives_Native.None)))
end
| uu____1003 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1016 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), (FStar_Pervasives_Native.None)))
end
| uu____1039 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), (FStar_Pervasives_Native.None)))
end
| uu____1056 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), (FStar_Pervasives_Native.None)))
end
| uu____1073 -> begin
(

let uu____1074 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____1074) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), (FStar_Pervasives_Native.None)))
end
| uu____1091 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____1098 = (

let uu____1099 = (FStar_Syntax_Subst.compress t)
in uu____1099.FStar_Syntax_Syntax.n)
in (match (uu____1098) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((Prims.op_Equality length1 (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____1115 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____1122 = (string_to_op s)
in (match (uu____1122) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____1156 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____1171 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____1181 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____1187) -> begin
true
end
| uu____1188 -> begin
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
| uu____1199 -> begin
(

let uu____1200 = (is_tuple_constructor_lid lid)
in (not (uu____1200)))
end))


let maybe_shorten_fv : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Ident.lid = (fun env fv -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____1212 = (may_shorten lid)
in (match (uu____1212) with
| true -> begin
(FStar_Syntax_DsEnv.shorten_lid env lid)
end
| uu____1213 -> begin
lid
end))))


let rec resugar_term' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun env t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____1325 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____1325)))
in (

let uu____1326 = (

let uu____1327 = (FStar_Syntax_Subst.compress t)
in uu____1327.FStar_Syntax_Syntax.n)
in (match (uu____1326) with
| FStar_Syntax_Syntax.Tm_delayed (uu____1330) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____1356 = (FStar_Syntax_Util.unfold_lazy i)
in (resugar_term' env uu____1356))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____1359 = (

let uu____1362 = (bv_as_unique_ident x)
in (uu____1362)::[])
in (FStar_Ident.lid_of_ids uu____1359))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____1365 = (

let uu____1368 = (bv_as_unique_ident x)
in (uu____1368)::[])
in (FStar_Ident.lid_of_ids uu____1365))
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
| uu____1377 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.strcat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____1386 = (

let uu____1387 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____1387))
in (mk1 uu____1386)))
end
| uu____1388 -> begin
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
| uu____1397 -> begin
(failwith "wrong projector format")
end)))
end
| uu____1400 -> begin
(

let uu____1401 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____1404 = (

let uu____1406 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____1406))
in (

let uu____1408 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____1404 uu____1408))))
in (match (uu____1401) with
| true -> begin
(

let uu____1411 = (

let uu____1412 = (maybe_shorten_fv env fv)
in FStar_Parser_AST.Var (uu____1412))
in (mk1 uu____1411))
end
| uu____1413 -> begin
(

let uu____1414 = (

let uu____1415 = (

let uu____1426 = (maybe_shorten_fv env fv)
in ((uu____1426), ([])))
in FStar_Parser_AST.Construct (uu____1415))
in (mk1 uu____1414))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let e1 = (resugar_term' env e)
in (

let uu____1444 = (FStar_Options.print_universes ())
in (match (uu____1444) with
| true -> begin
(

let univs1 = (FStar_List.map (fun x -> (resugar_universe x t.FStar_Syntax_Syntax.pos)) universes)
in (match (e1) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(

let args1 = (

let uu____1473 = (FStar_List.map (fun u -> ((u), (FStar_Parser_AST.UnivApp))) univs1)
in (FStar_List.append args uu____1473))
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), (args1)))) r l))
end
| uu____1496 -> begin
(FStar_List.fold_left (fun acc u -> (mk1 (FStar_Parser_AST.App (((acc), (u), (FStar_Parser_AST.UnivApp)))))) e1 univs1)
end))
end
| uu____1501 -> begin
e1
end)))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____1503 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____1503) with
| true -> begin
(

let uu____1504 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1504))
end
| uu____1505 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(

let uu____1507 = (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(("Type0"), (false))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(("Type"), (false))
end
| uu____1516 -> begin
(("Type"), (true))
end)
in (match (uu____1507) with
| (nm, needs_app) -> begin
(

let typ = (

let uu____1520 = (name nm t.FStar_Syntax_Syntax.pos)
in (mk1 uu____1520))
in (

let uu____1521 = (needs_app && (FStar_Options.print_universes ()))
in (match (uu____1521) with
| true -> begin
(

let uu____1522 = (

let uu____1523 = (

let uu____1530 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((typ), (uu____1530), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____1523))
in (mk1 uu____1522))
end
| uu____1531 -> begin
typ
end)))
end))
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____1534) -> begin
(

let uu____1555 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____1555) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1563 = (FStar_Options.print_implicits ())
in (match (uu____1563) with
| true -> begin
xs1
end
| uu____1564 -> begin
(filter_imp xs1)
end))
in (

let body_bv = (FStar_Syntax_Free.names body1)
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____1580 -> (match (uu____1580) with
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

let uu____1610 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____1610) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____1618 = (FStar_Options.print_implicits ())
in (match (uu____1618) with
| true -> begin
xs1
end
| uu____1619 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp' env body1)
in (

let xs3 = (

let uu____1624 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____1624 FStar_List.rev))
in (

let rec aux = (fun body3 uu___72_1647 -> (match (uu___72_1647) with
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

let uu____1663 = (

let uu____1668 = (

let uu____1669 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____1669)::[])
in (FStar_Syntax_Subst.open_term uu____1668 phi))
in (match (uu____1663) with
| (x1, phi1) -> begin
(

let b = (

let uu____1673 = (

let uu____1676 = (FStar_List.hd x1)
in (resugar_binder' env uu____1676 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____1673))
in (

let uu____1681 = (

let uu____1682 = (

let uu____1687 = (resugar_term' env phi1)
in ((b), (uu____1687)))
in FStar_Parser_AST.Refine (uu____1682))
in (mk1 uu____1681)))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1689; FStar_Syntax_Syntax.vars = uu____1690}, ((e, uu____1692))::[]) when ((

let uu____1723 = (FStar_Options.print_implicits ())
in (not (uu____1723))) && (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2p_lid)) -> begin
(resugar_term' env e)
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1725; FStar_Syntax_Syntax.vars = uu____1726}, ((t_base, uu____1728))::((f, uu____1730))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) -> begin
(

let uu____1769 = (

let uu____1770 = (FStar_Syntax_Subst.compress f)
in uu____1770.FStar_Syntax_Syntax.n)
in (match (uu____1769) with
| FStar_Syntax_Syntax.Tm_abs ((x)::[], f1, uu____1775) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((((FStar_Pervasives_Native.fst x)), (f1)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (resugar_term' env t1))
end
| uu____1807 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t_base)
in (

let phi = (

let uu____1812 = (

let uu____1817 = (

let uu____1818 = (

let uu____1819 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____1819))
in (uu____1818)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____1817))
in (uu____1812 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____1822 = (FStar_Syntax_Util.refine x phi)
in (resugar_term' env uu____1822))))
end))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____1824; FStar_Syntax_Syntax.vars = uu____1825}, uu____1826); FStar_Syntax_Syntax.pos = uu____1827; FStar_Syntax_Syntax.vars = uu____1828}, ((t_base, uu____1830))::((f, uu____1832))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.t_refine_lid) -> begin
(

let uu____1875 = (

let uu____1876 = (FStar_Syntax_Subst.compress f)
in uu____1876.FStar_Syntax_Syntax.n)
in (match (uu____1875) with
| FStar_Syntax_Syntax.Tm_abs ((x)::[], f1, uu____1881) -> begin
(

let t1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((((FStar_Pervasives_Native.fst x)), (f1)))) FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos)
in (resugar_term' env t1))
end
| uu____1913 -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t_base)
in (

let phi = (

let uu____1918 = (

let uu____1923 = (

let uu____1924 = (

let uu____1925 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_Syntax_Syntax.as_arg uu____1925))
in (uu____1924)::[])
in (FStar_Syntax_Syntax.mk_Tm_app f uu____1923))
in (uu____1918 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos))
in (

let uu____1928 = (FStar_Syntax_Util.refine x phi)
in (resugar_term' env uu____1928))))
end))
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___73_1972 -> (match (uu___73_1972) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____2042 -> begin
(failwith "last of an empty list")
end))
in (

let rec last_two = (fun uu___74_2080 -> (match (uu___74_2080) with
| [] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (uu____2111)::[] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (a1)::(a2)::[] -> begin
(a1)::(a2)::[]
end
| (uu____2188)::t1 -> begin
(last_two t1)
end))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_List.map (fun uu____2259 -> (match (uu____2259) with
| (e2, qual) -> begin
(

let uu____2276 = (resugar_term' env e2)
in (

let uu____2277 = (resugar_imp qual)
in ((uu____2276), (uu____2277))))
end)) args1)
in (

let uu____2278 = (resugar_term' env e1)
in (match (uu____2278) with
| {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (hd1, previous_args); FStar_Parser_AST.range = r; FStar_Parser_AST.level = l} -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((hd1), ((FStar_List.append previous_args args2))))) r l)
end
| e2 -> begin
(FStar_List.fold_left (fun acc uu____2315 -> (match (uu____2315) with
| (x, qual) -> begin
(mk1 (FStar_Parser_AST.App (((acc), (x), (qual)))))
end)) e2 args2)
end))))
in (

let args1 = (

let uu____2331 = (FStar_Options.print_implicits ())
in (match (uu____2331) with
| true -> begin
args
end
| uu____2340 -> begin
(filter_imp args)
end))
in (

let uu____2343 = (resugar_term_as_op e)
in (match (uu____2343) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____2354) -> begin
(match (args1) with
| ((fst1, uu____2360))::((snd1, uu____2362))::rest -> begin
(

let e1 = (

let uu____2393 = (

let uu____2394 = (

let uu____2401 = (FStar_Ident.id_of_text "*")
in (

let uu____2402 = (

let uu____2405 = (resugar_term' env fst1)
in (

let uu____2406 = (

let uu____2409 = (resugar_term' env snd1)
in (uu____2409)::[])
in (uu____2405)::uu____2406))
in ((uu____2401), (uu____2402))))
in FStar_Parser_AST.Op (uu____2394))
in (mk1 uu____2393))
in (FStar_List.fold_left (fun acc uu____2422 -> (match (uu____2422) with
| (x, uu____2428) -> begin
(

let uu____2429 = (

let uu____2430 = (

let uu____2437 = (FStar_Ident.id_of_text "*")
in (

let uu____2438 = (

let uu____2441 = (

let uu____2444 = (resugar_term' env x)
in (uu____2444)::[])
in (e1)::uu____2441)
in ((uu____2437), (uu____2438))))
in FStar_Parser_AST.Op (uu____2430))
in (mk1 uu____2429))
end)) e1 rest))
end
| uu____2447 -> begin
(resugar_as_app e args1)
end)
end
| FStar_Pervasives_Native.Some ("dtuple", uu____2456) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____2482))::[] -> begin
b
end
| uu____2499 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____2510 = (

let uu____2511 = (FStar_Syntax_Subst.compress body)
in uu____2511.FStar_Syntax_Syntax.n)
in (match (uu____2510) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____2516) -> begin
(

let uu____2537 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____2537) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____2545 = (FStar_Options.print_implicits ())
in (match (uu____2545) with
| true -> begin
xs1
end
| uu____2546 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term' env body2)
in (mk1 (FStar_Parser_AST.Sum (((xs3), (body3))))))))
end))
end
| uu____2557 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____2578 -> (match (uu____2578) with
| (e1, qual) -> begin
(resugar_term' env e1)
end))))
in (

let e1 = (resugar_term' env e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____2590) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____2596) when (Prims.op_Equality ref_read FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____2601 = (FStar_List.hd args1)
in (match (uu____2601) with
| (t1, uu____2615) -> begin
(

let uu____2620 = (

let uu____2621 = (FStar_Syntax_Subst.compress t1)
in uu____2621.FStar_Syntax_Syntax.n)
in (match (uu____2620) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____2626 = (

let uu____2627 = (

let uu____2632 = (resugar_term' env t1)
in ((uu____2632), (f)))
in FStar_Parser_AST.Project (uu____2627))
in (mk1 uu____2626)))
end
| uu____2633 -> begin
(resugar_term' env t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2634) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(

let new_args = (last_two args1)
in (

let uu____2654 = (match (new_args) with
| ((a1, uu____2672))::((a2, uu____2674))::[] -> begin
((a1), (a2))
end
| uu____2705 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____2654) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____2738 = (

let uu____2739 = (FStar_Syntax_Subst.compress term)
in uu____2739.FStar_Syntax_Syntax.n)
in (match (uu____2738) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____2744) -> begin
(

let uu____2765 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____2765) with
| (x1, e2) -> begin
e2
end))
end
| uu____2772 -> begin
(failwith "wrong argument format to try_with")
end)))
in (

let body1 = (

let uu____2774 = (decomp body)
in (resugar_term' env uu____2774))
in (

let handler1 = (

let uu____2776 = (decomp handler)
in (resugar_term' env uu____2776))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____2784, uu____2785, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____2817, uu____2818, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____2855 = (

let uu____2856 = (

let uu____2865 = (resugar_body t11)
in ((uu____2865), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____2856))
in (mk1 uu____2855))
end
| uu____2868 -> begin
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
| uu____2925 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____2955) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____2961) when ((Prims.op_Equality op "forall") || (Prims.op_Equality op "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____3052 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____3065 = (

let uu____3066 = (FStar_Syntax_Subst.compress body)
in uu____3066.FStar_Syntax_Syntax.n)
in (match (uu____3065) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____3071) -> begin
(

let uu____3092 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____3092) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____3100 = (FStar_Options.print_implicits ())
in (match (uu____3100) with
| true -> begin
xs1
end
| uu____3101 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let uu____3109 = (

let uu____3118 = (

let uu____3119 = (FStar_Syntax_Subst.compress body2)
in uu____3119.FStar_Syntax_Syntax.n)
in (match (uu____3118) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term' env e1)
in (

let uu____3137 = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(

let uu____3165 = (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____3201 -> (match (uu____3201) with
| (e2, uu____3207) -> begin
(resugar_term' env e2)
end))))) pats)
in ((uu____3165), (body3)))
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, p) -> begin
(

let uu____3215 = (mk1 (FStar_Parser_AST.Labeled (((body3), (s), (p)))))
in (([]), (uu____3215)))
end
| uu____3222 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in (match (uu____3137) with
| (pats, body4) -> begin
((pats), (body4))
end)))
end
| uu____3253 -> begin
(

let uu____3254 = (resugar_term' env body2)
in (([]), (uu____3254)))
end))
in (match (uu____3109) with
| (pats, body3) -> begin
(

let uu____3271 = (uncurry xs3 pats body3)
in (match (uu____3271) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((Prims.op_Equality op "forall")) with
| true -> begin
(mk1 (FStar_Parser_AST.QForall (((xs5), (pats1), (body4)))))
end
| uu____3312 -> begin
(mk1 (FStar_Parser_AST.QExists (((xs5), (pats1), (body4)))))
end))
end))
end))))
end))
end
| uu____3319 -> begin
(match ((Prims.op_Equality op "forall")) with
| true -> begin
(

let uu____3320 = (

let uu____3321 = (

let uu____3334 = (resugar_term' env body)
in (([]), (([])::[]), (uu____3334)))
in FStar_Parser_AST.QForall (uu____3321))
in (mk1 uu____3320))
end
| uu____3345 -> begin
(

let uu____3346 = (

let uu____3347 = (

let uu____3360 = (resugar_term' env body)
in (([]), (([])::[]), (uu____3360)))
in FStar_Parser_AST.QExists (uu____3347))
in (mk1 uu____3346))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____3387))::[] -> begin
(resugar b)
end
| uu____3404 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____3413 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____3414) -> begin
(

let uu____3419 = (FStar_List.hd args1)
in (match (uu____3419) with
| (e1, uu____3433) -> begin
(resugar_term' env e1)
end))
end
| FStar_Pervasives_Native.Some (op, expected_arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____3502 -> (match (uu____3502) with
| (e1, qual) -> begin
(

let uu____3519 = (resugar_term' env e1)
in (

let uu____3520 = (resugar_imp qual)
in ((uu____3519), (uu____3520))))
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

let uu____3533 = (FStar_Util.first_N expect_n resugared_args)
in (match (uu____3533) with
| (op_args, rest) -> begin
(

let head1 = (

let uu____3581 = (

let uu____3582 = (

let uu____3589 = (FStar_List.map FStar_Pervasives_Native.fst op_args)
in ((op1), (uu____3589)))
in FStar_Parser_AST.Op (uu____3582))
in (mk1 uu____3581))
in (FStar_List.fold_left (fun head2 uu____3607 -> (match (uu____3607) with
| (arg, qual) -> begin
(mk1 (FStar_Parser_AST.App (((head2), (arg), (qual)))))
end)) head1 rest))
end))
end
| uu____3614 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some (n1) when (Prims.op_Equality (FStar_List.length args1) n1) -> begin
(

let uu____3622 = (

let uu____3623 = (

let uu____3630 = (

let uu____3633 = (resugar args1)
in (FStar_List.map FStar_Pervasives_Native.fst uu____3633))
in ((op1), (uu____3630)))
in FStar_Parser_AST.Op (uu____3623))
in (mk1 uu____3622))
end
| uu____3646 -> begin
(resugar_as_app e args1)
end)))
end))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, wopt, t1))::[]) -> begin
(

let uu____3715 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (t1)))
in (match (uu____3715) with
| (pat1, wopt1, t2) -> begin
(

let branch_bv = (FStar_Syntax_Free.names t2)
in (

let bnds = (

let uu____3761 = (

let uu____3774 = (

let uu____3779 = (resugar_pat' env pat1 branch_bv)
in (

let uu____3780 = (resugar_term' env e)
in ((uu____3779), (uu____3780))))
in ((FStar_Pervasives_Native.None), (uu____3774)))
in (uu____3761)::[])
in (

let body = (resugar_term' env t2)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body))))))))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____3832, t1))::((pat2, uu____3835, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____3931 = (

let uu____3932 = (

let uu____3939 = (resugar_term' env e)
in (

let uu____3940 = (resugar_term' env t1)
in (

let uu____3941 = (resugar_term' env t2)
in ((uu____3939), (uu____3940), (uu____3941)))))
in FStar_Parser_AST.If (uu____3932))
in (mk1 uu____3931))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____4007 -> (match (uu____4007) with
| (pat, wopt, b) -> begin
(

let uu____4049 = (FStar_Syntax_Subst.open_branch ((pat), (wopt), (b)))
in (match (uu____4049) with
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

let uu____4101 = (resugar_term' env e1)
in FStar_Pervasives_Native.Some (uu____4101))
end)
in (

let b2 = (resugar_term' env b1)
in ((pat2), (wopt2), (b2))))))
end))
end))
in (

let uu____4105 = (

let uu____4106 = (

let uu____4121 = (resugar_term' env e)
in (

let uu____4122 = (FStar_List.map resugar_branch branches)
in ((uu____4121), (uu____4122))))
in FStar_Parser_AST.Match (uu____4106))
in (mk1 uu____4105)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____4168) -> begin
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

let uu____4235 = (

let uu____4236 = (

let uu____4245 = (resugar_term' env e)
in ((uu____4245), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____4236))
in (mk1 uu____4235))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, source_lbs), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____4271 = (FStar_Syntax_Subst.open_let_rec source_lbs body)
in (match (uu____4271) with
| (source_lbs1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let attrs_opt = (match (bnd.FStar_Syntax_Syntax.lbattrs) with
| [] -> begin
FStar_Pervasives_Native.None
end
| tms -> begin
(

let uu____4324 = (FStar_List.map (resugar_term' env) tms)
in FStar_Pervasives_Native.Some (uu____4324))
end)
in (

let uu____4329 = (

let uu____4334 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____4334))
in (match (uu____4329) with
| (univs1, td) -> begin
(

let uu____4353 = (

let uu____4362 = (

let uu____4363 = (FStar_Syntax_Subst.compress td)
in uu____4363.FStar_Syntax_Syntax.n)
in (match (uu____4362) with
| FStar_Syntax_Syntax.Tm_app (uu____4374, ((t1, uu____4376))::((d, uu____4378))::[]) -> begin
((t1), (d))
end
| uu____4421 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____4353) with
| (typ, def) -> begin
(

let uu____4456 = (

let uu____4463 = (

let uu____4464 = (FStar_Syntax_Subst.compress def)
in uu____4464.FStar_Syntax_Syntax.n)
in (match (uu____4463) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____4475) -> begin
(

let uu____4496 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____4496) with
| (b1, t2) -> begin
(

let b2 = (

let uu____4510 = (FStar_Options.print_implicits ())
in (match (uu____4510) with
| true -> begin
b1
end
| uu____4511 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____4512 -> begin
(([]), (def), (false))
end))
in (match (uu____4456) with
| (binders, term, is_pat_app) -> begin
(

let uu____4544 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____4555 = (

let uu____4556 = (

let uu____4557 = (

let uu____4564 = (bv_as_unique_ident bv)
in ((uu____4564), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____4557))
in (mk_pat uu____4556))
in ((uu____4555), (term)))
end)
in (match (uu____4544) with
| (pat, term1) -> begin
(

let uu____4585 = (match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders ((map_opt ()) (fun uu____4617 -> (match (uu____4617) with
| (bv, q) -> begin
(

let uu____4632 = (resugar_arg_qual q)
in (FStar_Util.map_opt uu____4632 (fun q1 -> (

let uu____4644 = (

let uu____4645 = (

let uu____4652 = (bv_as_unique_ident bv)
in ((uu____4652), (q1)))
in FStar_Parser_AST.PatVar (uu____4645))
in (mk_pat uu____4644)))))
end))))
in (

let uu____4655 = (

let uu____4660 = (resugar_term' env term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____4660)))
in (

let uu____4663 = (universe_to_string univs1)
in ((uu____4655), (uu____4663)))))
end
| uu____4668 -> begin
(

let uu____4669 = (

let uu____4674 = (resugar_term' env term1)
in ((pat), (uu____4674)))
in (

let uu____4675 = (universe_to_string univs1)
in ((uu____4669), (uu____4675))))
end)
in ((attrs_opt), (uu____4585)))
end))
end))
end))
end))))
in (

let r = (FStar_List.map resugar_one_binding source_lbs1)
in (

let bnds = (

let f = (fun uu____4775 -> (match (uu____4775) with
| (attrs, (pb, univs1)) -> begin
(

let uu____4831 = (

let uu____4832 = (FStar_Options.print_universes ())
in (not (uu____4832)))
in (match (uu____4831) with
| true -> begin
((attrs), (pb))
end
| uu____4853 -> begin
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
| uu____4905 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____4907) -> begin
(

let s = (

let uu____4933 = (

let uu____4934 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____4934 FStar_Util.string_of_int))
in (Prims.strcat "?u" uu____4933))
in (

let uu____4935 = (mk1 FStar_Parser_AST.Wild)
in (label s uu____4935)))
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

let uu____4943 = (

let uu____4944 = (

let uu____4949 = (resugar_term' env tm)
in ((uu____4949), (qi1)))
in FStar_Parser_AST.Quote (uu____4944))
in (mk1 uu____4943)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___75_4961 -> (match (uu___75_4961) with
| FStar_Syntax_Syntax.Sequence -> begin
(

let term = (resugar_term' env e)
in (

let rec resugar_seq = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (uu____4969, ((uu____4970, (p, t11)))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____5031 = (

let uu____5032 = (

let uu____5041 = (resugar_seq t11)
in ((uu____5041), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____5032))
in (mk1 uu____5031))
end
| uu____5044 -> begin
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
end
| FStar_Syntax_Syntax.Mutable_alloc -> begin
(

let term = (resugar_term' env e)
in (match (term.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (FStar_Parser_AST.NoLetQualifier, l, t1) -> begin
(mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.Mutable), (l), (t1)))))
end
| uu____5090 -> begin
(failwith "mutable_alloc should have let term with no qualifier")
end))
end
| FStar_Syntax_Syntax.Mutable_rval -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (

let uu____5092 = (

let uu____5093 = (FStar_Syntax_Subst.compress e)
in uu____5093.FStar_Syntax_Syntax.n)
in (match (uu____5092) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.pos = uu____5097; FStar_Syntax_Syntax.vars = uu____5098}, ((term, uu____5100))::[]) -> begin
(resugar_term' env term)
end
| uu____5129 -> begin
(failwith "mutable_rval should have app term")
end)))
end))
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____5167 -> (match (uu____5167) with
| (x, uu____5173) -> begin
(resugar_term' env x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (l, uu____5175, p) -> begin
(

let uu____5177 = (

let uu____5178 = (

let uu____5185 = (resugar_term' env e)
in ((uu____5185), (l), (p)))
in FStar_Parser_AST.Labeled (uu____5178))
in (mk1 uu____5177))
end
| FStar_Syntax_Syntax.Meta_desugared (i) -> begin
(resugar_meta_desugared i)
end
| FStar_Syntax_Syntax.Meta_named (t1) -> begin
(mk1 (FStar_Parser_AST.Name (t1)))
end
| FStar_Syntax_Syntax.Meta_monadic (name1, t1) -> begin
(

let uu____5194 = (

let uu____5195 = (

let uu____5204 = (resugar_term' env e)
in (

let uu____5205 = (

let uu____5206 = (

let uu____5207 = (

let uu____5218 = (

let uu____5225 = (

let uu____5230 = (resugar_term' env t1)
in ((uu____5230), (FStar_Parser_AST.Nothing)))
in (uu____5225)::[])
in ((name1), (uu____5218)))
in FStar_Parser_AST.Construct (uu____5207))
in (mk1 uu____5206))
in ((uu____5204), (uu____5205), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____5195))
in (mk1 uu____5194))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____5248, t1) -> begin
(

let uu____5254 = (

let uu____5255 = (

let uu____5264 = (resugar_term' env e)
in (

let uu____5265 = (

let uu____5266 = (

let uu____5267 = (

let uu____5278 = (

let uu____5285 = (

let uu____5290 = (resugar_term' env t1)
in ((uu____5290), (FStar_Parser_AST.Nothing)))
in (uu____5285)::[])
in ((name1), (uu____5278)))
in FStar_Parser_AST.Construct (uu____5267))
in (mk1 uu____5266))
in ((uu____5264), (uu____5265), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____5255))
in (mk1 uu____5254))
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

let uu____5341 = (FStar_Options.print_universes ())
in (match (uu____5341) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____5361 -> begin
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

let uu____5402 = (FStar_Options.print_universes ())
in (match (uu____5402) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____5422 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____5443 = (resugar_term' env c1.FStar_Syntax_Syntax.result_typ)
in ((uu____5443), (FStar_Parser_AST.Nothing)))
in (

let uu____5444 = (FStar_Options.print_effect_args ())
in (match (uu____5444) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (

let uu____5465 = (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____5465) with
| true -> begin
(match (c1.FStar_Syntax_Syntax.effect_args) with
| (pre)::(post)::(pats)::[] -> begin
(

let post1 = (

let uu____5534 = (FStar_Syntax_Util.unthunk_lemma_post (FStar_Pervasives_Native.fst post))
in ((uu____5534), ((FStar_Pervasives_Native.snd post))))
in (

let uu____5543 = (

let uu____5552 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.true_lid (FStar_Pervasives_Native.fst pre))
in (match (uu____5552) with
| true -> begin
[]
end
| uu____5569 -> begin
(pre)::[]
end))
in (

let uu____5582 = (

let uu____5591 = (

let uu____5600 = (FStar_Syntax_Util.is_fvar FStar_Parser_Const.nil_lid (FStar_Pervasives_Native.fst pats))
in (match (uu____5600) with
| true -> begin
[]
end
| uu____5617 -> begin
(pats)::[]
end))
in (FStar_List.append ((post1)::[]) uu____5591))
in (FStar_List.append uu____5543 uu____5582))))
end
| uu____5654 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
end
| uu____5663 -> begin
c1.FStar_Syntax_Syntax.effect_args
end))
in (

let args1 = (FStar_List.map (fun uu____5683 -> (match (uu____5683) with
| (e, uu____5693) -> begin
(

let uu____5694 = (resugar_term' env e)
in ((uu____5694), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___76_5719 -> (match (uu___76_5719) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____5752 = (resugar_term' env e)
in ((uu____5752), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____5757 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____5783 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun env b r -> (

let uu____5803 = b
in (match (uu____5803) with
| (x, aq) -> begin
(

let uu____5808 = (resugar_arg_qual aq)
in (FStar_Util.map_opt uu____5808 (fun imp -> (

let e = (resugar_term' env x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____5822 = (

let uu____5823 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____5823))
in (FStar_Parser_AST.mk_binder uu____5822 r FStar_Parser_AST.Type_level imp))
end
| uu____5824 -> begin
(

let uu____5825 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____5825) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____5826 -> begin
(

let uu____5827 = (

let uu____5828 = (

let uu____5833 = (bv_as_unique_ident x)
in ((uu____5833), (e)))
in FStar_Parser_AST.Annotated (uu____5828))
in (FStar_Parser_AST.mk_binder uu____5827 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Parser_AST.pattern = (fun env v1 aqual body_bv typ_opt -> (

let mk1 = (fun a -> (

let uu____5853 = (FStar_Syntax_Syntax.range_of_bv v1)
in (FStar_Parser_AST.mk_pattern a uu____5853)))
in (

let used = (FStar_Util.set_mem v1 body_bv)
in (

let pat = (

let uu____5856 = (match (used) with
| true -> begin
(

let uu____5857 = (

let uu____5864 = (bv_as_unique_ident v1)
in ((uu____5864), (aqual)))
in FStar_Parser_AST.PatVar (uu____5857))
end
| uu____5867 -> begin
FStar_Parser_AST.PatWild
end)
in (mk1 uu____5856))
in (match (typ_opt) with
| FStar_Pervasives_Native.None -> begin
pat
end
| FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown; FStar_Syntax_Syntax.pos = uu____5870; FStar_Syntax_Syntax.vars = uu____5871}) -> begin
pat
end
| FStar_Pervasives_Native.Some (typ) -> begin
(

let uu____5881 = (FStar_Options.print_bound_var_types ())
in (match (uu____5881) with
| true -> begin
(

let uu____5882 = (

let uu____5883 = (

let uu____5894 = (

let uu____5901 = (resugar_term' env typ)
in ((uu____5901), (FStar_Pervasives_Native.None)))
in ((pat), (uu____5894)))
in FStar_Parser_AST.PatAscribed (uu____5883))
in (mk1 uu____5882))
end
| uu____5910 -> begin
pat
end))
end)))))
and resugar_bv_as_pat : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun env x qual body_bv -> (

let uu____5919 = (resugar_arg_qual qual)
in (FStar_Util.map_opt uu____5919 (fun aqual -> (

let uu____5931 = (

let uu____5936 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_left (fun _0_16 -> FStar_Pervasives_Native.Some (_0_16)) uu____5936))
in (resugar_bv_as_pat' env x aqual body_bv uu____5931))))))
and resugar_pat' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun env p branch_bv -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_pattern a p.FStar_Syntax_Syntax.p))
in (

let to_arg_qual = (fun bopt -> (FStar_Util.bind_opt bopt (fun b -> (match (b) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)
end
| uu____5966 -> begin
FStar_Pervasives_Native.None
end))))
in (

let may_drop_implicits = (fun args -> ((

let uu____5991 = (FStar_Options.print_implicits ())
in (not (uu____5991))) && (

let uu____5993 = (FStar_List.existsML (fun uu____6004 -> (match (uu____6004) with
| (pattern, is_implicit1) -> begin
(

let might_be_used = (match (pattern.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (bv) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, uu____6020) -> begin
(FStar_Util.set_mem bv branch_bv)
end
| FStar_Syntax_Syntax.Pat_wild (uu____6025) -> begin
false
end
| uu____6026 -> begin
true
end)
in (is_implicit1 && might_be_used))
end)) args)
in (not (uu____5993)))))
in (

let resugar_plain_pat_cons' = (fun fv args -> (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args))))))
in (

let rec resugar_plain_pat_cons = (fun fv args -> (

let args1 = (

let uu____6091 = (may_drop_implicits args)
in (match (uu____6091) with
| true -> begin
(filter_pattern_imp args)
end
| uu____6102 -> begin
args
end))
in (

let args2 = (FStar_List.map (fun uu____6113 -> (match (uu____6113) with
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

let uu____6159 = (

let uu____6160 = (

let uu____6161 = (filter_pattern_imp args)
in (FStar_List.isEmpty uu____6161))
in (not (uu____6160)))
in (match (uu____6159) with
| true -> begin
(FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p ((FStar_Errors.Warning_NilGivenExplicitArgs), ("Prims.Nil given explicit arguments")))
end
| uu____6178 -> begin
()
end));
(mk1 (FStar_Parser_AST.PatList ([])));
)
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.cons_lid) && (may_drop_implicits args)) -> begin
(

let uu____6197 = (filter_pattern_imp args)
in (match (uu____6197) with
| ((hd1, false))::((tl1, false))::[] -> begin
(

let hd' = (aux hd1 (FStar_Pervasives_Native.Some (false)))
in (

let uu____6237 = (aux tl1 (FStar_Pervasives_Native.Some (false)))
in (match (uu____6237) with
| {FStar_Parser_AST.pat = FStar_Parser_AST.PatList (tl'); FStar_Parser_AST.prange = p2} -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatList ((hd')::tl')) p2)
end
| tl' -> begin
(resugar_plain_pat_cons' fv ((hd')::(tl')::[]))
end)))
end
| args' -> begin
((

let uu____6253 = (

let uu____6258 = (

let uu____6259 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length args'))
in (FStar_Util.format1 "Prims.Cons applied to %s explicit arguments" uu____6259))
in ((FStar_Errors.Warning_ConsAppliedExplicitArgs), (uu____6258)))
in (FStar_Errors.log_issue p1.FStar_Syntax_Syntax.p uu____6253));
(resugar_plain_pat_cons fv args);
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((is_tuple_constructor_lid fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) && (may_drop_implicits args)) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.filter_map (fun uu____6304 -> (match (uu____6304) with
| (p2, is_implicit1) -> begin
(match (is_implicit1) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____6315 -> begin
(

let uu____6316 = (aux p2 (FStar_Pervasives_Native.Some (false)))
in FStar_Pervasives_Native.Some (uu____6316))
end)
end))))
in (

let is_dependent_tuple = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (mk1 (FStar_Parser_AST.PatTuple (((args1), (is_dependent_tuple)))))))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____6320; FStar_Syntax_Syntax.fv_delta = uu____6321; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____6348 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____6348 FStar_List.rev))
in (

let args1 = (

let uu____6364 = (FStar_All.pipe_right args (FStar_List.map (fun uu____6384 -> (match (uu____6384) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____6364 FStar_List.rev))
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

let uu____6458 = (map21 tl1 [])
in (((hd1), ((mk1 FStar_Parser_AST.PatWild))))::uu____6458)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____6481 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____6481)
end))
in (

let args2 = (

let uu____6499 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____6499 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(resugar_plain_pat_cons fv args)
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____6541 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____6541) with
| FStar_Pervasives_Native.Some (op, uu____6551) -> begin
(

let uu____6562 = (

let uu____6563 = (FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
in FStar_Parser_AST.PatOp (uu____6563))
in (mk1 uu____6562))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6570 = (to_arg_qual imp_opt)
in (resugar_bv_as_pat' env v1 uu____6570 branch_bv FStar_Pervasives_Native.None))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____6575) -> begin
(mk1 FStar_Parser_AST.PatWild)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, term) -> begin
(resugar_bv_as_pat' env bv (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) branch_bv (FStar_Pervasives_Native.Some (term)))
end))
in (aux p FStar_Pervasives_Native.None)))))))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___77_6590 -> (match (uu___77_6590) with
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
| uu____6595 -> begin
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
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reifiable)
end
| FStar_Syntax_Syntax.Reflectable (uu____6596) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____6597) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____6598) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____6603) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____6612) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____6621) -> begin
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


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___78_6626 -> (match (uu___78_6626) with
| FStar_Syntax_Syntax.SetOptions (s) -> begin
FStar_Parser_AST.SetOptions (s)
end
| FStar_Syntax_Syntax.ResetOptions (s) -> begin
FStar_Parser_AST.ResetOptions (s)
end
| FStar_Syntax_Syntax.LightOff -> begin
FStar_Parser_AST.LightOff
end))


let resugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_Syntax_Syntax.sigelts * FStar_Parser_AST.tycon) = (fun env datacon_ses se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____6662, datacons) -> begin
(

let uu____6672 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____6699, uu____6700, uu____6701, inductive_lid, uu____6703, uu____6704) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____6709 -> begin
(failwith "unexpected")
end))))
in (match (uu____6672) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____6726 = (FStar_Options.print_implicits ())
in (match (uu____6726) with
| true -> begin
bs
end
| uu____6727 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 ((map_opt ()) (fun b -> (resugar_binder' env b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____6736 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___79_6741 -> (match (uu___79_6741) with
| FStar_Syntax_Syntax.RecordType (uu____6742) -> begin
true
end
| uu____6751 -> begin
false
end))))
in (match (uu____6736) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____6803, univs1, term, uu____6806, num, uu____6808) -> begin
(

let uu____6813 = (

let uu____6814 = (FStar_Syntax_Subst.compress term)
in uu____6814.FStar_Syntax_Syntax.n)
in (match (uu____6813) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____6828) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____6889 -> (match (uu____6889) with
| (b, qual) -> begin
(

let uu____6904 = (

let uu____6905 = (bv_as_unique_ident b)
in (FStar_Syntax_Util.unmangle_field_name uu____6905))
in (

let uu____6906 = (resugar_term' env b.FStar_Syntax_Syntax.sort)
in ((uu____6904), (uu____6906), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____6917 -> begin
(failwith "unexpected")
end))
end
| uu____6928 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____6982 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____7053, num, uu____7055) -> begin
(

let c = (

let uu____7073 = (

let uu____7076 = (resugar_term' env term)
in FStar_Pervasives_Native.Some (uu____7076))
in ((l.FStar_Ident.ident), (uu____7073), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____7093 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____7169 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____7193 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____7193; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme'' : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env name ts -> (

let uu____7219 = ts
in (match (uu____7219) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____7227 = (

let uu____7228 = (

let uu____7241 = (

let uu____7250 = (

let uu____7257 = (

let uu____7258 = (

let uu____7271 = (resugar_term' env typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____7271)))
in FStar_Parser_AST.TyconAbbrev (uu____7258))
in ((uu____7257), (FStar_Pervasives_Native.None)))
in (uu____7250)::[])
in ((false), (uu____7241)))
in FStar_Parser_AST.Tycon (uu____7228))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____7227)))
end)))


let resugar_tscheme' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun env ts -> (resugar_tscheme'' env "tsheme" ts))


let resugar_eff_decl' : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun env for_free r q ed -> (

let resugar_action = (fun d for_free1 -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____7349 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____7349) with
| (bs, action_defn) -> begin
(

let uu____7356 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____7356) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____7364 = (FStar_Options.print_implicits ())
in (match (uu____7364) with
| true -> begin
action_params
end
| uu____7365 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____7369 = (FStar_All.pipe_right action_params1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____7369 FStar_List.rev))
in (

let action_defn1 = (resugar_term' env action_defn)
in (

let action_typ1 = (resugar_term' env action_typ)
in (match (for_free1) with
| true -> begin
(

let a = (

let uu____7383 = (

let uu____7394 = (FStar_Ident.lid_of_str "construct")
in ((uu____7394), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____7383))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____7440 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____7468 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____7468) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____7476 = (FStar_Options.print_implicits ())
in (match (uu____7476) with
| true -> begin
eff_binders
end
| uu____7477 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____7481 = (FStar_All.pipe_right eff_binders1 ((map_opt ()) (fun b -> (resugar_binder' env b r))))
in (FStar_All.pipe_right uu____7481 FStar_List.rev))
in (

let eff_typ1 = (resugar_term' env eff_typ)
in (

let ret_wp = (resugar_tscheme'' env "ret_wp" ed.FStar_Syntax_Syntax.ret_wp)
in (

let bind_wp = (resugar_tscheme'' env "bind_wp" ed.FStar_Syntax_Syntax.ret_wp)
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
| uu____7513 -> begin
(repr)::(return_repr)::(bind_repr)::(ret_wp)::(bind_wp)::(if_then_else1)::(ite_wp)::(stronger)::(close_wp)::(assert_p)::(assume_p)::(null_wp)::(trivial)::[]
end)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls)))))))))))))))))))))))))
end)))))


let resugar_sigelt' : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____7545) -> begin
(

let uu____7554 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____7576) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7593) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____7600) -> begin
false
end
| uu____7615 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____7554) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____7651 se1 -> (match (uu____7651) with
| (datacon_ses1, tycons) -> begin
(

let uu____7677 = (resugar_typ env datacon_ses1 se1)
in (match (uu____7677) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____7692 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____7692) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____7727 = (

let uu____7728 = (

let uu____7729 = (

let uu____7742 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (uu____7742)))
in FStar_Parser_AST.Tycon (uu____7729))
in (decl'_to_decl se uu____7728))
in FStar_Pervasives_Native.Some (uu____7727))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____7773, uu____7774, uu____7775, uu____7776, uu____7777) -> begin
(

let uu____7782 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____7782))
end
| uu____7785 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____7788 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____7794) -> begin
(

let uu____7799 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___80_7805 -> (match (uu___80_7805) with
| FStar_Syntax_Syntax.Projector (uu____7806, uu____7807) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____7808) -> begin
true
end
| uu____7809 -> begin
false
end))))
in (match (uu____7799) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7812 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term' env desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____7834) -> begin
(

let uu____7863 = (

let uu____7864 = (

let uu____7865 = (

let uu____7876 = (FStar_List.map FStar_Pervasives_Native.snd lets)
in ((isrec), (uu____7876)))
in FStar_Parser_AST.TopLevelLet (uu____7865))
in (decl'_to_decl se uu____7864))
in FStar_Pervasives_Native.Some (uu____7863))
end
| uu____7913 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____7917, fml) -> begin
(

let uu____7919 = (

let uu____7920 = (

let uu____7921 = (

let uu____7926 = (resugar_term' env fml)
in ((lid.FStar_Ident.ident), (uu____7926)))
in FStar_Parser_AST.Assume (uu____7921))
in (decl'_to_decl se uu____7920))
in FStar_Pervasives_Native.Some (uu____7919))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____7928 = (resugar_eff_decl' env false se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____7928))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let uu____7930 = (resugar_eff_decl' env true se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____7930))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____7939, t) -> begin
(

let uu____7951 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____7951))
end
| uu____7952 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____7960, t) -> begin
(

let uu____7972 = (resugar_term' env t)
in FStar_Pervasives_Native.Some (uu____7972))
end
| uu____7973 -> begin
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
| uu____7997 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____8006 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____8006)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags1) -> begin
(

let uu____8016 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____8016) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____8026 = (FStar_Options.print_implicits ())
in (match (uu____8026) with
| true -> begin
bs1
end
| uu____8027 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 ((map_opt ()) (fun b -> (resugar_binder' env b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____8035 = (

let uu____8036 = (

let uu____8037 = (

let uu____8050 = (

let uu____8059 = (

let uu____8066 = (

let uu____8067 = (

let uu____8080 = (resugar_comp' env c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____8080)))
in FStar_Parser_AST.TyconAbbrev (uu____8067))
in ((uu____8066), (FStar_Pervasives_Native.None)))
in (uu____8059)::[])
in ((false), (uu____8050)))
in FStar_Parser_AST.Tycon (uu____8037))
in (decl'_to_decl se uu____8036))
in FStar_Pervasives_Native.Some (uu____8035))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____8108 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____8108))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____8112 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___81_8118 -> (match (uu___81_8118) with
| FStar_Syntax_Syntax.Projector (uu____8119, uu____8120) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____8121) -> begin
true
end
| uu____8122 -> begin
false
end))))
in (match (uu____8112) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____8125 -> begin
(

let t' = (

let uu____8127 = ((

let uu____8130 = (FStar_Options.print_universes ())
in (not (uu____8130))) || (FStar_List.isEmpty uvs))
in (match (uu____8127) with
| true -> begin
(resugar_term' env t)
end
| uu____8131 -> begin
(

let uu____8132 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____8132) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____8140 = (resugar_term' env t1)
in (label universes uu____8140)))
end))
end))
in (

let uu____8141 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____8141)))
end))
end
| FStar_Syntax_Syntax.Sig_splice (ids, t) -> begin
(

let uu____8148 = (

let uu____8149 = (

let uu____8150 = (

let uu____8157 = (FStar_List.map (fun l -> l.FStar_Ident.ident) ids)
in (

let uu____8162 = (resugar_term' env t)
in ((uu____8157), (uu____8162))))
in FStar_Parser_AST.Splice (uu____8150))
in (decl'_to_decl se uu____8149))
in FStar_Pervasives_Native.Some (uu____8148))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____8165) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____8182) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____8197) -> begin
FStar_Pervasives_Native.None
end))


let empty_env : FStar_Syntax_DsEnv.env = (FStar_Syntax_DsEnv.empty_env ())


let noenv : 'a . (FStar_Syntax_DsEnv.env  ->  'a)  ->  'a = (fun f -> (f empty_env))


let resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let uu____8218 = (noenv resugar_term')
in (uu____8218 t)))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (

let uu____8235 = (noenv resugar_sigelt')
in (uu____8235 se)))


let resugar_comp : FStar_Syntax_Syntax.comp  ->  FStar_Parser_AST.term = (fun c -> (

let uu____8252 = (noenv resugar_comp')
in (uu____8252 c)))


let resugar_pat : FStar_Syntax_Syntax.pat  ->  FStar_Syntax_Syntax.bv FStar_Util.set  ->  FStar_Parser_AST.pattern = (fun p branch_bv -> (

let uu____8274 = (noenv resugar_pat')
in (uu____8274 p branch_bv)))


let resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____8307 = (noenv resugar_binder')
in (uu____8307 b r)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (

let uu____8331 = (noenv resugar_tscheme')
in (uu____8331 ts)))


let resugar_eff_decl : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun for_free r q ed -> (

let uu____8363 = (noenv resugar_eff_decl')
in (uu____8363 for_free r q ed)))





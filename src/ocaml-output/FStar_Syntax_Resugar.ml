
open Prims
open FStar_Pervasives

let doc_to_string : FStar_Pprint.document  ->  Prims.string = (fun doc1 -> (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1))


let parser_term_to_string : FStar_Parser_AST.term  ->  Prims.string = (fun t -> (

let uu____9 = (FStar_Parser_ToDocument.term_to_document t)
in (doc_to_string uu____9)))


let map_opt = (fun f l -> (

let uu____38 = (FStar_Util.choose_map (fun uu____45 x -> (

let uu____47 = (f x)
in ((()), (uu____47)))) () l)
in (FStar_Pervasives_Native.snd uu____38)))


let bv_as_unique_ident : FStar_Syntax_Syntax.bv  ->  FStar_Ident.ident = (fun x -> (

let unique_name = (match ((FStar_Util.starts_with FStar_Ident.reserved_prefix x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)) with
| true -> begin
(

let uu____56 = (FStar_Util.string_of_int x.FStar_Syntax_Syntax.index)
in (Prims.strcat x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText uu____56))
end
| uu____57 -> begin
x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText
end)
in (FStar_Ident.mk_ident ((unique_name), (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))))


let filter_imp = (fun a -> (FStar_All.pipe_right a (FStar_List.filter (fun uu___187_93 -> (match (uu___187_93) with
| (uu____97, FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____98))) -> begin
false
end
| uu____100 -> begin
true
end)))))


let resugar_arg_qual : FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option FStar_Pervasives_Native.option = (fun q -> (match (q) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (b)) -> begin
(match (b) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____121 -> begin
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
| uu____143 -> begin
((n1), (u))
end))


let universe_to_string : FStar_Ident.ident Prims.list  ->  Prims.string = (fun univs1 -> (

let uu____150 = (FStar_Options.print_universes ())
in (match (uu____150) with
| true -> begin
(

let uu____151 = (FStar_List.map (fun x -> x.FStar_Ident.idText) univs1)
in (FStar_All.pipe_right uu____151 (FStar_String.concat ", ")))
end
| uu____156 -> begin
""
end)))


let rec resugar_universe : FStar_Syntax_Syntax.universe  ->  FStar_Range.range  ->  FStar_Parser_AST.term = (fun u r -> (

let mk1 = (fun a r1 -> (FStar_Parser_AST.mk_term a r1 FStar_Parser_AST.Un))
in (match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(mk1 (FStar_Parser_AST.Const (FStar_Const.Const_int ((("0"), (FStar_Pervasives_Native.None))))) r)
end
| FStar_Syntax_Syntax.U_succ (uu____177) -> begin
(

let uu____178 = (universe_to_int (Prims.parse_int "0") u)
in (match (uu____178) with
| (n1, u1) -> begin
(match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____183 = (

let uu____184 = (

let uu____185 = (

let uu____191 = (FStar_Util.string_of_int n1)
in ((uu____191), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____185))
in FStar_Parser_AST.Const (uu____184))
in (mk1 uu____183 r))
end
| uu____197 -> begin
(

let e1 = (

let uu____199 = (

let uu____200 = (

let uu____201 = (

let uu____207 = (FStar_Util.string_of_int n1)
in ((uu____207), (FStar_Pervasives_Native.None)))
in FStar_Const.Const_int (uu____201))
in FStar_Parser_AST.Const (uu____200))
in (mk1 uu____199 r))
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
| uu____217 -> begin
(

let t = (

let uu____220 = (

let uu____221 = (FStar_Ident.lid_of_path (("max")::[]) r)
in FStar_Parser_AST.Var (uu____221))
in (mk1 uu____220 r))
in (FStar_List.fold_left (fun acc x -> (

let uu____227 = (

let uu____228 = (

let uu____232 = (resugar_universe x r)
in ((acc), (uu____232), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____228))
in (mk1 uu____227 r))) t l))
end)
end
| FStar_Syntax_Syntax.U_name (u1) -> begin
(mk1 (FStar_Parser_AST.Uvar (u1)) r)
end
| FStar_Syntax_Syntax.U_unif (uu____234) -> begin
(mk1 FStar_Parser_AST.Wild r)
end
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(

let id = (

let uu____241 = (

let uu____244 = (

let uu____245 = (FStar_Util.string_of_int x)
in (FStar_Util.strcat "uu__univ_bvar_" uu____245))
in ((uu____244), (r)))
in (FStar_Ident.mk_ident uu____241))
in (mk1 (FStar_Parser_AST.Uvar (id)) r))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(mk1 FStar_Parser_AST.Wild r)
end)))


let string_to_op : Prims.string  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun s -> (

let name_of_op = (fun uu___188_259 -> (match (uu___188_259) with
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
| "Slash" -> begin
FStar_Pervasives_Native.Some ((("/"), ((Prims.parse_int "0"))))
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
| uu____297 -> begin
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
| uu____311 -> begin
(match ((FStar_Util.starts_with s "op_")) with
| true -> begin
(

let s1 = (

let uu____317 = (FStar_Util.substring_from s (FStar_String.length "op_"))
in (FStar_Util.split uu____317 "_"))
in (match (s1) with
| (op)::[] -> begin
(name_of_op op)
end
| uu____326 -> begin
(

let op = (

let uu____329 = (FStar_List.map name_of_op s1)
in (FStar_List.fold_left (fun acc x -> (match (x) with
| FStar_Pervasives_Native.Some (op, uu____350) -> begin
(Prims.strcat acc op)
end
| FStar_Pervasives_Native.None -> begin
(failwith "wrong composed operator format")
end)) "" uu____329))
in FStar_Pervasives_Native.Some (((op), ((Prims.parse_int "0")))))
end))
end
| uu____357 -> begin
FStar_Pervasives_Native.None
end)
end)))


let rec resugar_term_as_op : FStar_Syntax_Syntax.term  ->  (Prims.string * Prims.int) FStar_Pervasives_Native.option = (fun t -> (

let infix_prim_ops = (((FStar_Parser_Const.op_Addition), ("+")))::(((FStar_Parser_Const.op_Subtraction), ("-")))::(((FStar_Parser_Const.op_Minus), ("-")))::(((FStar_Parser_Const.op_Multiply), ("*")))::(((FStar_Parser_Const.op_Division), ("/")))::(((FStar_Parser_Const.op_Modulus), ("%")))::(((FStar_Parser_Const.read_lid), ("!")))::(((FStar_Parser_Const.list_append_lid), ("@")))::(((FStar_Parser_Const.list_tot_append_lid), ("@")))::(((FStar_Parser_Const.strcat_lid), ("^")))::(((FStar_Parser_Const.pipe_right_lid), ("|>")))::(((FStar_Parser_Const.pipe_left_lid), ("<|")))::(((FStar_Parser_Const.op_Eq), ("=")))::(((FStar_Parser_Const.op_ColonEq), (":=")))::(((FStar_Parser_Const.op_notEq), ("<>")))::(((FStar_Parser_Const.not_lid), ("~")))::(((FStar_Parser_Const.op_And), ("&&")))::(((FStar_Parser_Const.op_Or), ("||")))::(((FStar_Parser_Const.op_LTE), ("<=")))::(((FStar_Parser_Const.op_GTE), (">=")))::(((FStar_Parser_Const.op_LT), ("<")))::(((FStar_Parser_Const.op_GT), (">")))::(((FStar_Parser_Const.op_Modulus), ("mod")))::(((FStar_Parser_Const.and_lid), ("/\\")))::(((FStar_Parser_Const.or_lid), ("\\/")))::(((FStar_Parser_Const.imp_lid), ("==>")))::(((FStar_Parser_Const.iff_lid), ("<==>")))::(((FStar_Parser_Const.precedes_lid), ("<<")))::(((FStar_Parser_Const.eq2_lid), ("==")))::(((FStar_Parser_Const.eq3_lid), ("===")))::(((FStar_Parser_Const.forall_lid), ("forall")))::(((FStar_Parser_Const.exists_lid), ("exists")))::(((FStar_Parser_Const.salloc_lid), ("alloc")))::[]
in (

let fallback = (fun fv -> (

let uu____449 = (FStar_All.pipe_right infix_prim_ops (FStar_Util.find_opt (fun d -> (FStar_Syntax_Syntax.fv_eq_lid fv (FStar_Pervasives_Native.fst d)))))
in (match (uu____449) with
| FStar_Pervasives_Native.Some (op) -> begin
FStar_Pervasives_Native.Some ((((FStar_Pervasives_Native.snd op)), ((Prims.parse_int "0"))))
end
| uu____475 -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let str = (match ((length1 = (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____487 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (match ((FStar_Util.starts_with str "dtuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("dtuple"), ((Prims.parse_int "0"))))
end
| uu____499 -> begin
(match ((FStar_Util.starts_with str "tuple")) with
| true -> begin
FStar_Pervasives_Native.Some ((("tuple"), ((Prims.parse_int "0"))))
end
| uu____505 -> begin
(match ((FStar_Util.starts_with str "try_with")) with
| true -> begin
FStar_Pervasives_Native.Some ((("try_with"), ((Prims.parse_int "0"))))
end
| uu____511 -> begin
(

let uu____512 = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.sread_lid)
in (match (uu____512) with
| true -> begin
FStar_Pervasives_Native.Some (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str), ((Prims.parse_int "0"))))
end
| uu____518 -> begin
FStar_Pervasives_Native.None
end))
end)
end)
end)))
end)))
in (

let uu____521 = (

let uu____522 = (FStar_Syntax_Subst.compress t)
in uu____522.FStar_Syntax_Syntax.n)
in (match (uu____521) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let length1 = (FStar_String.length fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.nsstr)
in (

let s = (match ((length1 = (Prims.parse_int "0"))) with
| true -> begin
fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str
end
| uu____537 -> begin
(FStar_Util.substring_from fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let uu____544 = (string_to_op s)
in (match (uu____544) with
| FStar_Pervasives_Native.Some (t1) -> begin
FStar_Pervasives_Native.Some (t1)
end
| uu____558 -> begin
(fallback fv)
end))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, us) -> begin
(resugar_term_as_op e)
end
| uu____568 -> begin
FStar_Pervasives_Native.None
end)))))


let is_true_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true)) -> begin
true
end
| uu____575 -> begin
false
end))


let is_wild_pat : FStar_Syntax_Syntax.pat  ->  Prims.bool = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_wild (uu____580) -> begin
true
end
| uu____581 -> begin
false
end))


let rec resugar_term : FStar_Syntax_Syntax.term  ->  FStar_Parser_AST.term = (fun t -> (

let mk1 = (fun a -> (FStar_Parser_AST.mk_term a t.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un))
in (

let name = (fun a r -> (

let uu____610 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Name (uu____610)))
in (

let var = (fun a r -> (

let uu____618 = (FStar_Ident.lid_of_path ((a)::[]) r)
in FStar_Parser_AST.Var (uu____618)))
in (

let uu____619 = (

let uu____620 = (FStar_Syntax_Subst.compress t)
in uu____620.FStar_Syntax_Syntax.n)
in (match (uu____619) with
| FStar_Syntax_Syntax.Tm_delayed (uu____623) -> begin
(failwith "Tm_delayed is impossible after compress")
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let l = (

let uu____640 = (

let uu____642 = (bv_as_unique_ident x)
in (uu____642)::[])
in (FStar_Ident.lid_of_ids uu____640))
in (mk1 (FStar_Parser_AST.Var (l))))
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let l = (

let uu____645 = (

let uu____647 = (bv_as_unique_ident x)
in (uu____647)::[])
in (FStar_Ident.lid_of_ids uu____645))
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
| uu____658 -> begin
(FStar_Util.substring_from a.FStar_Ident.str (length1 + (Prims.parse_int "1")))
end)
in (

let is_prefix = (Prims.strcat FStar_Ident.reserved_prefix "is_")
in (match ((FStar_Util.starts_with s is_prefix)) with
| true -> begin
(

let rest = (FStar_Util.substring_from s (FStar_String.length is_prefix))
in (

let uu____671 = (

let uu____672 = (FStar_Ident.lid_of_path ((rest)::[]) t.FStar_Syntax_Syntax.pos)
in FStar_Parser_AST.Discrim (uu____672))
in (mk1 uu____671)))
end
| uu____673 -> begin
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
| uu____685 -> begin
(failwith "wrong projector format")
end)))
end
| uu____687 -> begin
(

let uu____688 = (((FStar_Ident.lid_equals a FStar_Parser_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Parser_Const.assume_lid)) || (

let uu____691 = (

let uu____692 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____692))
in (

let uu____693 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____691 <> uu____693))))
in (match (uu____688) with
| true -> begin
(

let uu____694 = (var a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____694))
end
| uu____695 -> begin
(

let uu____696 = (name a.FStar_Ident.str t.FStar_Syntax_Syntax.pos)
in (mk1 uu____696))
end))
end)
end)))))
end
| FStar_Syntax_Syntax.Tm_uinst (e, universes) -> begin
(

let uu____703 = (FStar_Options.print_universes ())
in (match (uu____703) with
| true -> begin
(

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (

let uu____710 = (

let uu____711 = (

let uu____715 = (resugar_universe x t.FStar_Syntax_Syntax.pos)
in ((acc), (uu____715), (FStar_Parser_AST.UnivApp)))
in FStar_Parser_AST.App (uu____711))
in (mk1 uu____710))) e1 universes))
end
| uu____716 -> begin
(resugar_term e)
end))
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____718 = (FStar_Syntax_Syntax.is_teff t)
in (match (uu____718) with
| true -> begin
(

let uu____719 = (name "Effect" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____719))
end
| uu____720 -> begin
(mk1 (FStar_Parser_AST.Const (c)))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(match (u) with
| FStar_Syntax_Syntax.U_zero -> begin
(

let uu____722 = (name "Type0" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____722))
end
| FStar_Syntax_Syntax.U_unknown -> begin
(

let uu____723 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____723))
end
| uu____724 -> begin
(

let uu____725 = (FStar_Options.print_universes ())
in (match (uu____725) with
| true -> begin
(

let u1 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in (

let l = (FStar_Ident.lid_of_path (("Type")::[]) t.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((l), ((((u1), (FStar_Parser_AST.UnivApp)))::[])))))))
end
| uu____735 -> begin
(

let uu____736 = (name "Type" t.FStar_Syntax_Syntax.pos)
in (mk1 uu____736))
end))
end)
end
| FStar_Syntax_Syntax.Tm_abs (xs, body, uu____739) -> begin
(

let uu____752 = (FStar_Syntax_Subst.open_term xs body)
in (match (uu____752) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____758 = (FStar_Options.print_implicits ())
in (match (uu____758) with
| true -> begin
xs1
end
| uu____759 -> begin
(filter_imp xs1)
end))
in (

let patterns = (FStar_All.pipe_right xs2 (FStar_List.choose (fun uu____768 -> (match (uu____768) with
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

let uu____788 = (FStar_Syntax_Subst.open_comp xs body)
in (match (uu____788) with
| (xs1, body1) -> begin
(

let xs2 = (

let uu____794 = (FStar_Options.print_implicits ())
in (match (uu____794) with
| true -> begin
xs1
end
| uu____795 -> begin
(filter_imp xs1)
end))
in (

let body2 = (resugar_comp body1)
in (

let xs3 = (

let uu____799 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (FStar_All.pipe_right uu____799 FStar_List.rev))
in (

let rec aux = (fun body3 uu___189_813 -> (match (uu___189_813) with
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

let uu____826 = (

let uu____829 = (

let uu____830 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____830)::[])
in (FStar_Syntax_Subst.open_term uu____829 phi))
in (match (uu____826) with
| (x1, phi1) -> begin
(

let b = (

let uu____834 = (

let uu____836 = (FStar_List.hd x1)
in (resugar_binder uu____836 t.FStar_Syntax_Syntax.pos))
in (FStar_Util.must uu____834))
in (

let uu____839 = (

let uu____840 = (

let uu____843 = (resugar_term phi1)
in ((b), (uu____843)))
in FStar_Parser_AST.Refine (uu____840))
in (mk1 uu____839)))
end))
end
| FStar_Syntax_Syntax.Tm_app (e, args) -> begin
(

let rec last1 = (fun uu___190_873 -> (match (uu___190_873) with
| (hd1)::[] -> begin
(hd1)::[]
end
| (hd1)::tl1 -> begin
(last1 tl1)
end
| uu____920 -> begin
(failwith "last of an empty list")
end))
in (

let rec last_two = (fun uu___191_944 -> (match (uu___191_944) with
| [] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (uu____964)::[] -> begin
(failwith "last two elements of a list with less than two elements ")
end
| (a1)::(a2)::[] -> begin
(a1)::(a2)::[]
end
| (uu____1016)::t1 -> begin
(last_two t1)
end))
in (

let rec last_three = (fun uu___192_1044 -> (match (uu___192_1044) with
| [] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1064)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (uu____1082)::(uu____1083)::[] -> begin
(failwith "last three elements of a list with less than three elements ")
end
| (a1)::(a2)::(a3)::[] -> begin
(a1)::(a2)::(a3)::[]
end
| (uu____1156)::t1 -> begin
(last_three t1)
end))
in (

let resugar_as_app = (fun e1 args1 -> (

let args2 = (FStar_All.pipe_right args1 (FStar_List.map (fun uu____1209 -> (match (uu____1209) with
| (e2, qual) -> begin
(

let uu____1220 = (resugar_term e2)
in ((uu____1220), (qual)))
end))))
in (

let e2 = (resugar_term e1)
in (FStar_List.fold_left (fun acc uu____1232 -> (match (uu____1232) with
| (x, qual) -> begin
(

let uu____1240 = (

let uu____1241 = (

let uu____1245 = (resugar_imp qual)
in ((acc), (x), (uu____1245)))
in FStar_Parser_AST.App (uu____1241))
in (mk1 uu____1240))
end)) e2 args2))))
in (

let args1 = (

let uu____1252 = (FStar_Options.print_implicits ())
in (match (uu____1252) with
| true -> begin
args
end
| uu____1258 -> begin
(filter_imp args)
end))
in (

let uu____1261 = (resugar_term_as_op e)
in (match (uu____1261) with
| FStar_Pervasives_Native.None -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some ("tuple", uu____1267) -> begin
(match (args1) with
| ((fst1, uu____1271))::((snd1, uu____1273))::rest -> begin
(

let e1 = (

let uu____1297 = (

let uu____1298 = (

let uu____1302 = (

let uu____1304 = (resugar_term fst1)
in (

let uu____1305 = (

let uu____1307 = (resugar_term snd1)
in (uu____1307)::[])
in (uu____1304)::uu____1305))
in (((FStar_Ident.id_of_text "*")), (uu____1302)))
in FStar_Parser_AST.Op (uu____1298))
in (mk1 uu____1297))
in (FStar_List.fold_left (fun acc uu____1317 -> (match (uu____1317) with
| (x, uu____1321) -> begin
(

let uu____1322 = (

let uu____1323 = (

let uu____1327 = (

let uu____1329 = (

let uu____1331 = (resugar_term x)
in (uu____1331)::[])
in (e1)::uu____1329)
in (((FStar_Ident.id_of_text "*")), (uu____1327)))
in FStar_Parser_AST.Op (uu____1323))
in (mk1 uu____1322))
end)) e1 rest))
end
| uu____1333 -> begin
(resugar_as_app e args1)
end)
end
| FStar_Pervasives_Native.Some ("dtuple", uu____1339) when ((FStar_List.length args1) > (Prims.parse_int "0")) -> begin
(

let args2 = (last1 args1)
in (

let body = (match (args2) with
| ((b, uu____1364))::[] -> begin
b
end
| uu____1377 -> begin
(failwith "wrong arguments to dtuple")
end)
in (

let uu____1385 = (

let uu____1386 = (FStar_Syntax_Subst.compress body)
in uu____1386.FStar_Syntax_Syntax.n)
in (match (uu____1385) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____1391) -> begin
(

let uu____1404 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____1404) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____1410 = (FStar_Options.print_implicits ())
in (match (uu____1410) with
| true -> begin
xs1
end
| uu____1411 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let body3 = (resugar_term body2)
in (mk1 (FStar_Parser_AST.Sum (((xs3), (body3))))))))
end))
end
| uu____1419 -> begin
(

let args3 = (FStar_All.pipe_right args2 (FStar_List.map (fun uu____1433 -> (match (uu____1433) with
| (e1, qual) -> begin
(resugar_term e1)
end))))
in (

let e1 = (resugar_term e)
in (FStar_List.fold_left (fun acc x -> (mk1 (FStar_Parser_AST.App (((acc), (x), (FStar_Parser_AST.Nothing)))))) e1 args3)))
end))))
end
| FStar_Pervasives_Native.Some ("dtuple", uu____1443) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (ref_read, uu____1447) when (ref_read = FStar_Parser_Const.sread_lid.FStar_Ident.str) -> begin
(

let uu____1450 = (FStar_List.hd args1)
in (match (uu____1450) with
| (t1, uu____1460) -> begin
(

let uu____1465 = (

let uu____1466 = (FStar_Syntax_Subst.compress t1)
in uu____1466.FStar_Syntax_Syntax.n)
in (match (uu____1465) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Util.field_projector_contains_constructor fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str) -> begin
(

let f = (FStar_Ident.lid_of_path ((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v.FStar_Ident.str)::[]) t1.FStar_Syntax_Syntax.pos)
in (

let uu____1471 = (

let uu____1472 = (

let uu____1475 = (resugar_term t1)
in ((uu____1475), (f)))
in FStar_Parser_AST.Project (uu____1472))
in (mk1 uu____1471)))
end
| uu____1476 -> begin
(resugar_term t1)
end))
end))
end
| FStar_Pervasives_Native.Some ("try_with", uu____1477) when ((FStar_List.length args1) > (Prims.parse_int "1")) -> begin
(

let new_args = (last_two args1)
in (

let uu____1496 = (match (new_args) with
| ((a1, uu____1510))::((a2, uu____1512))::[] -> begin
((a1), (a2))
end
| uu____1537 -> begin
(failwith "wrong arguments to try_with")
end)
in (match (uu____1496) with
| (body, handler) -> begin
(

let decomp = (fun term -> (

let uu____1563 = (

let uu____1564 = (FStar_Syntax_Subst.compress term)
in uu____1564.FStar_Syntax_Syntax.n)
in (match (uu____1563) with
| FStar_Syntax_Syntax.Tm_abs (x, e1, uu____1569) -> begin
(

let uu____1582 = (FStar_Syntax_Subst.open_term x e1)
in (match (uu____1582) with
| (x1, e2) -> begin
e2
end))
end
| uu____1587 -> begin
(failwith "wrong argument format to try_with")
end)))
in (

let body1 = (

let uu____1589 = (decomp body)
in (resugar_term uu____1589))
in (

let handler1 = (

let uu____1591 = (decomp handler)
in (resugar_term uu____1591))
in (

let rec resugar_body = (fun t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Match (e1, ((uu____1597, uu____1598, b))::[]) -> begin
b
end
| FStar_Parser_AST.Let (uu____1615, uu____1616, b) -> begin
b
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____1629 = (

let uu____1630 = (

let uu____1635 = (resugar_body t11)
in ((uu____1635), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____1630))
in (mk1 uu____1629))
end
| uu____1637 -> begin
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
| uu____1670 -> begin
[]
end))
in (

let branches = (resugar_branches handler1)
in (mk1 (FStar_Parser_AST.TryWith (((e1), (branches))))))))))))
end)))
end
| FStar_Pervasives_Native.Some ("try_with", uu____1686) -> begin
(resugar_as_app e args1)
end
| FStar_Pervasives_Native.Some (op, uu____1690) when ((op = "forall") || (op = "exists")) -> begin
(

let rec uncurry = (fun xs pat t1 -> (match (t1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.QExists (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| FStar_Parser_AST.QForall (x, p, body) -> begin
(uncurry (FStar_List.append x xs) (FStar_List.append p pat) body)
end
| uu____1741 -> begin
((xs), (pat), (t1))
end))
in (

let resugar = (fun body -> (

let uu____1749 = (

let uu____1750 = (FStar_Syntax_Subst.compress body)
in uu____1750.FStar_Syntax_Syntax.n)
in (match (uu____1749) with
| FStar_Syntax_Syntax.Tm_abs (xs, body1, uu____1755) -> begin
(

let uu____1768 = (FStar_Syntax_Subst.open_term xs body1)
in (match (uu____1768) with
| (xs1, body2) -> begin
(

let xs2 = (

let uu____1774 = (FStar_Options.print_implicits ())
in (match (uu____1774) with
| true -> begin
xs1
end
| uu____1775 -> begin
(filter_imp xs1)
end))
in (

let xs3 = (FStar_All.pipe_right xs2 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let uu____1781 = (

let uu____1786 = (

let uu____1787 = (FStar_Syntax_Subst.compress body2)
in uu____1787.FStar_Syntax_Syntax.n)
in (match (uu____1786) with
| FStar_Syntax_Syntax.Tm_meta (e1, m) -> begin
(

let body3 = (resugar_term e1)
in (

let pats = (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun uu____1831 -> (match (uu____1831) with
| (e2, uu____1835) -> begin
(resugar_term e2)
end))))) pats)
end
| FStar_Syntax_Syntax.Meta_labeled (s, r, uu____1838) -> begin
(

let uu____1839 = (

let uu____1841 = (

let uu____1842 = (name s r)
in (mk1 uu____1842))
in (uu____1841)::[])
in (uu____1839)::[])
end
| uu____1845 -> begin
(failwith "wrong pattern format for QForall/QExists")
end)
in ((pats), (body3))))
end
| uu____1850 -> begin
(

let uu____1851 = (resugar_term body2)
in (([]), (uu____1851)))
end))
in (match (uu____1781) with
| (pats, body3) -> begin
(

let uu____1861 = (uncurry xs3 pats body3)
in (match (uu____1861) with
| (xs4, pats1, body4) -> begin
(

let xs5 = (FStar_All.pipe_right xs4 FStar_List.rev)
in (match ((op = "forall")) with
| true -> begin
(mk1 (FStar_Parser_AST.QForall (((xs5), (pats1), (body4)))))
end
| uu____1884 -> begin
(mk1 (FStar_Parser_AST.QExists (((xs5), (pats1), (body4)))))
end))
end))
end))))
end))
end
| uu____1888 -> begin
(match ((op = "forall")) with
| true -> begin
(

let uu____1889 = (

let uu____1890 = (

let uu____1897 = (resugar_term body)
in (([]), (([])::[]), (uu____1897)))
in FStar_Parser_AST.QForall (uu____1890))
in (mk1 uu____1889))
end
| uu____1903 -> begin
(

let uu____1904 = (

let uu____1905 = (

let uu____1912 = (resugar_term body)
in (([]), (([])::[]), (uu____1912)))
in FStar_Parser_AST.QExists (uu____1905))
in (mk1 uu____1904))
end)
end)))
in (match (((FStar_List.length args1) > (Prims.parse_int "0"))) with
| true -> begin
(

let args2 = (last1 args1)
in (match (args2) with
| ((b, uu____1935))::[] -> begin
(resugar b)
end
| uu____1948 -> begin
(failwith "wrong args format to QForall")
end))
end
| uu____1954 -> begin
(resugar_as_app e args1)
end)))
end
| FStar_Pervasives_Native.Some ("alloc", uu____1955) -> begin
(

let uu____1958 = (FStar_List.hd args1)
in (match (uu____1958) with
| (e1, uu____1968) -> begin
(resugar_term e1)
end))
end
| FStar_Pervasives_Native.Some (op, arity) -> begin
(

let op1 = (FStar_Ident.id_of_text op)
in (

let resugar = (fun args2 -> (FStar_All.pipe_right args2 (FStar_List.map (fun uu____1998 -> (match (uu____1998) with
| (e1, qual) -> begin
(resugar_term e1)
end)))))
in (match (arity) with
| _0_38 when (_0_38 = (Prims.parse_int "0")) -> begin
(

let uu____2003 = (FStar_Parser_ToDocument.handleable_args_length op1)
in (match (uu____2003) with
| _0_39 when ((_0_39 = (Prims.parse_int "1")) && ((FStar_List.length args1) > (Prims.parse_int "0"))) -> begin
(

let uu____2014 = (

let uu____2015 = (

let uu____2019 = (

let uu____2021 = (last1 args1)
in (resugar uu____2021))
in ((op1), (uu____2019)))
in FStar_Parser_AST.Op (uu____2015))
in (mk1 uu____2014))
end
| _0_40 when ((_0_40 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____2036 = (

let uu____2037 = (

let uu____2041 = (

let uu____2043 = (last_two args1)
in (resugar uu____2043))
in ((op1), (uu____2041)))
in FStar_Parser_AST.Op (uu____2037))
in (mk1 uu____2036))
end
| _0_41 when ((_0_41 = (Prims.parse_int "3")) && ((FStar_List.length args1) > (Prims.parse_int "2"))) -> begin
(

let uu____2058 = (

let uu____2059 = (

let uu____2063 = (

let uu____2065 = (last_three args1)
in (resugar uu____2065))
in ((op1), (uu____2063)))
in FStar_Parser_AST.Op (uu____2059))
in (mk1 uu____2058))
end
| uu____2070 -> begin
(resugar_as_app e args1)
end))
end
| _0_42 when ((_0_42 = (Prims.parse_int "2")) && ((FStar_List.length args1) > (Prims.parse_int "1"))) -> begin
(

let uu____2081 = (

let uu____2082 = (

let uu____2086 = (

let uu____2088 = (last_two args1)
in (resugar uu____2088))
in ((op1), (uu____2086)))
in FStar_Parser_AST.Op (uu____2082))
in (mk1 uu____2081))
end
| uu____2093 -> begin
(resugar_as_app e args1)
end)))
end)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat, uu____2096, t1))::[]) -> begin
(

let bnds = (

let uu____2146 = (

let uu____2149 = (resugar_pat pat)
in (

let uu____2150 = (resugar_term e)
in ((uu____2149), (uu____2150))))
in (uu____2146)::[])
in (

let body = (resugar_term t1)
in (mk1 (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (bnds), (body)))))))
end
| FStar_Syntax_Syntax.Tm_match (e, ((pat1, uu____2161, t1))::((pat2, uu____2164, t2))::[]) when ((is_true_pat pat1) && (is_wild_pat pat2)) -> begin
(

let uu____2231 = (

let uu____2232 = (

let uu____2236 = (resugar_term e)
in (

let uu____2237 = (resugar_term t1)
in (

let uu____2238 = (resugar_term t2)
in ((uu____2236), (uu____2237), (uu____2238)))))
in FStar_Parser_AST.If (uu____2232))
in (mk1 uu____2231))
end
| FStar_Syntax_Syntax.Tm_match (e, branches) -> begin
(

let resugar_branch = (fun uu____2276 -> (match (uu____2276) with
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

let uu____2295 = (resugar_term e1)
in FStar_Pervasives_Native.Some (uu____2295))
end)
in (

let b1 = (resugar_term b)
in ((pat1), (wopt1), (b1)))))
end))
in (

let uu____2298 = (

let uu____2299 = (

let uu____2307 = (resugar_term e)
in (

let uu____2308 = (FStar_List.map resugar_branch branches)
in ((uu____2307), (uu____2308))))
in FStar_Parser_AST.Match (uu____2299))
in (mk1 uu____2298)))
end
| FStar_Syntax_Syntax.Tm_ascribed (e, (asc, tac_opt), uu____2330) -> begin
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

let uu____2383 = (

let uu____2384 = (

let uu____2389 = (resugar_term e)
in ((uu____2389), (term), (tac_opt1)))
in FStar_Parser_AST.Ascribed (uu____2384))
in (mk1 uu____2383))))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, bnds), body) -> begin
(

let mk_pat = (fun a -> (FStar_Parser_AST.mk_pattern a t.FStar_Syntax_Syntax.pos))
in (

let uu____2407 = (FStar_Syntax_Subst.open_let_rec bnds body)
in (match (uu____2407) with
| (bnds1, body1) -> begin
(

let resugar_one_binding = (fun bnd -> (

let uu____2423 = (

let uu____2426 = (FStar_Syntax_Util.mk_conj bnd.FStar_Syntax_Syntax.lbtyp bnd.FStar_Syntax_Syntax.lbdef)
in (FStar_Syntax_Subst.open_univ_vars bnd.FStar_Syntax_Syntax.lbunivs uu____2426))
in (match (uu____2423) with
| (univs1, td) -> begin
(

let uu____2433 = (

let uu____2440 = (

let uu____2441 = (FStar_Syntax_Subst.compress td)
in uu____2441.FStar_Syntax_Syntax.n)
in (match (uu____2440) with
| FStar_Syntax_Syntax.Tm_app (uu____2450, ((t1, uu____2452))::((d, uu____2454))::[]) -> begin
((t1), (d))
end
| uu____2488 -> begin
(failwith "wrong let binding format")
end))
in (match (uu____2433) with
| (typ, def) -> begin
(

let uu____2509 = (

let uu____2513 = (

let uu____2514 = (FStar_Syntax_Subst.compress def)
in uu____2514.FStar_Syntax_Syntax.n)
in (match (uu____2513) with
| FStar_Syntax_Syntax.Tm_abs (b, t1, uu____2522) -> begin
(

let uu____2535 = (FStar_Syntax_Subst.open_term b t1)
in (match (uu____2535) with
| (b1, t2) -> begin
(

let b2 = (

let uu____2544 = (FStar_Options.print_implicits ())
in (match (uu____2544) with
| true -> begin
b1
end
| uu____2545 -> begin
(filter_imp b1)
end))
in ((b2), (t2), (true)))
end))
end
| uu____2546 -> begin
(([]), (def), (false))
end))
in (match (uu____2509) with
| (binders, term, is_pat_app) -> begin
(

let uu____2561 = (match (bnd.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inr (fv) -> begin
(((mk_pat (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (term))
end
| FStar_Util.Inl (bv) -> begin
(

let uu____2568 = (

let uu____2569 = (

let uu____2570 = (

let uu____2574 = (bv_as_unique_ident bv)
in ((uu____2574), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2570))
in (mk_pat uu____2569))
in ((uu____2568), (term)))
end)
in (match (uu____2561) with
| (pat, term1) -> begin
(match (is_pat_app) with
| true -> begin
(

let args = (FStar_All.pipe_right binders (FStar_List.map (fun uu____2595 -> (match (uu____2595) with
| (bv, uu____2599) -> begin
(

let uu____2600 = (

let uu____2601 = (

let uu____2605 = (bv_as_unique_ident bv)
in ((uu____2605), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2601))
in (mk_pat uu____2600))
end))))
in (

let uu____2607 = (

let uu____2610 = (resugar_term term1)
in (((mk_pat (FStar_Parser_AST.PatApp (((pat), (args)))))), (uu____2610)))
in (

let uu____2612 = (universe_to_string univs1)
in ((uu____2607), (uu____2612)))))
end
| uu____2615 -> begin
(

let uu____2616 = (

let uu____2619 = (resugar_term term1)
in ((pat), (uu____2619)))
in (

let uu____2620 = (universe_to_string univs1)
in ((uu____2616), (uu____2620))))
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

let uu____2646 = (

let uu____2647 = (FStar_Options.print_universes ())
in (not (uu____2647)))
in (Obj.magic ((match (uu____2646) with
| true -> begin
FStar_Pervasives_Native.fst
end
| uu____2658 -> begin
(fun uu___193_2659 -> (match (uu___193_2659) with
| ((pat, body2), univs1) -> begin
(

let uu____2671 = (match ((univs1 = "")) with
| true -> begin
body2
end
| uu____2672 -> begin
(mk1 (FStar_Parser_AST.Labeled (((body2), (univs1), (true)))))
end)
in ((pat), (uu____2671)))
end))
end))))
in (FStar_List.map f r))
in (

let body2 = (resugar_term body1)
in (mk1 (FStar_Parser_AST.Let ((((match (is_rec) with
| true -> begin
FStar_Parser_AST.Rec
end
| uu____2683 -> begin
FStar_Parser_AST.NoLetQualifier
end)), (bnds2), (body2)))))))))
end)))
end
| FStar_Syntax_Syntax.Tm_uvar (u, uu____2685) -> begin
(

let s = (

let uu____2703 = (

let uu____2704 = (FStar_Syntax_Unionfind.uvar_id u)
in (FStar_All.pipe_right uu____2704 FStar_Util.string_of_int))
in (Prims.strcat "uu___unification_ " uu____2703))
in (

let uu____2705 = (var s t.FStar_Syntax_Syntax.pos)
in (mk1 uu____2705)))
end
| FStar_Syntax_Syntax.Tm_meta (e, m) -> begin
(

let resugar_meta_desugared = (fun uu___194_2715 -> (match (uu___194_2715) with
| FStar_Syntax_Syntax.Data_app -> begin
(

let rec head_fv_universes_args = (fun h -> (

let uu____2729 = (

let uu____2730 = (FStar_Syntax_Subst.compress h)
in uu____2730.FStar_Syntax_Syntax.n)
in (match (uu____2729) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____2743 = (FStar_Syntax_Syntax.lid_of_fv fv)
in ((uu____2743), ([]), ([])))
end
| FStar_Syntax_Syntax.Tm_uinst (h1, u) -> begin
(

let uu____2760 = (head_fv_universes_args h1)
in (match (uu____2760) with
| (h2, uvs, args) -> begin
((h2), ((FStar_List.append uvs u)), (args))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let uu____2816 = (head_fv_universes_args head1)
in (match (uu____2816) with
| (h1, uvs, args') -> begin
((h1), (uvs), ((FStar_List.append args' args)))
end))
end
| uu____2860 -> begin
(

let uu____2861 = (

let uu____2862 = (

let uu____2863 = (

let uu____2864 = (resugar_term h)
in (parser_term_to_string uu____2864))
in (FStar_Util.format1 "Not an application or a fv %s" uu____2863))
in FStar_Errors.Err (uu____2862))
in (FStar_Pervasives.raise uu____2861))
end)))
in (

let uu____2874 = try
(match (()) with
| () -> begin
(

let uu____2905 = (FStar_Syntax_Util.unmeta e)
in (head_fv_universes_args uu____2905))
end)
with
| FStar_Errors.Err (uu____2919) -> begin
(

let uu____2920 = (

let uu____2921 = (

let uu____2924 = (

let uu____2925 = (

let uu____2926 = (resugar_term e)
in (parser_term_to_string uu____2926))
in (FStar_Util.format1 "wrong Data_app head format %s" uu____2925))
in ((uu____2924), (e.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____2921))
in (FStar_Pervasives.raise uu____2920))
end
in (match (uu____2874) with
| (head1, universes, args) -> begin
(

let universes1 = (FStar_List.map (fun u -> (

let uu____2960 = (resugar_universe u t.FStar_Syntax_Syntax.pos)
in ((uu____2960), (FStar_Parser_AST.UnivApp)))) universes)
in (

let args1 = (FStar_List.map (fun uu____2975 -> (match (uu____2975) with
| (t1, q) -> begin
(

let uu____2985 = (resugar_term t1)
in (

let uu____2986 = (resugar_imp q)
in ((uu____2985), (uu____2986))))
end)) args)
in (

let args2 = (

let uu____2991 = ((FStar_Parser_Const.is_tuple_data_lid' head1) || (

let uu____2993 = (FStar_Options.print_universes ())
in (not (uu____2993))))
in (match (uu____2991) with
| true -> begin
args1
end
| uu____2997 -> begin
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
| FStar_Parser_AST.Let (uu____3008, ((p, t11))::[], t2) -> begin
(mk1 (FStar_Parser_AST.Seq (((t11), (t2)))))
end
| FStar_Parser_AST.Ascribed (t11, t2, t3) -> begin
(

let uu____3024 = (

let uu____3025 = (

let uu____3030 = (resugar_seq t11)
in ((uu____3030), (t2), (t3)))
in FStar_Parser_AST.Ascribed (uu____3025))
in (mk1 uu____3024))
end
| uu____3032 -> begin
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
| uu____3045 -> begin
(failwith "mutable_alloc should have let term with no qualifier")
end))
end
| FStar_Syntax_Syntax.Mutable_rval -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____3047 = (

let uu____3048 = (FStar_Syntax_Subst.compress e)
in uu____3048.FStar_Syntax_Syntax.n)
in (match (uu____3047) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv1); FStar_Syntax_Syntax.tk = uu____3052; FStar_Syntax_Syntax.pos = uu____3053; FStar_Syntax_Syntax.vars = uu____3054}, ((term, uu____3056))::[]) -> begin
(resugar_term term)
end
| uu____3078 -> begin
(failwith "mutable_rval should have app term")
end)))
end))
in (match (m) with
| FStar_Syntax_Syntax.Meta_pattern (pats) -> begin
(

let pats1 = (FStar_All.pipe_right (FStar_List.flatten pats) (FStar_List.map (fun uu____3103 -> (match (uu____3103) with
| (x, uu____3107) -> begin
(resugar_term x)
end))))
in (mk1 (FStar_Parser_AST.Attributes (pats1))))
end
| FStar_Syntax_Syntax.Meta_labeled (l, uu____3109, p) -> begin
(

let uu____3111 = (

let uu____3112 = (

let uu____3116 = (resugar_term e)
in ((uu____3116), (l), (p)))
in FStar_Parser_AST.Labeled (uu____3112))
in (mk1 uu____3111))
end
| FStar_Syntax_Syntax.Meta_desugared (i) -> begin
(resugar_meta_desugared i)
end
| FStar_Syntax_Syntax.Meta_alien (uu____3118, s) -> begin
(resugar_term e)
end
| FStar_Syntax_Syntax.Meta_named (t1) -> begin
(mk1 (FStar_Parser_AST.Name (t1)))
end
| FStar_Syntax_Syntax.Meta_monadic (name1, t1) -> begin
(

let uu____3127 = (

let uu____3128 = (

let uu____3133 = (resugar_term e)
in (

let uu____3134 = (

let uu____3135 = (

let uu____3136 = (

let uu____3142 = (

let uu____3146 = (

let uu____3149 = (resugar_term t1)
in ((uu____3149), (FStar_Parser_AST.Nothing)))
in (uu____3146)::[])
in ((name1), (uu____3142)))
in FStar_Parser_AST.Construct (uu____3136))
in (mk1 uu____3135))
in ((uu____3133), (uu____3134), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____3128))
in (mk1 uu____3127))
end
| FStar_Syntax_Syntax.Meta_monadic_lift (name1, uu____3159, t1) -> begin
(

let uu____3165 = (

let uu____3166 = (

let uu____3171 = (resugar_term e)
in (

let uu____3172 = (

let uu____3173 = (

let uu____3174 = (

let uu____3180 = (

let uu____3184 = (

let uu____3187 = (resugar_term t1)
in ((uu____3187), (FStar_Parser_AST.Nothing)))
in (uu____3184)::[])
in ((name1), (uu____3180)))
in FStar_Parser_AST.Construct (uu____3174))
in (mk1 uu____3173))
in ((uu____3171), (uu____3172), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____3166))
in (mk1 uu____3165))
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

let uu____3218 = (FStar_Options.print_universes ())
in (match (uu____3218) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_Tot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____3229 -> begin
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

let uu____3254 = (FStar_Options.print_universes ())
in (match (uu____3254) with
| true -> begin
(

let u2 = (resugar_universe u1 c.FStar_Syntax_Syntax.pos)
in (mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((u2), (FStar_Parser_AST.UnivApp)))::(((t), (FStar_Parser_AST.Nothing)))::[]))))))
end
| uu____3265 -> begin
(mk1 (FStar_Parser_AST.Construct (((FStar_Parser_Const.effect_GTot_lid), ((((t), (FStar_Parser_AST.Nothing)))::[])))))
end))
end))
end
| FStar_Syntax_Syntax.Comp (c1) -> begin
(

let result = (

let uu____3277 = (resugar_term c1.FStar_Syntax_Syntax.result_typ)
in ((uu____3277), (FStar_Parser_AST.Nothing)))
in (

let uu____3278 = (FStar_Options.print_effect_args ())
in (match (uu____3278) with
| true -> begin
(

let universe = (FStar_List.map (fun u -> (resugar_universe u)) c1.FStar_Syntax_Syntax.comp_univs)
in (

let args = (match ((FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(

let rec aux = (fun l uu___195_3319 -> (match (uu___195_3319) with
| [] -> begin
l
end
| ((t, aq))::tl1 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid) -> begin
(aux l tl1)
end
| FStar_Syntax_Syntax.Tm_meta (uu____3361) -> begin
(aux l tl1)
end
| uu____3366 -> begin
(aux ((((t), (aq)))::l) tl1)
end)
end))
in (aux [] c1.FStar_Syntax_Syntax.effect_args))
end
| uu____3377 -> begin
c1.FStar_Syntax_Syntax.effect_args
end)
in (

let args1 = (FStar_List.map (fun uu____3390 -> (match (uu____3390) with
| (e, uu____3396) -> begin
(

let uu____3397 = (resugar_term e)
in ((uu____3397), (FStar_Parser_AST.Nothing)))
end)) args)
in (

let rec aux = (fun l uu___196_3411 -> (match (uu___196_3411) with
| [] -> begin
l
end
| (hd1)::tl1 -> begin
(match (hd1) with
| FStar_Syntax_Syntax.DECREASES (e) -> begin
(

let e1 = (

let uu____3431 = (resugar_term e)
in ((uu____3431), (FStar_Parser_AST.Nothing)))
in (aux ((e1)::l) tl1))
end
| uu____3434 -> begin
(aux l tl1)
end)
end))
in (

let decrease = (aux [] c1.FStar_Syntax_Syntax.flags)
in (mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((FStar_List.append ((result)::decrease) args1)))))))))))
end
| uu____3448 -> begin
(mk1 (FStar_Parser_AST.Construct (((c1.FStar_Syntax_Syntax.effect_name), ((result)::[])))))
end)))
end)))
and resugar_binder : FStar_Syntax_Syntax.binder  ->  FStar_Range.range  ->  FStar_Parser_AST.binder FStar_Pervasives_Native.option = (fun b r -> (

let uu____3459 = b
in (match (uu____3459) with
| (x, aq) -> begin
(

let uu____3463 = (resugar_arg_qual aq)
in (FStar_Util.map_opt uu____3463 (fun imp -> (

let e = (resugar_term x.FStar_Syntax_Syntax.sort)
in (match (e.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(

let uu____3473 = (

let uu____3474 = (bv_as_unique_ident x)
in FStar_Parser_AST.Variable (uu____3474))
in (FStar_Parser_AST.mk_binder uu____3473 r FStar_Parser_AST.Type_level imp))
end
| uu____3475 -> begin
(

let uu____3476 = (FStar_Syntax_Syntax.is_null_bv x)
in (match (uu____3476) with
| true -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (e)) r FStar_Parser_AST.Type_level imp)
end
| uu____3477 -> begin
(

let uu____3478 = (

let uu____3479 = (

let uu____3482 = (bv_as_unique_ident x)
in ((uu____3482), (e)))
in FStar_Parser_AST.Annotated (uu____3479))
in (FStar_Parser_AST.mk_binder uu____3478 r FStar_Parser_AST.Type_level imp))
end))
end)))))
end)))
and resugar_bv_as_pat : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.aqual  ->  FStar_Parser_AST.pattern FStar_Pervasives_Native.option = (fun x qual -> (

let mk1 = (fun a -> (

let uu____3490 = (FStar_Syntax_Syntax.range_of_bv x)
in (FStar_Parser_AST.mk_pattern a uu____3490)))
in (

let uu____3491 = (

let uu____3492 = (FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort)
in uu____3492.FStar_Syntax_Syntax.n)
in (match (uu____3491) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let i = (FStar_String.compare x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText FStar_Ident.reserved_prefix)
in (match ((i = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3498 = (mk1 FStar_Parser_AST.PatWild)
in FStar_Pervasives_Native.Some (uu____3498))
end
| uu____3499 -> begin
(

let uu____3500 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____3500 (fun aq -> (

let uu____3508 = (

let uu____3509 = (

let uu____3510 = (

let uu____3514 = (bv_as_unique_ident x)
in ((uu____3514), (aq)))
in FStar_Parser_AST.PatVar (uu____3510))
in (mk1 uu____3509))
in FStar_Pervasives_Native.Some (uu____3508)))))
end))
end
| uu____3516 -> begin
(

let uu____3517 = (resugar_arg_qual qual)
in (FStar_Util.bind_opt uu____3517 (fun aq -> (

let pat = (

let uu____3528 = (

let uu____3529 = (

let uu____3533 = (bv_as_unique_ident x)
in ((uu____3533), (aq)))
in FStar_Parser_AST.PatVar (uu____3529))
in (mk1 uu____3528))
in (

let uu____3535 = (FStar_Options.print_bound_var_types ())
in (match (uu____3535) with
| true -> begin
(

let uu____3537 = (

let uu____3538 = (

let uu____3539 = (

let uu____3542 = (resugar_term x.FStar_Syntax_Syntax.sort)
in ((pat), (uu____3542)))
in FStar_Parser_AST.PatAscribed (uu____3539))
in (mk1 uu____3538))
in FStar_Pervasives_Native.Some (uu____3537))
end
| uu____3543 -> begin
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
| uu____3559 -> begin
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

let args1 = (FStar_List.map (fun uu____3595 -> (match (uu____3595) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatList (args1))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) when ((FStar_Parser_Const.is_tuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v) || (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) -> begin
(

let args1 = (FStar_List.map (fun uu____3617 -> (match (uu____3617) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (

let uu____3622 = (FStar_Parser_Const.is_dtuple_data_lid' fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____3622) with
| true -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (true)))))
end
| uu____3624 -> begin
(mk1 (FStar_Parser_AST.PatTuple (((args1), (false)))))
end)))
end
| FStar_Syntax_Syntax.Pat_cons ({FStar_Syntax_Syntax.fv_name = uu____3626; FStar_Syntax_Syntax.fv_delta = uu____3627; FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (name, fields))}, args) -> begin
(

let fields1 = (

let uu____3643 = (FStar_All.pipe_right fields (FStar_List.map (fun f -> (FStar_Ident.lid_of_ids ((f)::[])))))
in (FStar_All.pipe_right uu____3643 FStar_List.rev))
in (

let args1 = (

let uu____3653 = (FStar_All.pipe_right args (FStar_List.map (fun uu____3665 -> (match (uu____3665) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end))))
in (FStar_All.pipe_right uu____3653 FStar_List.rev))
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

let uu____3707 = (map21 tl1 [])
in (((hd1), ((mk1 FStar_Parser_AST.PatWild))))::uu____3707)
end
| ((hd1)::tl1, (hd2)::tl2) -> begin
(

let uu____3721 = (map21 tl1 tl2)
in (((hd1), (hd2)))::uu____3721)
end))
in (

let args2 = (

let uu____3731 = (map21 fields1 args1)
in (FStar_All.pipe_right uu____3731 FStar_List.rev))
in (mk1 (FStar_Parser_AST.PatRecord (args2)))))))
end
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(

let args1 = (FStar_List.map (fun uu____3760 -> (match (uu____3760) with
| (p2, b) -> begin
(aux p2 (FStar_Pervasives_Native.Some (b)))
end)) args)
in (mk1 (FStar_Parser_AST.PatApp ((((mk1 (FStar_Parser_AST.PatName (fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))), (args1))))))
end
| FStar_Syntax_Syntax.Pat_var (v1) -> begin
(

let uu____3767 = (string_to_op v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____3767) with
| FStar_Pervasives_Native.Some (op, uu____3772) -> begin
(mk1 (FStar_Parser_AST.PatOp ((FStar_Ident.mk_ident ((op), (v1.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3777 = (

let uu____3778 = (

let uu____3782 = (bv_as_unique_ident v1)
in (

let uu____3783 = (to_arg_qual imp_opt)
in ((uu____3782), (uu____3783))))
in FStar_Parser_AST.PatVar (uu____3778))
in (mk1 uu____3777))
end))
end
| FStar_Syntax_Syntax.Pat_wild (uu____3786) -> begin
(mk1 FStar_Parser_AST.PatWild)
end
| FStar_Syntax_Syntax.Pat_dot_term (bv, term) -> begin
(

let pat = (

let uu____3794 = (

let uu____3795 = (

let uu____3799 = (bv_as_unique_ident bv)
in ((uu____3799), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))
in FStar_Parser_AST.PatVar (uu____3795))
in (mk1 uu____3794))
in (

let uu____3801 = (FStar_Options.print_bound_var_types ())
in (match (uu____3801) with
| true -> begin
(

let uu____3802 = (

let uu____3803 = (

let uu____3806 = (resugar_term term)
in ((pat), (uu____3806)))
in FStar_Parser_AST.PatAscribed (uu____3803))
in (mk1 uu____3802))
end
| uu____3807 -> begin
pat
end)))
end))
in (aux p FStar_Pervasives_Native.None)))))


let resugar_qualifier : FStar_Syntax_Syntax.qualifier  ->  FStar_Parser_AST.qualifier FStar_Pervasives_Native.option = (fun uu___197_3812 -> (match (uu___197_3812) with
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
| uu____3815 -> begin
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
| uu____3817 -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Logic)
end)
end
| FStar_Syntax_Syntax.Reifiable -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reifiable)
end
| FStar_Syntax_Syntax.Reflectable (uu____3818) -> begin
FStar_Pervasives_Native.Some (FStar_Parser_AST.Reflectable)
end
| FStar_Syntax_Syntax.Discriminator (uu____3819) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Projector (uu____3820) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordType (uu____3823) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.RecordConstructor (uu____3828) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Action (uu____3833) -> begin
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


let resugar_pragma : FStar_Syntax_Syntax.pragma  ->  FStar_Parser_AST.pragma = (fun uu___198_3837 -> (match (uu___198_3837) with
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
| FStar_Syntax_Syntax.Sig_inductive_typ (tylid, uvs, bs, t, uu____3859, datacons) -> begin
(

let uu____3865 = (FStar_All.pipe_right datacon_ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3883, uu____3884, uu____3885, inductive_lid, uu____3887, uu____3888) -> begin
(FStar_Ident.lid_equals inductive_lid tylid)
end
| uu____3891 -> begin
(failwith "unexpected")
end))))
in (match (uu____3865) with
| (current_datacons, other_datacons) -> begin
(

let bs1 = (

let uu____3903 = (FStar_Options.print_implicits ())
in (match (uu____3903) with
| true -> begin
bs
end
| uu____3904 -> begin
(filter_imp bs)
end))
in (

let bs2 = (FStar_All.pipe_right bs1 (map_opt (fun b -> (resugar_binder b t.FStar_Syntax_Syntax.pos))))
in (

let tyc = (

let uu____3911 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___199_3915 -> (match (uu___199_3915) with
| FStar_Syntax_Syntax.RecordType (uu____3916) -> begin
true
end
| uu____3921 -> begin
false
end))))
in (match (uu____3911) with
| true -> begin
(

let resugar_datacon_as_fields = (fun fields se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (uu____3949, univs1, term, uu____3952, num, uu____3954) -> begin
(

let uu____3957 = (

let uu____3958 = (FStar_Syntax_Subst.compress term)
in uu____3958.FStar_Syntax_Syntax.n)
in (match (uu____3957) with
| FStar_Syntax_Syntax.Tm_arrow (bs3, uu____3967) -> begin
(

let mfields = (FStar_All.pipe_right bs3 (FStar_List.map (fun uu____4003 -> (match (uu____4003) with
| (b, qual) -> begin
(

let uu____4012 = (

let uu____4013 = (bv_as_unique_ident b)
in (FStar_Syntax_Util.unmangle_field_name uu____4013))
in (

let uu____4014 = (resugar_term b.FStar_Syntax_Syntax.sort)
in ((uu____4012), (uu____4014), (FStar_Pervasives_Native.None))))
end))))
in (FStar_List.append mfields fields))
end
| uu____4020 -> begin
(failwith "unexpected")
end))
end
| uu____4026 -> begin
(failwith "unexpected")
end))
in (

let fields = (FStar_List.fold_left resugar_datacon_as_fields [] current_datacons)
in FStar_Parser_AST.TyconRecord (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (fields)))))
end
| uu____4054 -> begin
(

let resugar_datacon = (fun constructors se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, univs1, term, uu____4093, num, uu____4095) -> begin
(

let c = (

let uu____4105 = (

let uu____4107 = (resugar_term term)
in FStar_Pervasives_Native.Some (uu____4107))
in ((l.FStar_Ident.ident), (uu____4105), (FStar_Pervasives_Native.None), (false)))
in (c)::constructors)
end
| uu____4116 -> begin
(failwith "unexpected")
end))
in (

let constructors = (FStar_List.fold_left resugar_datacon [] current_datacons)
in FStar_Parser_AST.TyconVariant (((tylid.FStar_Ident.ident), (bs2), (FStar_Pervasives_Native.None), (constructors)))))
end))
in ((other_datacons), (tyc)))))
end))
end
| uu____4155 -> begin
(failwith "Impossible : only Sig_inductive_typ can be resugared as types")
end))


let mk_decl : FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun r q d' -> (

let uu____4172 = (FStar_List.choose resugar_qualifier q)
in {FStar_Parser_AST.d = d'; FStar_Parser_AST.drange = r; FStar_Parser_AST.doc = FStar_Pervasives_Native.None; FStar_Parser_AST.quals = uu____4172; FStar_Parser_AST.attrs = []}))


let decl'_to_decl : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl'  ->  FStar_Parser_AST.decl = (fun se d' -> (mk_decl se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals d'))


let resugar_tscheme' : Prims.string  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun name ts -> (

let uu____4189 = ts
in (match (uu____4189) with
| (univs1, typ) -> begin
(

let name1 = (FStar_Ident.mk_ident ((name), (typ.FStar_Syntax_Syntax.pos)))
in (

let uu____4195 = (

let uu____4196 = (

let uu____4203 = (

let uu____4208 = (

let uu____4212 = (

let uu____4213 = (

let uu____4220 = (resugar_term typ)
in ((name1), ([]), (FStar_Pervasives_Native.None), (uu____4220)))
in FStar_Parser_AST.TyconAbbrev (uu____4213))
in ((uu____4212), (FStar_Pervasives_Native.None)))
in (uu____4208)::[])
in ((false), (uu____4203)))
in FStar_Parser_AST.Tycon (uu____4196))
in (mk_decl typ.FStar_Syntax_Syntax.pos [] uu____4195)))
end)))


let resugar_tscheme : FStar_Syntax_Syntax.tscheme  ->  FStar_Parser_AST.decl = (fun ts -> (resugar_tscheme' "tsheme" ts))


let resugar_eff_decl : Prims.bool  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Parser_AST.decl = (fun for_free r q ed -> (

let resugar_action = (fun d for_free1 -> (

let action_params = (FStar_Syntax_Subst.open_binders d.FStar_Syntax_Syntax.action_params)
in (

let uu____4264 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_defn)
in (match (uu____4264) with
| (bs, action_defn) -> begin
(

let uu____4269 = (FStar_Syntax_Subst.open_term action_params d.FStar_Syntax_Syntax.action_typ)
in (match (uu____4269) with
| (bs1, action_typ) -> begin
(

let action_params1 = (

let uu____4275 = (FStar_Options.print_implicits ())
in (match (uu____4275) with
| true -> begin
action_params
end
| uu____4276 -> begin
(filter_imp action_params)
end))
in (

let action_params2 = (

let uu____4279 = (FStar_All.pipe_right action_params1 (map_opt (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____4279 FStar_List.rev))
in (

let action_defn1 = (resugar_term action_defn)
in (

let action_typ1 = (resugar_term action_typ)
in (match (for_free1) with
| true -> begin
(

let a = (

let uu____4289 = (

let uu____4295 = (FStar_Ident.lid_of_str "construct")
in ((uu____4295), ((((action_defn1), (FStar_Parser_AST.Nothing)))::(((action_typ1), (FStar_Parser_AST.Nothing)))::[])))
in FStar_Parser_AST.Construct (uu____4289))
in (

let t = (FStar_Parser_AST.mk_term a r FStar_Parser_AST.Un)
in (mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (t)))), (FStar_Pervasives_Native.None)))::[])))))))
end
| uu____4319 -> begin
(mk_decl r q (FStar_Parser_AST.Tycon (((false), ((((FStar_Parser_AST.TyconAbbrev (((d.FStar_Syntax_Syntax.action_name.FStar_Ident.ident), (action_params2), (FStar_Pervasives_Native.None), (action_defn1)))), (FStar_Pervasives_Native.None)))::[])))))
end)))))
end))
end))))
in (

let eff_name = ed.FStar_Syntax_Syntax.mname.FStar_Ident.ident
in (

let uu____4334 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature)
in (match (uu____4334) with
| (eff_binders, eff_typ) -> begin
(

let eff_binders1 = (

let uu____4340 = (FStar_Options.print_implicits ())
in (match (uu____4340) with
| true -> begin
eff_binders
end
| uu____4341 -> begin
(filter_imp eff_binders)
end))
in (

let eff_binders2 = (

let uu____4344 = (FStar_All.pipe_right eff_binders1 (map_opt (fun b -> (resugar_binder b r))))
in (FStar_All.pipe_right uu____4344 FStar_List.rev))
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
| uu____4369 -> begin
(repr)::(return_repr)::(bind_repr)::(ret_wp)::(bind_wp)::(if_then_else1)::(ite_wp)::(stronger)::(close_wp)::(assert_p)::(assume_p)::(null_wp)::(trivial)::[]
end)
in (

let actions = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.map (fun a -> (resugar_action a false))))
in (

let decls = (FStar_List.append mandatory_members_decls actions)
in (mk_decl r q (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (((eff_name), (eff_binders2), (eff_typ1), (decls)))))))))))))))))))))))))
end)))))


let resugar_sigelt : FStar_Syntax_Syntax.sigelt  ->  FStar_Parser_AST.decl FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____4387) -> begin
(

let uu____4392 = (FStar_All.pipe_right ses (FStar_List.partition (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4405) -> begin
true
end
| FStar_Syntax_Syntax.Sig_declare_typ (uu____4414) -> begin
true
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4418) -> begin
false
end
| uu____4426 -> begin
(failwith "Found a sigelt which is neither a type declaration or a data constructor in a sigelt")
end))))
in (match (uu____4392) with
| (decl_typ_ses, datacon_ses) -> begin
(

let retrieve_datacons_and_resugar = (fun uu____4446 se1 -> (match (uu____4446) with
| (datacon_ses1, tycons) -> begin
(

let uu____4461 = (resugar_typ datacon_ses1 se1)
in (match (uu____4461) with
| (datacon_ses2, tyc) -> begin
((datacon_ses2), ((tyc)::tycons))
end))
end))
in (

let uu____4470 = (FStar_List.fold_left retrieve_datacons_and_resugar ((datacon_ses), ([])) decl_typ_ses)
in (match (uu____4470) with
| (leftover_datacons, tycons) -> begin
(match (leftover_datacons) with
| [] -> begin
(

let uu____4489 = (

let uu____4490 = (

let uu____4491 = (

let uu____4498 = (FStar_List.map (fun tyc -> ((tyc), (FStar_Pervasives_Native.None))) tycons)
in ((false), (uu____4498)))
in FStar_Parser_AST.Tycon (uu____4491))
in (decl'_to_decl se uu____4490))
in FStar_Pervasives_Native.Some (uu____4489))
end
| (se1)::[] -> begin
(match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (l, uu____4516, uu____4517, uu____4518, uu____4519, uu____4520) -> begin
(

let uu____4523 = (decl'_to_decl se1 (FStar_Parser_AST.Exception (((l.FStar_Ident.ident), (FStar_Pervasives_Native.None)))))
in FStar_Pervasives_Native.Some (uu____4523))
end
| uu____4525 -> begin
(failwith "wrong format for resguar to Exception")
end)
end
| uu____4527 -> begin
(failwith "Should not happen hopefully")
end)
end)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____4531) -> begin
(

let uu____4534 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___200_4539 -> (match (uu___200_4539) with
| FStar_Syntax_Syntax.Projector (uu____4540, uu____4541) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4542) -> begin
true
end
| uu____4543 -> begin
false
end))))
in (match (uu____4534) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4545 -> begin
(

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
in (

let dummy = (mk1 FStar_Syntax_Syntax.Tm_unknown)
in (

let desugared_let = (mk1 (FStar_Syntax_Syntax.Tm_let (((lbs), (dummy)))))
in (

let t = (resugar_term desugared_let)
in (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Let (isrec, lets, uu____4568) -> begin
(

let uu____4575 = (decl'_to_decl se (FStar_Parser_AST.TopLevelLet (((isrec), (lets)))))
in FStar_Pervasives_Native.Some (uu____4575))
end
| uu____4579 -> begin
(failwith "Should not happen hopefully")
end)))))
end))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____4582, fml) -> begin
(

let uu____4584 = (

let uu____4585 = (

let uu____4586 = (

let uu____4589 = (resugar_term fml)
in ((lid.FStar_Ident.ident), (uu____4589)))
in FStar_Parser_AST.Assume (uu____4586))
in (decl'_to_decl se uu____4585))
in FStar_Pervasives_Native.Some (uu____4584))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____4591 = (resugar_eff_decl false se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____4591))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let uu____4593 = (resugar_eff_decl true se.FStar_Syntax_Syntax.sigrng se.FStar_Syntax_Syntax.sigquals ed)
in FStar_Pervasives_Native.Some (uu____4593))
end
| FStar_Syntax_Syntax.Sig_sub_effect (e) -> begin
(

let src = e.FStar_Syntax_Syntax.source
in (

let dst = e.FStar_Syntax_Syntax.target
in (

let lift_wp = (match (e.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (uu____4600, t) -> begin
(

let uu____4607 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____4607))
end
| uu____4608 -> begin
FStar_Pervasives_Native.None
end)
in (

let lift = (match (e.FStar_Syntax_Syntax.lift) with
| FStar_Pervasives_Native.Some (uu____4613, t) -> begin
(

let uu____4620 = (resugar_term t)
in FStar_Pervasives_Native.Some (uu____4620))
end
| uu____4621 -> begin
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
| uu____4636 -> begin
(failwith "Should not happen hopefully")
end)
in (

let uu____4641 = (decl'_to_decl se (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = src; FStar_Parser_AST.mdest = dst; FStar_Parser_AST.lift_op = op})))
in FStar_Pervasives_Native.Some (uu____4641)))))))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, vs, bs, c, flags) -> begin
(

let uu____4649 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____4649) with
| (bs1, c1) -> begin
(

let bs2 = (

let uu____4656 = (FStar_Options.print_implicits ())
in (match (uu____4656) with
| true -> begin
bs1
end
| uu____4657 -> begin
(filter_imp bs1)
end))
in (

let bs3 = (FStar_All.pipe_right bs2 (map_opt (fun b -> (resugar_binder b se.FStar_Syntax_Syntax.sigrng))))
in (

let uu____4663 = (

let uu____4664 = (

let uu____4665 = (

let uu____4672 = (

let uu____4677 = (

let uu____4681 = (

let uu____4682 = (

let uu____4689 = (resugar_comp c1)
in ((lid.FStar_Ident.ident), (bs3), (FStar_Pervasives_Native.None), (uu____4689)))
in FStar_Parser_AST.TyconAbbrev (uu____4682))
in ((uu____4681), (FStar_Pervasives_Native.None)))
in (uu____4677)::[])
in ((false), (uu____4672)))
in FStar_Parser_AST.Tycon (uu____4665))
in (decl'_to_decl se uu____4664))
in FStar_Pervasives_Native.Some (uu____4663))))
end))
end
| FStar_Syntax_Syntax.Sig_pragma (p) -> begin
(

let uu____4704 = (decl'_to_decl se (FStar_Parser_AST.Pragma ((resugar_pragma p))))
in FStar_Pervasives_Native.Some (uu____4704))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uvs, t) -> begin
(

let uu____4708 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___201_4713 -> (match (uu___201_4713) with
| FStar_Syntax_Syntax.Projector (uu____4714, uu____4715) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____4716) -> begin
true
end
| uu____4717 -> begin
false
end))))
in (match (uu____4708) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____4719 -> begin
(

let t' = (

let uu____4721 = ((

let uu____4724 = (FStar_Options.print_universes ())
in (not (uu____4724))) || (FStar_List.isEmpty uvs))
in (match (uu____4721) with
| true -> begin
(resugar_term t)
end
| uu____4725 -> begin
(

let uu____4726 = (FStar_Syntax_Subst.open_univ_vars uvs t)
in (match (uu____4726) with
| (uvs1, t1) -> begin
(

let universes = (universe_to_string uvs1)
in (

let uu____4732 = (

let uu____4733 = (

let uu____4737 = (resugar_term t1)
in ((uu____4737), (universes), (true)))
in FStar_Parser_AST.Labeled (uu____4733))
in (FStar_Parser_AST.mk_term uu____4732 t1.FStar_Syntax_Syntax.pos FStar_Parser_AST.Un)))
end))
end))
in (

let uu____4738 = (decl'_to_decl se (FStar_Parser_AST.Val (((lid.FStar_Ident.ident), (t')))))
in FStar_Pervasives_Native.Some (uu____4738)))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____4739) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_datacon (uu____4748) -> begin
FStar_Pervasives_Native.None
end
| FStar_Syntax_Syntax.Sig_main (uu____4756) -> begin
FStar_Pervasives_Native.None
end))





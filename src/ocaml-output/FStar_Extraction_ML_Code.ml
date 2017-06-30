
open Prims
open FStar_Pervasives
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc


let uu___is_ILeft : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ILeft -> begin
true
end
| uu____4 -> begin
false
end))


let uu___is_IRight : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IRight -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_Left : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Right : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____16 -> begin
false
end))


let uu___is_NonAssoc : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____20 -> begin
false
end))

type fixity =
| Prefix
| Postfix
| Infix of assoc


let uu___is_Prefix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Prefix -> begin
true
end
| uu____28 -> begin
false
end))


let uu___is_Postfix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Postfix -> begin
true
end
| uu____32 -> begin
false
end))


let uu___is_Infix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
true
end
| uu____37 -> begin
false
end))


let __proj__Infix__item___0 : fixity  ->  assoc = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
_0
end))


type opprec =
(Prims.int * fixity)


type level =
(opprec * assoc)


let t_prio_fun : (Prims.int * fixity) = (((Prims.parse_int "10")), (Infix (Right)))


let t_prio_tpl : (Prims.int * fixity) = (((Prims.parse_int "20")), (Infix (NonAssoc)))


let t_prio_name : (Prims.int * fixity) = (((Prims.parse_int "30")), (Postfix))


let e_bin_prio_lambda : (Prims.int * fixity) = (((Prims.parse_int "5")), (Prefix))


let e_bin_prio_if : (Prims.int * fixity) = (((Prims.parse_int "15")), (Prefix))


let e_bin_prio_letin : (Prims.int * fixity) = (((Prims.parse_int "19")), (Prefix))


let e_bin_prio_or : (Prims.int * fixity) = (((Prims.parse_int "20")), (Infix (Left)))


let e_bin_prio_and : (Prims.int * fixity) = (((Prims.parse_int "25")), (Infix (Left)))


let e_bin_prio_eq : (Prims.int * fixity) = (((Prims.parse_int "27")), (Infix (NonAssoc)))


let e_bin_prio_order : (Prims.int * fixity) = (((Prims.parse_int "29")), (Infix (NonAssoc)))


let e_bin_prio_op1 : (Prims.int * fixity) = (((Prims.parse_int "30")), (Infix (Left)))


let e_bin_prio_op2 : (Prims.int * fixity) = (((Prims.parse_int "40")), (Infix (Left)))


let e_bin_prio_op3 : (Prims.int * fixity) = (((Prims.parse_int "50")), (Infix (Left)))


let e_bin_prio_op4 : (Prims.int * fixity) = (((Prims.parse_int "60")), (Infix (Left)))


let e_bin_prio_comb : (Prims.int * fixity) = (((Prims.parse_int "70")), (Infix (Left)))


let e_bin_prio_seq : (Prims.int * fixity) = (((Prims.parse_int "100")), (Infix (Left)))


let e_app_prio : (Prims.int * fixity) = (((Prims.parse_int "10000")), (Infix (Left)))


let min_op_prec : (Prims.int * fixity) = (((~- ((Prims.parse_int "1")))), (Infix (NonAssoc)))


let max_op_prec : (Prims.int * fixity) = ((FStar_Util.max_int), (Infix (NonAssoc)))


let rec in_ns = (fun x -> (match (x) with
| ([], uu____102) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____116, uu____117) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| uu____133 -> begin
(

let cg_libs = (FStar_Options.codegen_libs ())
in (

let ns_len = (FStar_List.length ns)
in (

let found = (FStar_Util.find_map cg_libs (fun cg_path -> (

let cg_len = (FStar_List.length cg_path)
in (match (((FStar_List.length cg_path) < ns_len)) with
| true -> begin
(

let uu____155 = (FStar_Util.first_N cg_len ns)
in (match (uu____155) with
| (pfx, sfx) -> begin
(match ((pfx = cg_path)) with
| true -> begin
(

let uu____173 = (

let uu____175 = (

let uu____177 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____177)::[])
in (FStar_List.append pfx uu____175))
in FStar_Pervasives_Native.Some (uu____173))
end
| uu____179 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____181 -> begin
FStar_Pervasives_Native.None
end))))
in (match (found) with
| FStar_Pervasives_Native.None -> begin
(ns')::[]
end
| FStar_Pervasives_Native.Some (x) -> begin
x
end))))
end)))


let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (

let uu____194 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____194) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____197 -> begin
(

let uu____198 = x
in (match (uu____198) with
| (ns, x1) -> begin
(

let uu____203 = (path_of_ns currentModule ns)
in ((uu____203), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____209 = (

let uu____210 = (

let uu____211 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____211))
in (

let uu____212 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____210 <> uu____212)))
in (match (uu____209) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____213 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____222 -> begin
(

let uu____223 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____223) with
| (p, s) -> begin
(

let uu____228 = (

let uu____230 = (

let uu____232 = (ptsym_of_symbol s)
in (uu____232)::[])
in (FStar_List.append p uu____230))
in (FStar_String.concat "." uu____228))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____239 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____239) with
| (p, s) -> begin
(

let s1 = (

let uu____245 = (

let uu____246 = (

let uu____247 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____247))
in (

let uu____248 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____246 <> uu____248)))
in (match (uu____245) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____249 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____373 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____401 -> (match (uu____401) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____423 -> (match (uu____423) with
| (y, uu____430, uu____431) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____436 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____445 = (as_bin_op p)
in (uu____445 <> FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____468 -> (match (uu____468) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____481 -> (match (uu____481) with
| (y, uu____485) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____486 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____492 = (as_uni_op p)
in (uu____492 <> FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____509 -> (match (uu____509) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____522 -> (match (uu____522) with
| (y, uu____526) -> begin
(x = y)
end)) prim_constructors)
end
| uu____527 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____533 = (as_standard_constructor p)
in (uu____533 <> FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____554 inner doc1 -> (match (uu____554) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____587 = _inner
in (match (uu____587) with
| (pi, fi) -> begin
(

let uu____592 = _outer
in (match (uu____592) with
| (po, fo) -> begin
((pi > po) || (match (((fi), (side1))) with
| (Postfix, Left) -> begin
true
end
| (Prefix, Right) -> begin
true
end
| (Infix (Left), Left) -> begin
((pi = po) && (fo = Infix (Left)))
end
| (Infix (Right), Right) -> begin
((pi = po) && (fo = Infix (Right)))
end
| (Infix (Left), ILeft) -> begin
((pi = po) && (fo = Infix (Left)))
end
| (Infix (Right), IRight) -> begin
((pi = po) && (fo = Infix (Right)))
end
| (uu____597, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____598, uu____599) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____600 -> begin
(FStar_Format.parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___117_615 -> (match (uu___117_615) with
| c when (c = '\\') -> begin
"\\\\"
end
| c when (c = ' ') -> begin
" "
end
| c when (c = '\b') -> begin
"\\b"
end
| c when (c = '\t') -> begin
"\\t"
end
| c when (c = '\r') -> begin
"\\r"
end
| c when (c = '\n') -> begin
"\\n"
end
| c when (c = '\'') -> begin
"\\\'"
end
| c when (c = '\"') -> begin
"\\\""
end
| c when (FStar_Util.is_letter_or_digit c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_punctuation c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_symbol c) -> begin
(FStar_Util.string_of_char c)
end
| c -> begin
(fallback c)
end))


let string_of_mlconstant : FStar_Extraction_ML_Syntax.mlconstant  ->  Prims.string = (fun sctt -> (match (sctt) with
| FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"()"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (true) -> begin
"true"
end
| FStar_Extraction_ML_Syntax.MLC_Bool (false) -> begin
"false"
end
| FStar_Extraction_ML_Syntax.MLC_Char (c) -> begin
(

let uu____634 = (

let uu____635 = (escape_or escape_char_hex c)
in (Prims.strcat uu____635 "\'"))
in (Prims.strcat "\'" uu____634))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____649, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____656, FStar_Const.Int16)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
(Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")"))
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(

let uu____671 = (

let uu____672 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____672 "\""))
in (Prims.strcat "\"" uu____671))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____674 = (

let uu____675 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____675 "\""))
in (Prims.strcat "\"" uu____674))
end
| uu____676 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____697 -> begin
s
end))
in (

let uu____698 = (

let uu____699 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar uu____699))
in (FStar_Format.text uu____698)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____707 = (

let uu____708 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____708))
in (FStar_Format.parens uu____707))
in doc2))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args1 = (match (args) with
| [] -> begin
FStar_Format.empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule ((t_prio_name), (Left)) arg)
end
| uu____717 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____723 = (

let uu____724 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____724))
in (FStar_Format.parens uu____723)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____726 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____726))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____728, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____736 = (

let uu____737 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____737))
in (maybe_paren outer t_prio_fun uu____736))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____738 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____738) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____739 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____743 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____743)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____791 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____791) with
| true -> begin
(

let uu____792 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc1)::[]))
in (FStar_Format.parens uu____792))
end
| uu____793 -> begin
(

let uu____794 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____794))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs2 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs1)
in (

let uu____804 = (FStar_Format.reduce docs2)
in (FStar_Format.parens uu____804))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____806 = (string_of_mlconstant c)
in (FStar_Format.text uu____806))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____808) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____810 = (ptsym currentModule path)
in (FStar_Format.text uu____810))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____826 -> (match (uu____826) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____834 = (

let uu____836 = (

let uu____837 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____837))
in (uu____836)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____834)))
end))
in (

let uu____839 = (

let uu____840 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____840))
in (FStar_Format.cbrackets uu____839)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____847 = (is_standard_constructor ctor)
in (match (uu____847) with
| true -> begin
(

let uu____848 = (

let uu____851 = (as_standard_constructor ctor)
in (FStar_Option.get uu____851))
in (FStar_Pervasives_Native.snd uu____848))
end
| uu____857 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____863 = (is_standard_constructor ctor)
in (match (uu____863) with
| true -> begin
(

let uu____864 = (

let uu____867 = (as_standard_constructor ctor)
in (FStar_Option.get uu____867))
in (FStar_Pervasives_Native.snd uu____864))
end
| uu____873 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____883, uu____884) -> begin
(

let uu____887 = (

let uu____889 = (

let uu____891 = (

let uu____892 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____892))
in (uu____891)::[])
in ((FStar_Format.text name))::uu____889)
in (FStar_Format.reduce1 uu____887))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs1 = (FStar_List.map (fun x -> (

let uu____898 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____898))) es)
in (

let docs2 = (

let uu____902 = (FStar_Format.combine (FStar_Format.text ", ") docs1)
in (FStar_Format.parens uu____902))
in docs2))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____904, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____914 = (

let uu____916 = (

let uu____918 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____918)::[])
in (FStar_Format.hardline)::uu____916)
in (FStar_Format.reduce uu____914))
end
| uu____919 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____925 = (

let uu____926 = (

let uu____928 = (

let uu____930 = (

let uu____932 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____932)::[])
in (doc1)::uu____930)
in (pre)::uu____928)
in (FStar_Format.combine FStar_Format.hardline uu____926))
in (FStar_Format.parens uu____925)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____939)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____941; FStar_Extraction_ML_Syntax.loc = uu____942})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____944))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____946; FStar_Extraction_ML_Syntax.loc = uu____947})::[]) when (

let uu____965 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____965 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____978; FStar_Extraction_ML_Syntax.loc = uu____979}, branches); FStar_Extraction_ML_Syntax.mlty = uu____981; FStar_Extraction_ML_Syntax.loc = uu____982} when (

let uu____993 = (FStar_Extraction_ML_Syntax.idsym arg)
in (

let uu____994 = (FStar_Extraction_ML_Syntax.idsym arg')
in (uu____993 = uu____994))) -> begin
branches
end
| e2 -> begin
(((FStar_Extraction_ML_Syntax.MLP_Wild), (FStar_Pervasives_Native.None), (e2)))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try (((scrutinee), (branches))); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::(e2)::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1015; FStar_Extraction_ML_Syntax.loc = uu____1016}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1026; FStar_Extraction_ML_Syntax.loc = uu____1027}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1032 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1043 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1043))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1050 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1050) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1052 -> begin
(

let uu____1053 = (

let uu____1055 = (

let uu____1057 = (

let uu____1059 = (

let uu____1060 = (ptsym currentModule f)
in (FStar_Format.text uu____1060))
in (uu____1059)::[])
in ((FStar_Format.text "."))::uu____1057)
in (e2)::uu____1055)
in (FStar_Format.reduce uu____1053))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1078 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1078) with
| true -> begin
(

let uu____1079 = (

let uu____1081 = (

let uu____1083 = (

let uu____1085 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1087 = (

let uu____1089 = (

let uu____1091 = (doc_of_mltype currentModule outer xxt)
in (uu____1091)::[])
in ((FStar_Format.text " : "))::uu____1089)
in (FStar_Format.reduce1 uu____1087))
end
| uu____1092 -> begin
(FStar_Format.text "")
end)
in (uu____1085)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1083)
in ((FStar_Format.text "("))::uu____1081)
in (FStar_Format.reduce1 uu____1079))
end
| uu____1094 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1101 -> (match (uu____1101) with
| ((x, uu____1107), xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1115 = (

let uu____1117 = (

let uu____1119 = (FStar_Format.reduce1 ids1)
in (uu____1119)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1117)
in (FStar_Format.reduce1 uu____1115))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1127 = (

let uu____1129 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1130 = (

let uu____1132 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1132)::((FStar_Format.text "end"))::[])
in (uu____1129)::uu____1130))
in (FStar_Format.combine FStar_Format.hardline uu____1127))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1143 = (

let uu____1145 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1146 = (

let uu____1148 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1151 = (

let uu____1153 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1154 = (

let uu____1156 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1156)::((FStar_Format.text "end"))::[])
in (uu____1153)::uu____1154))
in (uu____1148)::uu____1151))
in (uu____1145)::uu____1146))
in (FStar_Format.combine FStar_Format.hardline uu____1143))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1178 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1178)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1182 = (

let uu____1184 = (

let uu____1186 = (

let uu____1187 = (ptctor currentModule exn)
in (FStar_Format.text uu____1187))
in (uu____1186)::[])
in ((FStar_Format.text "raise"))::uu____1184)
in (FStar_Format.reduce1 uu____1182))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1196 = (

let uu____1198 = (

let uu____1200 = (

let uu____1201 = (ptctor currentModule exn)
in (FStar_Format.text uu____1201))
in (

let uu____1202 = (

let uu____1204 = (

let uu____1205 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1205))
in (uu____1204)::[])
in (uu____1200)::uu____1202))
in ((FStar_Format.text "raise"))::uu____1198)
in (FStar_Format.reduce1 uu____1196)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1218 = (

let uu____1220 = (

let uu____1222 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1225 = (

let uu____1227 = (

let uu____1229 = (

let uu____1230 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1230))
in (uu____1229)::[])
in ((FStar_Format.text "with"))::uu____1227)
in (uu____1222)::uu____1225))
in ((FStar_Format.text "try"))::uu____1220)
in (FStar_Format.combine FStar_Format.hardline uu____1218))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1236 = (

let uu____1242 = (as_bin_op p)
in (FStar_Option.get uu____1242))
in (match (uu____1236) with
| (uu____1254, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1271 = (

let uu____1274 = (as_uni_op p)
in (FStar_Option.get uu____1274))
in (match (uu____1271) with
| (uu____1280, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (FStar_Format.reduce1 (((FStar_Format.text txt))::((FStar_Format.parens e11))::[]))
in (FStar_Format.parens doc1)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(

let uu____1289 = (string_of_mlconstant c)
in (FStar_Format.text uu____1289))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (FStar_Pervasives_Native.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1306 -> (match (uu____1306) with
| (name, p) -> begin
(

let uu____1311 = (

let uu____1313 = (

let uu____1314 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1314))
in (

let uu____1316 = (

let uu____1318 = (

let uu____1320 = (doc_of_pattern currentModule p)
in (uu____1320)::[])
in ((FStar_Format.text "="))::uu____1318)
in (uu____1313)::uu____1316))
in (FStar_Format.reduce1 uu____1311))
end))
in (

let uu____1321 = (

let uu____1322 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1322))
in (FStar_Format.cbrackets uu____1321)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1329 = (is_standard_constructor ctor)
in (match (uu____1329) with
| true -> begin
(

let uu____1330 = (

let uu____1333 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1333))
in (FStar_Pervasives_Native.snd uu____1330))
end
| uu____1339 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1345 = (is_standard_constructor ctor)
in (match (uu____1345) with
| true -> begin
(

let uu____1346 = (

let uu____1349 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1349))
in (FStar_Pervasives_Native.snd uu____1346))
end
| uu____1355 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____1361 = (

let uu____1363 = (

let uu____1364 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____1364))
in (

let uu____1365 = (

let uu____1367 = (

let uu____1369 = (doc_of_pattern currentModule xs)
in (uu____1369)::[])
in ((FStar_Format.text "::"))::uu____1367)
in (uu____1363)::uu____1365))
in (FStar_Format.reduce uu____1361))
end
| (uu____1370, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1371))::[]) -> begin
(

let uu____1374 = (

let uu____1376 = (

let uu____1378 = (

let uu____1379 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____1379))
in (uu____1378)::[])
in ((FStar_Format.text name))::uu____1376)
in (FStar_Format.reduce1 uu____1374))
end
| uu____1380 -> begin
(

let uu____1384 = (

let uu____1386 = (

let uu____1388 = (

let uu____1389 = (

let uu____1390 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____1390))
in (FStar_Format.parens uu____1389))
in (uu____1388)::[])
in ((FStar_Format.text name))::uu____1386)
in (FStar_Format.reduce1 uu____1384))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____1398 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____1398)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1406 -> (match (uu____1406) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1413 = (

let uu____1415 = (

let uu____1417 = (doc_of_pattern currentModule p)
in (uu____1417)::[])
in ((FStar_Format.text "|"))::uu____1415)
in (FStar_Format.reduce1 uu____1413))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____1422 = (

let uu____1424 = (

let uu____1426 = (doc_of_pattern currentModule p)
in (uu____1426)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____1424)
in (FStar_Format.reduce1 uu____1422)))
end)
in (

let uu____1427 = (

let uu____1429 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1430 = (

let uu____1432 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1432)::((FStar_Format.text "end"))::[])
in (uu____1429)::uu____1430))
in (FStar_Format.combine FStar_Format.hardline uu____1427)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1436 -> (match (uu____1436) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1449 -> (match (uu____1449) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1452; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1462 -> begin
(

let uu____1463 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1463) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____1464)::uu____1465, uu____1466) -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.None -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty1)::[])))
end)
end
| uu____1480 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.None -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ((uu____1481)::uu____1482, uu____1483) -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty1)::[])))
end)
end
| uu____1497 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____1498 = (

let uu____1500 = (

let uu____1501 = (FStar_Extraction_ML_Syntax.idsym name)
in (FStar_Format.text uu____1501))
in (

let uu____1502 = (

let uu____1504 = (FStar_Format.reduce1 ids)
in (uu____1504)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in (uu____1500)::uu____1502))
in (FStar_Format.reduce1 uu____1498)))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1506 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1513 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1514 -> (match (uu____1514) with
| (lineno, file) -> begin
(

let uu____1517 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1517) with
| true -> begin
FStar_Format.empty
end
| uu____1518 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1537 -> (match (uu____1537) with
| (uu____1546, x, mangle_opt, tparams, body) -> begin
(

let x1 = (match (mangle_opt) with
| FStar_Pervasives_Native.None -> begin
x
end
| FStar_Pervasives_Native.Some (y) -> begin
y
end)
in (

let tparams1 = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x2)::[] -> begin
(

let uu____1561 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1561))
end
| uu____1562 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (

let uu____1567 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1567))) tparams)
in (

let uu____1568 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____1568)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1585 -> (match (uu____1585) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____1594 = (

let uu____1595 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1595))
in (FStar_Format.cbrackets uu____1594)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1614 -> (match (uu____1614) with
| (name, tys) -> begin
(

let uu____1628 = (FStar_List.split tys)
in (match (uu____1628) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1639 -> begin
(

let tys2 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys1)
in (

let tys3 = (FStar_Format.combine (FStar_Format.text " * ") tys2)
in (FStar_Format.reduce1 (((FStar_Format.text name))::((FStar_Format.text "of"))::(tys3)::[]))))
end)
end))
end))
in (

let ctors1 = (FStar_List.map forctor ctors)
in (

let ctors2 = (FStar_List.map (fun d -> (FStar_Format.reduce1 (((FStar_Format.text "|"))::(d)::[]))) ctors1)
in (FStar_Format.combine FStar_Format.hardline ctors2))))
end))
in (

let doc1 = (

let uu____1657 = (

let uu____1659 = (

let uu____1661 = (

let uu____1662 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____1662))
in (uu____1661)::[])
in (tparams1)::uu____1659)
in (FStar_Format.reduce1 uu____1657))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____1666 = (

let uu____1668 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____1668)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____1666)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1683 = (

let uu____1685 = (

let uu____1687 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____1687)::[])
in ((FStar_Format.text "type"))::uu____1685)
in (FStar_Format.reduce1 uu____1683))
end
| uu____1688 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____1703 = (

let uu____1705 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____1706 = (

let uu____1708 = (doc_of_sig currentModule subsig)
in (

let uu____1709 = (

let uu____1711 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____1711)::[])
in (uu____1708)::uu____1709))
in (uu____1705)::uu____1706))
in (FStar_Format.combine FStar_Format.hardline uu____1703))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____1723 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____1723))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1725, ty)) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text "val"))::((FStar_Format.text x))::((FStar_Format.text ": "))::(ty1)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (

let docs1 = (FStar_List.map (doc_of_sig1 currentModule) s)
in (

let docs2 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs1)
in (FStar_Format.reduce docs2))))


let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args1 = (FStar_List.map FStar_Pervasives_Native.snd args)
in (

let args2 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args1)
in (

let args3 = (

let uu____1769 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____1769))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1772, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____1778 = (

let uu____1780 = (

let uu____1782 = (

let uu____1784 = (

let uu____1786 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1786)::[])
in ((FStar_Format.text "="))::uu____1784)
in ((FStar_Format.text "_"))::uu____1782)
in ((FStar_Format.text "let"))::uu____1780)
in (FStar_Format.reduce1 uu____1778))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs1 = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1802) -> begin
FStar_Format.empty
end
| uu____1803 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs1))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1809 -> (match (uu____1809) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1847 -> (match (uu____1847) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____1886 -> (match (uu____1886) with
| (s, uu____1890) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____1905 = (

let uu____1907 = (

let uu____1909 = (

let uu____1911 = (FStar_Format.reduce sub3)
in (uu____1911)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1909)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____1907)
in (FStar_Format.reduce uu____1905))))))))
end))
and for1_mod = (fun istop uu____1914 -> (match (uu____1914) with
| (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name)
in (

let maybe_open_pervasives = (match (mod_name) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____1951 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____1958 = (

let uu____1960 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1960) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____1962 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1964 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____1958))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1966 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____1971 -> (match (uu____1971) with
| (uu____1974, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____1992 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1992) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____1994 -> begin
[]
end))
in (

let uu____1995 = (

let uu____1997 = (

let uu____1999 = (

let uu____2001 = (

let uu____2003 = (

let uu____2005 = (

let uu____2007 = (FStar_Format.reduce sub3)
in (uu____2007)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____2005)
in (FStar_Format.hardline)::uu____2003)
in (FStar_List.append maybe_open_pervasives uu____2001))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____1999))
in (FStar_List.append prefix1 uu____1997))
in (FStar_All.pipe_left FStar_Format.reduce uu____1995))))))))))
end))
in (

let docs1 = (FStar_List.map (fun uu____2025 -> (match (uu____2025) with
| (x, s, m) -> begin
(

let uu____2052 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____2053 = (for1_mod true ((x), (s), (m)))
in ((uu____2052), (uu____2053))))
end)) mllib)
in docs1))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2073 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____2073 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2083 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____2083 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





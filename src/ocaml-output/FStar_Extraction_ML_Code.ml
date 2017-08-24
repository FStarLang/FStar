
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
| c when (c = 92 (*\*)) -> begin
"\\\\"
end
| c when (c = 32 (* *)) -> begin
" "
end
| c when (c = 8) -> begin
"\\b"
end
| c when (c = 9) -> begin
"\\t"
end
| c when (c = 13) -> begin
"\\r"
end
| c when (c = 10) -> begin
"\\n"
end
| c when (c = 39 (*'*)) -> begin
"\\\'"
end
| c when (c = 34 (*"*)) -> begin
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

let nc = (FStar_Char.int_of_char c)
in (

let uu____637 = (FStar_Util.string_of_int nc)
in (Prims.strcat uu____637 (match (((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127")))) with
| true -> begin
(Prims.strcat " (*" (Prims.strcat (FStar_Util.string_of_char c) "*)"))
end
| uu____656 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____670, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____677, FStar_Const.Int16)) -> begin
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

let uu____692 = (

let uu____693 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____693 "\""))
in (Prims.strcat "\"" uu____692))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____695 = (

let uu____696 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____696 "\""))
in (Prims.strcat "\"" uu____695))
end
| uu____697 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____718 -> begin
s
end))
in (

let uu____719 = (

let uu____720 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar uu____720))
in (FStar_Format.text uu____719)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____728 = (

let uu____729 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____729))
in (FStar_Format.parens uu____728))
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
| uu____738 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____744 = (

let uu____745 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____745))
in (FStar_Format.parens uu____744)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____747 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____747))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____749, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____757 = (

let uu____758 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____758))
in (maybe_paren outer t_prio_fun uu____757))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____759 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____759) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____760 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____764 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____764)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____812 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____812) with
| true -> begin
(

let uu____813 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc1)::[]))
in (FStar_Format.parens uu____813))
end
| uu____814 -> begin
(

let uu____815 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____815))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs2 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs1)
in (

let uu____825 = (FStar_Format.reduce docs2)
in (FStar_Format.parens uu____825))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____827 = (string_of_mlconstant c)
in (FStar_Format.text uu____827))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____829) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____831 = (ptsym currentModule path)
in (FStar_Format.text uu____831))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____847 -> (match (uu____847) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____855 = (

let uu____857 = (

let uu____858 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____858))
in (uu____857)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____855)))
end))
in (

let uu____860 = (

let uu____861 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____861))
in (FStar_Format.cbrackets uu____860)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____868 = (is_standard_constructor ctor)
in (match (uu____868) with
| true -> begin
(

let uu____869 = (

let uu____872 = (as_standard_constructor ctor)
in (FStar_Option.get uu____872))
in (FStar_Pervasives_Native.snd uu____869))
end
| uu____878 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____884 = (is_standard_constructor ctor)
in (match (uu____884) with
| true -> begin
(

let uu____885 = (

let uu____888 = (as_standard_constructor ctor)
in (FStar_Option.get uu____888))
in (FStar_Pervasives_Native.snd uu____885))
end
| uu____894 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____904, uu____905) -> begin
(

let uu____908 = (

let uu____910 = (

let uu____912 = (

let uu____913 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____913))
in (uu____912)::[])
in ((FStar_Format.text name))::uu____910)
in (FStar_Format.reduce1 uu____908))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs1 = (FStar_List.map (fun x -> (

let uu____919 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____919))) es)
in (

let docs2 = (

let uu____923 = (FStar_Format.combine (FStar_Format.text ", ") docs1)
in (FStar_Format.parens uu____923))
in docs2))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____925, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____935 = (

let uu____937 = (

let uu____939 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____939)::[])
in (FStar_Format.hardline)::uu____937)
in (FStar_Format.reduce uu____935))
end
| uu____940 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____946 = (

let uu____947 = (

let uu____949 = (

let uu____951 = (

let uu____953 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____953)::[])
in (doc1)::uu____951)
in (pre)::uu____949)
in (FStar_Format.combine FStar_Format.hardline uu____947))
in (FStar_Format.parens uu____946)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____960)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____962; FStar_Extraction_ML_Syntax.loc = uu____963})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____965))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____967; FStar_Extraction_ML_Syntax.loc = uu____968})::[]) when (

let uu____986 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____986 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____999; FStar_Extraction_ML_Syntax.loc = uu____1000}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1002; FStar_Extraction_ML_Syntax.loc = uu____1003} when (

let uu____1014 = (FStar_Extraction_ML_Syntax.idsym arg)
in (

let uu____1015 = (FStar_Extraction_ML_Syntax.idsym arg')
in (uu____1014 = uu____1015))) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1036; FStar_Extraction_ML_Syntax.loc = uu____1037}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1047; FStar_Extraction_ML_Syntax.loc = uu____1048}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1053 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1064 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1064))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1071 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1071) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1073 -> begin
(

let uu____1074 = (

let uu____1076 = (

let uu____1078 = (

let uu____1080 = (

let uu____1081 = (ptsym currentModule f)
in (FStar_Format.text uu____1081))
in (uu____1080)::[])
in ((FStar_Format.text "."))::uu____1078)
in (e2)::uu____1076)
in (FStar_Format.reduce uu____1074))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1099 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1099) with
| true -> begin
(

let uu____1100 = (

let uu____1102 = (

let uu____1104 = (

let uu____1106 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1108 = (

let uu____1110 = (

let uu____1112 = (doc_of_mltype currentModule outer xxt)
in (uu____1112)::[])
in ((FStar_Format.text " : "))::uu____1110)
in (FStar_Format.reduce1 uu____1108))
end
| uu____1113 -> begin
(FStar_Format.text "")
end)
in (uu____1106)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1104)
in ((FStar_Format.text "("))::uu____1102)
in (FStar_Format.reduce1 uu____1100))
end
| uu____1115 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1122 -> (match (uu____1122) with
| ((x, uu____1128), xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1136 = (

let uu____1138 = (

let uu____1140 = (FStar_Format.reduce1 ids1)
in (uu____1140)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1138)
in (FStar_Format.reduce1 uu____1136))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1148 = (

let uu____1150 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1151 = (

let uu____1153 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1153)::((FStar_Format.text "end"))::[])
in (uu____1150)::uu____1151))
in (FStar_Format.combine FStar_Format.hardline uu____1148))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1164 = (

let uu____1166 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1167 = (

let uu____1169 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1172 = (

let uu____1174 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1175 = (

let uu____1177 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1177)::((FStar_Format.text "end"))::[])
in (uu____1174)::uu____1175))
in (uu____1169)::uu____1172))
in (uu____1166)::uu____1167))
in (FStar_Format.combine FStar_Format.hardline uu____1164))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1199 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1199)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1203 = (

let uu____1205 = (

let uu____1207 = (

let uu____1208 = (ptctor currentModule exn)
in (FStar_Format.text uu____1208))
in (uu____1207)::[])
in ((FStar_Format.text "raise"))::uu____1205)
in (FStar_Format.reduce1 uu____1203))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1217 = (

let uu____1219 = (

let uu____1221 = (

let uu____1222 = (ptctor currentModule exn)
in (FStar_Format.text uu____1222))
in (

let uu____1223 = (

let uu____1225 = (

let uu____1226 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1226))
in (uu____1225)::[])
in (uu____1221)::uu____1223))
in ((FStar_Format.text "raise"))::uu____1219)
in (FStar_Format.reduce1 uu____1217)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1239 = (

let uu____1241 = (

let uu____1243 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1246 = (

let uu____1248 = (

let uu____1250 = (

let uu____1251 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1251))
in (uu____1250)::[])
in ((FStar_Format.text "with"))::uu____1248)
in (uu____1243)::uu____1246))
in ((FStar_Format.text "try"))::uu____1241)
in (FStar_Format.combine FStar_Format.hardline uu____1239))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1257 = (

let uu____1263 = (as_bin_op p)
in (FStar_Option.get uu____1263))
in (match (uu____1257) with
| (uu____1275, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1292 = (

let uu____1295 = (as_uni_op p)
in (FStar_Option.get uu____1295))
in (match (uu____1292) with
| (uu____1301, txt) -> begin
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

let uu____1310 = (string_of_mlconstant c)
in (FStar_Format.text uu____1310))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (FStar_Pervasives_Native.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1327 -> (match (uu____1327) with
| (name, p) -> begin
(

let uu____1332 = (

let uu____1334 = (

let uu____1335 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1335))
in (

let uu____1337 = (

let uu____1339 = (

let uu____1341 = (doc_of_pattern currentModule p)
in (uu____1341)::[])
in ((FStar_Format.text "="))::uu____1339)
in (uu____1334)::uu____1337))
in (FStar_Format.reduce1 uu____1332))
end))
in (

let uu____1342 = (

let uu____1343 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1343))
in (FStar_Format.cbrackets uu____1342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1350 = (is_standard_constructor ctor)
in (match (uu____1350) with
| true -> begin
(

let uu____1351 = (

let uu____1354 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1354))
in (FStar_Pervasives_Native.snd uu____1351))
end
| uu____1360 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1366 = (is_standard_constructor ctor)
in (match (uu____1366) with
| true -> begin
(

let uu____1367 = (

let uu____1370 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1370))
in (FStar_Pervasives_Native.snd uu____1367))
end
| uu____1376 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____1382 = (

let uu____1384 = (

let uu____1385 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____1385))
in (

let uu____1386 = (

let uu____1388 = (

let uu____1390 = (doc_of_pattern currentModule xs)
in (uu____1390)::[])
in ((FStar_Format.text "::"))::uu____1388)
in (uu____1384)::uu____1386))
in (FStar_Format.reduce uu____1382))
end
| (uu____1391, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1392))::[]) -> begin
(

let uu____1395 = (

let uu____1397 = (

let uu____1399 = (

let uu____1400 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____1400))
in (uu____1399)::[])
in ((FStar_Format.text name))::uu____1397)
in (FStar_Format.reduce1 uu____1395))
end
| uu____1401 -> begin
(

let uu____1405 = (

let uu____1407 = (

let uu____1409 = (

let uu____1410 = (

let uu____1411 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____1411))
in (FStar_Format.parens uu____1410))
in (uu____1409)::[])
in ((FStar_Format.text name))::uu____1407)
in (FStar_Format.reduce1 uu____1405))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____1419 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____1419)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1427 -> (match (uu____1427) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1434 = (

let uu____1436 = (

let uu____1438 = (doc_of_pattern currentModule p)
in (uu____1438)::[])
in ((FStar_Format.text "|"))::uu____1436)
in (FStar_Format.reduce1 uu____1434))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____1443 = (

let uu____1445 = (

let uu____1447 = (doc_of_pattern currentModule p)
in (uu____1447)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____1445)
in (FStar_Format.reduce1 uu____1443)))
end)
in (

let uu____1448 = (

let uu____1450 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1451 = (

let uu____1453 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1453)::((FStar_Format.text "end"))::[])
in (uu____1450)::uu____1451))
in (FStar_Format.combine FStar_Format.hardline uu____1448)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1457 -> (match (uu____1457) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1470 -> (match (uu____1470) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1473; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1483 -> begin
(

let uu____1484 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1484) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____1485)::uu____1486, uu____1487) -> begin
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
| uu____1501 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.None -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ((uu____1502)::uu____1503, uu____1504) -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty1)::[])))
end)
end
| uu____1518 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____1519 = (

let uu____1521 = (

let uu____1522 = (FStar_Extraction_ML_Syntax.idsym name)
in (FStar_Format.text uu____1522))
in (

let uu____1523 = (

let uu____1525 = (FStar_Format.reduce1 ids)
in (uu____1525)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in (uu____1521)::uu____1523))
in (FStar_Format.reduce1 uu____1519)))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1527 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1534 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1535 -> (match (uu____1535) with
| (lineno, file) -> begin
(

let uu____1538 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1538) with
| true -> begin
FStar_Format.empty
end
| uu____1539 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1558 -> (match (uu____1558) with
| (uu____1567, x, mangle_opt, tparams, body) -> begin
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

let uu____1582 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1582))
end
| uu____1583 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (

let uu____1588 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1588))) tparams)
in (

let uu____1589 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____1589)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1606 -> (match (uu____1606) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____1615 = (

let uu____1616 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1616))
in (FStar_Format.cbrackets uu____1615)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1635 -> (match (uu____1635) with
| (name, tys) -> begin
(

let uu____1649 = (FStar_List.split tys)
in (match (uu____1649) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1660 -> begin
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

let uu____1678 = (

let uu____1680 = (

let uu____1682 = (

let uu____1683 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____1683))
in (uu____1682)::[])
in (tparams1)::uu____1680)
in (FStar_Format.reduce1 uu____1678))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____1687 = (

let uu____1689 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____1689)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____1687)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1704 = (

let uu____1706 = (

let uu____1708 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____1708)::[])
in ((FStar_Format.text "type"))::uu____1706)
in (FStar_Format.reduce1 uu____1704))
end
| uu____1709 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____1724 = (

let uu____1726 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____1727 = (

let uu____1729 = (doc_of_sig currentModule subsig)
in (

let uu____1730 = (

let uu____1732 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____1732)::[])
in (uu____1729)::uu____1730))
in (uu____1726)::uu____1727))
in (FStar_Format.combine FStar_Format.hardline uu____1724))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____1744 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____1744))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1746, ty)) -> begin
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

let uu____1790 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____1790))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1793, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____1799 = (

let uu____1801 = (

let uu____1803 = (

let uu____1805 = (

let uu____1807 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1807)::[])
in ((FStar_Format.text "="))::uu____1805)
in ((FStar_Format.text "_"))::uu____1803)
in ((FStar_Format.text "let"))::uu____1801)
in (FStar_Format.reduce1 uu____1799))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs1 = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1823) -> begin
FStar_Format.empty
end
| uu____1824 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs1))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1830 -> (match (uu____1830) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1868 -> (match (uu____1868) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____1907 -> (match (uu____1907) with
| (s, uu____1911) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____1926 = (

let uu____1928 = (

let uu____1930 = (

let uu____1932 = (FStar_Format.reduce sub3)
in (uu____1932)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1930)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____1928)
in (FStar_Format.reduce uu____1926))))))))
end))
and for1_mod = (fun istop uu____1935 -> (match (uu____1935) with
| (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name)
in (

let maybe_open_pervasives = (match (mod_name) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____1972 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____1979 = (

let uu____1981 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1981) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____1983 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1985 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____1979))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1987 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____1992 -> (match (uu____1992) with
| (uu____1995, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____2013 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2013) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____2015 -> begin
[]
end))
in (

let uu____2016 = (

let uu____2018 = (

let uu____2020 = (

let uu____2022 = (

let uu____2024 = (

let uu____2026 = (

let uu____2028 = (FStar_Format.reduce sub3)
in (uu____2028)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____2026)
in (FStar_Format.hardline)::uu____2024)
in (FStar_List.append maybe_open_pervasives uu____2022))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____2020))
in (FStar_List.append prefix1 uu____2018))
in (FStar_All.pipe_left FStar_Format.reduce uu____2016))))))))))
end))
in (

let docs1 = (FStar_List.map (fun uu____2046 -> (match (uu____2046) with
| (x, s, m) -> begin
(

let uu____2073 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____2074 = (for1_mod true ((x), (s), (m)))
in ((uu____2073), (uu____2074))))
end)) mllib)
in docs1))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2094 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____2094 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2104 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____2104 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





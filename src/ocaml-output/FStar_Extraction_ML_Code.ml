
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
| uu____6 -> begin
false
end))


let uu___is_IRight : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IRight -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Left : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Right : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_NonAssoc : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____30 -> begin
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
| uu____41 -> begin
false
end))


let uu___is_Postfix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Postfix -> begin
true
end
| uu____47 -> begin
false
end))


let uu___is_Infix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
true
end
| uu____54 -> begin
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


let rec in_ns : 'a . ('a Prims.list * 'a Prims.list)  ->  Prims.bool = (fun x -> (match (x) with
| ([], uu____173) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (Prims.op_Equality x1 x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____196, uu____197) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((Prims.op_Equality ns' currentModule)) with
| true -> begin
[]
end
| uu____225 -> begin
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

let uu____259 = (FStar_Util.first_N cg_len ns)
in (match (uu____259) with
| (pfx, sfx) -> begin
(match ((Prims.op_Equality pfx cg_path)) with
| true -> begin
(

let uu____292 = (

let uu____295 = (

let uu____298 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____298)::[])
in (FStar_List.append pfx uu____295))
in FStar_Pervasives_Native.Some (uu____292))
end
| uu____301 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____304 -> begin
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

let uu____326 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____326) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____331 -> begin
(

let uu____332 = x
in (match (uu____332) with
| (ns, x1) -> begin
(

let uu____339 = (path_of_ns currentModule ns)
in ((uu____339), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____349 = (

let uu____350 = (

let uu____352 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____352))
in (

let uu____354 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____350 uu____354)))
in (match (uu____349) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____357 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____372 -> begin
(

let uu____373 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____373) with
| (p, s) -> begin
(

let uu____380 = (

let uu____383 = (

let uu____386 = (ptsym_of_symbol s)
in (uu____386)::[])
in (FStar_List.append p uu____383))
in (FStar_String.concat "." uu____380))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____397 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____397) with
| (p, s) -> begin
(

let s1 = (

let uu____405 = (

let uu____406 = (

let uu____408 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____408))
in (

let uu____410 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____406 uu____410)))
in (match (uu____405) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____413 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____642 -> (

let op_minus = (

let uu____644 = (

let uu____645 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____645 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____644) with
| true -> begin
"-"
end
| uu____650 -> begin
"~-"
end))
in ((("op_Negation"), ("not")))::((("op_Minus"), (op_minus)))::((("op_Bang"), ("Support.ST.read")))::[]))


let prim_types : 'Auu____669 . unit  ->  'Auu____669 Prims.list = (fun uu____672 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (Prims.op_Equality ns (("Prims")::[])))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____726 -> (match (uu____726) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____771 -> (match (uu____771) with
| (y, uu____783, uu____784) -> begin
(Prims.op_Equality x y)
end)) infix_prim_ops)
end
| uu____793 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____809 = (as_bin_op p)
in (Prims.op_disEquality uu____809 FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____854 -> (match (uu____854) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(

let uu____873 = (prim_uni_ops ())
in (FStar_List.tryFind (fun uu____887 -> (match (uu____887) with
| (y, uu____893) -> begin
(Prims.op_Equality x y)
end)) uu____873))
end
| uu____894 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____904 = (as_uni_op p)
in (Prims.op_disEquality uu____904 FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____936 -> (match (uu____936) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____962 -> (match (uu____962) with
| (y, uu____968) -> begin
(Prims.op_Equality x y)
end)) prim_constructors)
end
| uu____969 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____979 = (as_standard_constructor p)
in (Prims.op_disEquality uu____979 FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____1020 inner doc1 -> (match (uu____1020) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____1077 = _inner
in (match (uu____1077) with
| (pi, fi) -> begin
(

let uu____1084 = _outer
in (match (uu____1084) with
| (po, fo) -> begin
((pi > po) || (match (((fi), (side1))) with
| (Postfix, Left) -> begin
true
end
| (Prefix, Right) -> begin
true
end
| (Infix (Left), Left) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fo (Infix (Left))))
end
| (Infix (Right), Right) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fo (Infix (Right))))
end
| (Infix (Left), ILeft) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fo (Infix (Left))))
end
| (Infix (Right), IRight) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fo (Infix (Right))))
end
| (uu____1091, NonAssoc) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fi fo))
end
| (uu____1092, uu____1093) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____1094 -> begin
(FStar_Format.parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___66_1119 -> (match (uu___66_1119) with
| c when (Prims.op_Equality c 92 (*\*)) -> begin
"\\\\"
end
| c when (Prims.op_Equality c 32 (* *)) -> begin
" "
end
| c when (Prims.op_Equality c 8) -> begin
"\\b"
end
| c when (Prims.op_Equality c 9) -> begin
"\\t"
end
| c when (Prims.op_Equality c 13) -> begin
"\\r"
end
| c when (Prims.op_Equality c 10) -> begin
"\\n"
end
| c when (Prims.op_Equality c 39 (*'*)) -> begin
"\\\'"
end
| c when (Prims.op_Equality c 34) -> begin
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

let uu____1171 = (FStar_Util.string_of_int nc)
in (Prims.strcat uu____1171 (match ((((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127"))) && (Prims.op_disEquality nc (Prims.parse_int "34")))) with
| true -> begin
(Prims.strcat " (*" (Prims.strcat (FStar_Util.string_of_char c) "*)"))
end
| uu____1194 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1218, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1230, FStar_Const.Int16)) -> begin
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

let uu____1256 = (

let uu____1257 = (FStar_Compiler_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____1257 "\""))
in (Prims.strcat "\"" uu____1256))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____1259 = (

let uu____1260 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____1260 "\""))
in (Prims.strcat "\"" uu____1259))
end
| uu____1261 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____1298 -> begin
s
end))
in (FStar_Format.text (escape_tyvar x)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____1310 = (

let uu____1311 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____1311))
in (FStar_Format.parens uu____1310))
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
| uu____1324 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1334 = (

let uu____1335 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____1335))
in (FStar_Format.parens uu____1334)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____1337 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____1337))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____1339, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____1351 = (

let uu____1352 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____1352))
in (maybe_paren outer t_prio_fun uu____1351))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____1353 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1353) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____1354 -> begin
(FStar_Format.text "Obj.t")
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(FStar_Format.text "unit")
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____1358 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____1358)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1446 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1446) with
| true -> begin
(

let uu____1447 = (FStar_Format.reduce (((FStar_Format.text "Prims.unsafe_coerce "))::(doc1)::[]))
in (FStar_Format.parens uu____1447))
end
| uu____1448 -> begin
(

let uu____1449 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____1449))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs1 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (

let uu____1465 = (FStar_Format.reduce docs1)
in (FStar_Format.parens uu____1465))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____1467 = (string_of_mlconstant c)
in (FStar_Format.text uu____1467))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____1470 = (ptsym currentModule path)
in (FStar_Format.text uu____1470))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____1498 -> (match (uu____1498) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1510 = (

let uu____1513 = (

let uu____1514 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1514))
in (uu____1513)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____1510)))
end))
in (

let uu____1517 = (

let uu____1518 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1518))
in (FStar_Format.cbrackets uu____1517)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____1529 = (is_standard_constructor ctor)
in (match (uu____1529) with
| true -> begin
(

let uu____1530 = (

let uu____1535 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1535))
in (FStar_Pervasives_Native.snd uu____1530))
end
| uu____1546 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____1554 = (is_standard_constructor ctor)
in (match (uu____1554) with
| true -> begin
(

let uu____1555 = (

let uu____1560 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1560))
in (FStar_Pervasives_Native.snd uu____1555))
end
| uu____1571 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____1586, uu____1587) -> begin
(

let uu____1592 = (

let uu____1595 = (

let uu____1598 = (

let uu____1599 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1599))
in (uu____1598)::[])
in ((FStar_Format.text name))::uu____1595)
in (FStar_Format.reduce1 uu____1592))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____1609 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____1609))) es)
in (

let docs1 = (

let uu____1615 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens uu____1615))
in docs1))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = (match ((Prims.op_disEquality e.FStar_Extraction_ML_Syntax.loc FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____1630 = (

let uu____1633 = (

let uu____1636 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____1636)::[])
in (FStar_Format.hardline)::uu____1633)
in (FStar_Format.reduce uu____1630))
end
| uu____1637 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____1646 = (

let uu____1647 = (

let uu____1650 = (

let uu____1653 = (

let uu____1656 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____1656)::[])
in (doc1)::uu____1653)
in (pre)::uu____1650)
in (FStar_Format.combine FStar_Format.hardline uu____1647))
in (FStar_Format.parens uu____1646)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1666)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1668; FStar_Extraction_ML_Syntax.loc = uu____1669})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1671))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1673; FStar_Extraction_ML_Syntax.loc = uu____1674})::[]) when (

let uu____1709 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____1709 "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1732; FStar_Extraction_ML_Syntax.loc = uu____1733}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1735; FStar_Extraction_ML_Syntax.loc = uu____1736} when (Prims.op_Equality arg arg') -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1792; FStar_Extraction_ML_Syntax.loc = uu____1793}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1806; FStar_Extraction_ML_Syntax.loc = uu____1807}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1814 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1833 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1833))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1842 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1842) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1845 -> begin
(

let uu____1846 = (

let uu____1849 = (

let uu____1852 = (

let uu____1855 = (

let uu____1856 = (ptsym currentModule f)
in (FStar_Format.text uu____1856))
in (uu____1855)::[])
in ((FStar_Format.text "."))::uu____1852)
in (e2)::uu____1849)
in (FStar_Format.reduce uu____1846))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1886 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1886) with
| true -> begin
(

let uu____1887 = (

let uu____1890 = (

let uu____1893 = (

let uu____1896 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1898 = (

let uu____1901 = (

let uu____1904 = (doc_of_mltype currentModule outer xxt)
in (uu____1904)::[])
in ((FStar_Format.text " : "))::uu____1901)
in (FStar_Format.reduce1 uu____1898))
end
| uu____1905 -> begin
(FStar_Format.text "")
end)
in (uu____1896)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1893)
in ((FStar_Format.text "("))::uu____1890)
in (FStar_Format.reduce1 uu____1887))
end
| uu____1908 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1919 -> (match (uu____1919) with
| (x, xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1932 = (

let uu____1935 = (

let uu____1938 = (FStar_Format.reduce1 ids1)
in (uu____1938)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1935)
in (FStar_Format.reduce1 uu____1932))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1949 = (

let uu____1952 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1953 = (

let uu____1956 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1956)::((FStar_Format.text "end"))::[])
in (uu____1952)::uu____1953))
in (FStar_Format.combine FStar_Format.hardline uu____1949))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1972 = (

let uu____1975 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1976 = (

let uu____1979 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1984 = (

let uu____1987 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1988 = (

let uu____1991 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1991)::((FStar_Format.text "end"))::[])
in (uu____1987)::uu____1988))
in (uu____1979)::uu____1984))
in (uu____1975)::uu____1976))
in (FStar_Format.combine FStar_Format.hardline uu____1972))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____2029 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____2029)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____2034 = (

let uu____2037 = (

let uu____2040 = (

let uu____2041 = (ptctor currentModule exn)
in (FStar_Format.text uu____2041))
in (uu____2040)::[])
in ((FStar_Format.text "raise"))::uu____2037)
in (FStar_Format.reduce1 uu____2034))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____2055 = (

let uu____2058 = (

let uu____2061 = (

let uu____2062 = (ptctor currentModule exn)
in (FStar_Format.text uu____2062))
in (

let uu____2063 = (

let uu____2066 = (

let uu____2067 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____2067))
in (uu____2066)::[])
in (uu____2061)::uu____2063))
in ((FStar_Format.text "raise"))::uu____2058)
in (FStar_Format.reduce1 uu____2055)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____2090 = (

let uu____2093 = (

let uu____2096 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2101 = (

let uu____2104 = (

let uu____2107 = (

let uu____2108 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____2108))
in (uu____2107)::[])
in ((FStar_Format.text "with"))::uu____2104)
in (uu____2096)::uu____2101))
in ((FStar_Format.text "try"))::uu____2093)
in (FStar_Format.combine FStar_Format.hardline uu____2090))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(doc_of_expr currentModule outer head1)
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____2121 = (

let uu____2132 = (as_bin_op p)
in (FStar_Option.get uu____2132))
in (match (uu____2121) with
| (uu____2155, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____2180 = (

let uu____2185 = (as_uni_op p)
in (FStar_Option.get uu____2185))
in (match (uu____2180) with
| (uu____2196, txt) -> begin
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

let uu____2207 = (string_of_mlconstant c)
in (FStar_Format.text uu____2207))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____2236 -> (match (uu____2236) with
| (name, p) -> begin
(

let uu____2243 = (

let uu____2246 = (

let uu____2247 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____2247))
in (

let uu____2250 = (

let uu____2253 = (

let uu____2256 = (doc_of_pattern currentModule p)
in (uu____2256)::[])
in ((FStar_Format.text "="))::uu____2253)
in (uu____2246)::uu____2250))
in (FStar_Format.reduce1 uu____2243))
end))
in (

let uu____2257 = (

let uu____2258 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2258))
in (FStar_Format.cbrackets uu____2257)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____2269 = (is_standard_constructor ctor)
in (match (uu____2269) with
| true -> begin
(

let uu____2270 = (

let uu____2275 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2275))
in (FStar_Pervasives_Native.snd uu____2270))
end
| uu____2286 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____2294 = (is_standard_constructor ctor)
in (match (uu____2294) with
| true -> begin
(

let uu____2295 = (

let uu____2300 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2300))
in (FStar_Pervasives_Native.snd uu____2295))
end
| uu____2311 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____2319 = (

let uu____2322 = (

let uu____2323 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____2323))
in (

let uu____2324 = (

let uu____2327 = (

let uu____2330 = (doc_of_pattern currentModule xs)
in (uu____2330)::[])
in ((FStar_Format.text "::"))::uu____2327)
in (uu____2322)::uu____2324))
in (FStar_Format.reduce uu____2319))
end
| (uu____2331, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____2332))::[]) -> begin
(

let uu____2337 = (

let uu____2340 = (

let uu____2343 = (

let uu____2344 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____2344))
in (uu____2343)::[])
in ((FStar_Format.text name))::uu____2340)
in (FStar_Format.reduce1 uu____2337))
end
| uu____2345 -> begin
(

let uu____2352 = (

let uu____2355 = (

let uu____2358 = (

let uu____2359 = (

let uu____2360 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____2360))
in (FStar_Format.parens uu____2359))
in (uu____2358)::[])
in ((FStar_Format.text name))::uu____2355)
in (FStar_Format.reduce1 uu____2352))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____2373 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____2373)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____2384 -> (match (uu____2384) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2393 = (

let uu____2396 = (

let uu____2399 = (doc_of_pattern currentModule p)
in (uu____2399)::[])
in ((FStar_Format.text "|"))::uu____2396)
in (FStar_Format.reduce1 uu____2393))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____2406 = (

let uu____2409 = (

let uu____2412 = (doc_of_pattern currentModule p)
in (uu____2412)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____2409)
in (FStar_Format.reduce1 uu____2406)))
end)
in (

let uu____2413 = (

let uu____2416 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____2417 = (

let uu____2420 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2420)::((FStar_Format.text "end"))::[])
in (uu____2416)::uu____2417))
in (FStar_Format.combine FStar_Format.hardline uu____2413)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____2426 -> (match (uu____2426) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____2447 -> (match (uu____2447) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2450; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = uu____2452; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____2465 -> begin
(

let uu____2466 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____2466) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____2467)::uu____2468, uu____2469) -> begin
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
| uu____2494 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.None -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty1)::[])))
end
| FStar_Pervasives_Native.Some (vs, ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (

let vars = (

let uu____2521 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____2521 FStar_Format.reduce1))
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(vars)::((FStar_Format.text "."))::(ty1)::[]))))
end)
end
| uu____2534 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____2535 = (

let uu____2538 = (

let uu____2541 = (FStar_Format.reduce1 ids)
in (uu____2541)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in ((FStar_Format.text name))::uu____2538)
in (FStar_Format.reduce1 uu____2535)))))
end))
in (

let letdoc = (match ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____2543 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____2554 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____2555 -> (match (uu____2555) with
| (lineno, file) -> begin
(

let uu____2558 = (((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (Prims.op_Equality file "<dummy>"))
in (match (uu____2558) with
| true -> begin
FStar_Format.empty
end
| uu____2559 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____2594 -> (match (uu____2594) with
| (uu____2613, x, mangle_opt, tparams, uu____2617, body) -> begin
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
(FStar_Format.text x2)
end
| uu____2635 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (FStar_Format.text x2)) tparams)
in (

let uu____2643 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____2643)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____2671 -> (match (uu____2671) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____2684 = (

let uu____2685 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2685))
in (FStar_Format.cbrackets uu____2684)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____2720 -> (match (uu____2720) with
| (name, tys) -> begin
(

let uu____2745 = (FStar_List.split tys)
in (match (uu____2745) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____2764 -> begin
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

let uu____2794 = (

let uu____2797 = (

let uu____2800 = (

let uu____2801 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____2801))
in (uu____2800)::[])
in (tparams1)::uu____2797)
in (FStar_Format.reduce1 uu____2794))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____2806 = (

let uu____2809 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____2809)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____2806)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2832 = (

let uu____2835 = (

let uu____2838 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____2838)::[])
in ((FStar_Format.text "type"))::uu____2835)
in (FStar_Format.reduce1 uu____2832))
end
| uu____2839 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____2864 = (

let uu____2867 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____2868 = (

let uu____2871 = (doc_of_sig currentModule subsig)
in (

let uu____2872 = (

let uu____2875 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____2875)::[])
in (uu____2871)::uu____2872))
in (uu____2867)::uu____2868))
in (FStar_Format.combine FStar_Format.hardline uu____2864))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____2893 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____2893))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____2895, ty)) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text "val"))::((FStar_Format.text x))::((FStar_Format.text ": "))::(ty1)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (

let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (

let docs1 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs1))))


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

let uu____2967 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____2967))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____2978 = (

let uu____2981 = (

let uu____2984 = (

let uu____2987 = (

let uu____2990 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2990)::[])
in ((FStar_Format.text "="))::uu____2987)
in ((FStar_Format.text "_"))::uu____2984)
in ((FStar_Format.text "let"))::uu____2981)
in (FStar_Format.reduce1 uu____2978))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____3018) -> begin
FStar_Format.empty
end
| uu____3019 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____3030 -> (match (uu____3030) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____3102 -> (match (uu____3102) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____3175 -> (match (uu____3175) with
| (s, uu____3181) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____3208 = (

let uu____3211 = (

let uu____3214 = (

let uu____3217 = (FStar_Format.reduce sub3)
in (uu____3217)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3214)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____3211)
in (FStar_Format.reduce uu____3208))))))))
end))
and for1_mod = (fun istop uu____3220 -> (match (uu____3220) with
| (mod_name1, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name1)
in (

let maybe_open_pervasives = (match (mod_name1) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____3288 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____3299 = (

let uu____3302 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3302) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____3305 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____3308 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____3299))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____3310 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____3321 -> (match (uu____3321) with
| (uu____3326, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____3357 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3357) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____3360 -> begin
[]
end))
in (

let uu____3361 = (

let uu____3364 = (

let uu____3367 = (

let uu____3370 = (

let uu____3373 = (

let uu____3376 = (

let uu____3379 = (FStar_Format.reduce sub3)
in (uu____3379)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3376)
in (FStar_Format.hardline)::uu____3373)
in (FStar_List.append maybe_open_pervasives uu____3370))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____3367))
in (FStar_List.append prefix1 uu____3364))
in (FStar_All.pipe_left FStar_Format.reduce uu____3361))))))))))
end))
in (

let docs = (FStar_List.map (fun uu____3418 -> (match (uu____3418) with
| (x, s, m) -> begin
(

let uu____3468 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____3469 = (for1_mod true ((x), (s), (m)))
in ((uu____3468), (uu____3469))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3504 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____3504 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3520 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____3520 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





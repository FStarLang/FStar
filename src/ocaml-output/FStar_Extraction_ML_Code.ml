
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___65_1119 -> (match (uu___65_1119) with
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
| uu____1195 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1219, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1231, FStar_Const.Int16)) -> begin
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

let uu____1257 = (

let uu____1258 = (FStar_Compiler_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____1258 "\""))
in (Prims.strcat "\"" uu____1257))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____1260 = (

let uu____1261 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____1261 "\""))
in (Prims.strcat "\"" uu____1260))
end
| uu____1262 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____1299 -> begin
s
end))
in (FStar_Format.text (escape_tyvar x)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____1307 = (

let uu____1308 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____1308))
in (FStar_Format.parens uu____1307))
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
| uu____1317 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1323 = (

let uu____1324 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____1324))
in (FStar_Format.parens uu____1323)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____1326 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____1326))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____1328, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____1332 = (

let uu____1333 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____1333))
in (maybe_paren outer t_prio_fun uu____1332))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____1334 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1334) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____1335 -> begin
(FStar_Format.text "Obj.t")
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(FStar_Format.text "unit")
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____1339 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____1339)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1423 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1423) with
| true -> begin
(

let uu____1424 = (FStar_Format.reduce (((FStar_Format.text "Prims.unsafe_coerce "))::(doc1)::[]))
in (FStar_Format.parens uu____1424))
end
| uu____1425 -> begin
(

let uu____1426 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____1426))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs1 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (

let uu____1438 = (FStar_Format.reduce docs1)
in (FStar_Format.parens uu____1438))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____1440 = (string_of_mlconstant c)
in (FStar_Format.text uu____1440))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____1443 = (ptsym currentModule path)
in (FStar_Format.text uu____1443))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____1471 -> (match (uu____1471) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1479 = (

let uu____1482 = (

let uu____1483 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1483))
in (uu____1482)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____1479)))
end))
in (

let uu____1486 = (

let uu____1487 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1487))
in (FStar_Format.cbrackets uu____1486)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____1498 = (is_standard_constructor ctor)
in (match (uu____1498) with
| true -> begin
(

let uu____1499 = (

let uu____1504 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1504))
in (FStar_Pervasives_Native.snd uu____1499))
end
| uu____1515 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____1523 = (is_standard_constructor ctor)
in (match (uu____1523) with
| true -> begin
(

let uu____1524 = (

let uu____1529 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1529))
in (FStar_Pervasives_Native.snd uu____1524))
end
| uu____1540 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____1551, uu____1552) -> begin
(

let uu____1557 = (

let uu____1560 = (

let uu____1563 = (

let uu____1564 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1564))
in (uu____1563)::[])
in ((FStar_Format.text name))::uu____1560)
in (FStar_Format.reduce1 uu____1557))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____1574 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____1574))) es)
in (

let docs1 = (

let uu____1576 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens uu____1576))
in docs1))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = (match ((Prims.op_disEquality e.FStar_Extraction_ML_Syntax.loc FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____1595 = (

let uu____1598 = (

let uu____1601 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____1601)::[])
in (FStar_Format.hardline)::uu____1598)
in (FStar_Format.reduce uu____1595))
end
| uu____1602 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____1607 = (

let uu____1608 = (

let uu____1611 = (

let uu____1614 = (

let uu____1617 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____1617)::[])
in (doc1)::uu____1614)
in (pre)::uu____1611)
in (FStar_Format.combine FStar_Format.hardline uu____1608))
in (FStar_Format.parens uu____1607)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1627)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1629; FStar_Extraction_ML_Syntax.loc = uu____1630})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1632))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1634; FStar_Extraction_ML_Syntax.loc = uu____1635})::[]) when (

let uu____1670 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____1670 "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1693; FStar_Extraction_ML_Syntax.loc = uu____1694}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1696; FStar_Extraction_ML_Syntax.loc = uu____1697} when (Prims.op_Equality arg arg') -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1753; FStar_Extraction_ML_Syntax.loc = uu____1754}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1767; FStar_Extraction_ML_Syntax.loc = uu____1768}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1775 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1786 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1786))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1791 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1791) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1794 -> begin
(

let uu____1795 = (

let uu____1798 = (

let uu____1801 = (

let uu____1804 = (

let uu____1805 = (ptsym currentModule f)
in (FStar_Format.text uu____1805))
in (uu____1804)::[])
in ((FStar_Format.text "."))::uu____1801)
in (e2)::uu____1798)
in (FStar_Format.reduce uu____1795))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1835 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1835) with
| true -> begin
(

let uu____1836 = (

let uu____1839 = (

let uu____1842 = (

let uu____1845 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1847 = (

let uu____1850 = (

let uu____1853 = (doc_of_mltype currentModule outer xxt)
in (uu____1853)::[])
in ((FStar_Format.text " : "))::uu____1850)
in (FStar_Format.reduce1 uu____1847))
end
| uu____1854 -> begin
(FStar_Format.text "")
end)
in (uu____1845)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1842)
in ((FStar_Format.text "("))::uu____1839)
in (FStar_Format.reduce1 uu____1836))
end
| uu____1857 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1868 -> (match (uu____1868) with
| (x, xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1877 = (

let uu____1880 = (

let uu____1883 = (FStar_Format.reduce1 ids1)
in (uu____1883)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1880)
in (FStar_Format.reduce1 uu____1877))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1890 = (

let uu____1893 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1894 = (

let uu____1897 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1897)::((FStar_Format.text "end"))::[])
in (uu____1893)::uu____1894))
in (FStar_Format.combine FStar_Format.hardline uu____1890))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1905 = (

let uu____1908 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1909 = (

let uu____1912 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1913 = (

let uu____1916 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1917 = (

let uu____1920 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1920)::((FStar_Format.text "end"))::[])
in (uu____1916)::uu____1917))
in (uu____1912)::uu____1913))
in (uu____1908)::uu____1909))
in (FStar_Format.combine FStar_Format.hardline uu____1905))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1958 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1958)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1963 = (

let uu____1966 = (

let uu____1969 = (

let uu____1970 = (ptctor currentModule exn)
in (FStar_Format.text uu____1970))
in (uu____1969)::[])
in ((FStar_Format.text "raise"))::uu____1966)
in (FStar_Format.reduce1 uu____1963))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1980 = (

let uu____1983 = (

let uu____1986 = (

let uu____1987 = (ptctor currentModule exn)
in (FStar_Format.text uu____1987))
in (

let uu____1988 = (

let uu____1991 = (

let uu____1992 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1992))
in (uu____1991)::[])
in (uu____1986)::uu____1988))
in ((FStar_Format.text "raise"))::uu____1983)
in (FStar_Format.reduce1 uu____1980)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____2015 = (

let uu____2018 = (

let uu____2021 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2022 = (

let uu____2025 = (

let uu____2028 = (

let uu____2029 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____2029))
in (uu____2028)::[])
in ((FStar_Format.text "with"))::uu____2025)
in (uu____2021)::uu____2022))
in ((FStar_Format.text "try"))::uu____2018)
in (FStar_Format.combine FStar_Format.hardline uu____2015))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(doc_of_expr currentModule outer head1)
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____2050 = (

let uu____2061 = (as_bin_op p)
in (FStar_Option.get uu____2061))
in (match (uu____2050) with
| (uu____2084, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____2101 = (

let uu____2106 = (as_uni_op p)
in (FStar_Option.get uu____2106))
in (match (uu____2101) with
| (uu____2117, txt) -> begin
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

let uu____2124 = (string_of_mlconstant c)
in (FStar_Format.text uu____2124))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____2153 -> (match (uu____2153) with
| (name, p) -> begin
(

let uu____2160 = (

let uu____2163 = (

let uu____2164 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____2164))
in (

let uu____2167 = (

let uu____2170 = (

let uu____2173 = (doc_of_pattern currentModule p)
in (uu____2173)::[])
in ((FStar_Format.text "="))::uu____2170)
in (uu____2163)::uu____2167))
in (FStar_Format.reduce1 uu____2160))
end))
in (

let uu____2174 = (

let uu____2175 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2175))
in (FStar_Format.cbrackets uu____2174)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____2186 = (is_standard_constructor ctor)
in (match (uu____2186) with
| true -> begin
(

let uu____2187 = (

let uu____2192 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2192))
in (FStar_Pervasives_Native.snd uu____2187))
end
| uu____2203 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____2211 = (is_standard_constructor ctor)
in (match (uu____2211) with
| true -> begin
(

let uu____2212 = (

let uu____2217 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2217))
in (FStar_Pervasives_Native.snd uu____2212))
end
| uu____2228 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____2236 = (

let uu____2239 = (

let uu____2240 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____2240))
in (

let uu____2241 = (

let uu____2244 = (

let uu____2247 = (doc_of_pattern currentModule xs)
in (uu____2247)::[])
in ((FStar_Format.text "::"))::uu____2244)
in (uu____2239)::uu____2241))
in (FStar_Format.reduce uu____2236))
end
| (uu____2248, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____2249))::[]) -> begin
(

let uu____2254 = (

let uu____2257 = (

let uu____2260 = (

let uu____2261 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____2261))
in (uu____2260)::[])
in ((FStar_Format.text name))::uu____2257)
in (FStar_Format.reduce1 uu____2254))
end
| uu____2262 -> begin
(

let uu____2269 = (

let uu____2272 = (

let uu____2275 = (

let uu____2276 = (

let uu____2277 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____2277))
in (FStar_Format.parens uu____2276))
in (uu____2275)::[])
in ((FStar_Format.text name))::uu____2272)
in (FStar_Format.reduce1 uu____2269))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____2290 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____2290)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____2301 -> (match (uu____2301) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2310 = (

let uu____2313 = (

let uu____2316 = (doc_of_pattern currentModule p)
in (uu____2316)::[])
in ((FStar_Format.text "|"))::uu____2313)
in (FStar_Format.reduce1 uu____2310))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____2319 = (

let uu____2322 = (

let uu____2325 = (doc_of_pattern currentModule p)
in (uu____2325)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____2322)
in (FStar_Format.reduce1 uu____2319)))
end)
in (

let uu____2326 = (

let uu____2329 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____2330 = (

let uu____2333 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2333)::((FStar_Format.text "end"))::[])
in (uu____2329)::uu____2330))
in (FStar_Format.combine FStar_Format.hardline uu____2326)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____2335 -> (match (uu____2335) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____2356 -> (match (uu____2356) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2359; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = uu____2361; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____2370 -> begin
(

let uu____2371 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____2371) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____2372)::uu____2373, uu____2374) -> begin
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
| uu____2379 -> begin
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

let uu____2386 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____2386 FStar_Format.reduce1))
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(vars)::((FStar_Format.text "."))::(ty1)::[]))))
end)
end
| uu____2397 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____2398 = (

let uu____2401 = (

let uu____2404 = (FStar_Format.reduce1 ids)
in (uu____2404)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in ((FStar_Format.text name))::uu____2401)
in (FStar_Format.reduce1 uu____2398)))))
end))
in (

let letdoc = (match ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____2406 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____2417 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____2418 -> (match (uu____2418) with
| (lineno, file) -> begin
(

let uu____2421 = (((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (Prims.op_Equality file "<dummy>"))
in (match (uu____2421) with
| true -> begin
FStar_Format.empty
end
| uu____2422 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____2457 -> (match (uu____2457) with
| (uu____2476, x, mangle_opt, tparams, uu____2480, body) -> begin
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
| uu____2498 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (FStar_Format.text x2)) tparams)
in (

let uu____2506 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____2506)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____2530 -> (match (uu____2530) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____2539 = (

let uu____2540 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2540))
in (FStar_Format.cbrackets uu____2539)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____2575 -> (match (uu____2575) with
| (name, tys) -> begin
(

let uu____2600 = (FStar_List.split tys)
in (match (uu____2600) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____2619 -> begin
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

let uu____2645 = (

let uu____2648 = (

let uu____2651 = (

let uu____2652 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____2652))
in (uu____2651)::[])
in (tparams1)::uu____2648)
in (FStar_Format.reduce1 uu____2645))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____2657 = (

let uu____2660 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____2660)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____2657)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2665 = (

let uu____2668 = (

let uu____2671 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____2671)::[])
in ((FStar_Format.text "type"))::uu____2668)
in (FStar_Format.reduce1 uu____2665))
end
| uu____2672 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____2697 = (

let uu____2700 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____2701 = (

let uu____2704 = (doc_of_sig currentModule subsig)
in (

let uu____2705 = (

let uu____2708 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____2708)::[])
in (uu____2704)::uu____2705))
in (uu____2700)::uu____2701))
in (FStar_Format.combine FStar_Format.hardline uu____2697))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____2722 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____2722))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____2724, ty)) -> begin
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

let uu____2784 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____2784))
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

let uu____2795 = (

let uu____2798 = (

let uu____2801 = (

let uu____2804 = (

let uu____2807 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2807)::[])
in ((FStar_Format.text "="))::uu____2804)
in ((FStar_Format.text "_"))::uu____2801)
in ((FStar_Format.text "let"))::uu____2798)
in (FStar_Format.reduce1 uu____2795))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2831) -> begin
FStar_Format.empty
end
| uu____2832 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____2843 -> (match (uu____2843) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____2909 -> (match (uu____2909) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____2964 -> (match (uu____2964) with
| (s, uu____2970) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____2991 = (

let uu____2994 = (

let uu____2997 = (

let uu____3000 = (FStar_Format.reduce sub3)
in (uu____3000)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____2997)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____2994)
in (FStar_Format.reduce uu____2991))))))))
end))
and for1_mod = (fun istop uu____3003 -> (match (uu____3003) with
| (mod_name1, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name1)
in (

let maybe_open_pervasives = (match (mod_name1) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____3071 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____3082 = (

let uu____3085 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3085) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____3088 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____3091 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____3082))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____3093 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____3104 -> (match (uu____3104) with
| (uu____3109, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____3134 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3134) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____3137 -> begin
[]
end))
in (

let uu____3138 = (

let uu____3141 = (

let uu____3144 = (

let uu____3147 = (

let uu____3150 = (

let uu____3153 = (

let uu____3156 = (FStar_Format.reduce sub3)
in (uu____3156)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3153)
in (FStar_Format.hardline)::uu____3150)
in (FStar_List.append maybe_open_pervasives uu____3147))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____3144))
in (FStar_List.append prefix1 uu____3141))
in (FStar_All.pipe_left FStar_Format.reduce uu____3138))))))))))
end))
in (

let docs = (FStar_List.map (fun uu____3195 -> (match (uu____3195) with
| (x, s, m) -> begin
(

let uu____3245 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____3246 = (for1_mod true ((x), (s), (m)))
in ((uu____3245), (uu____3246))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3281 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____3281 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3293 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____3293 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





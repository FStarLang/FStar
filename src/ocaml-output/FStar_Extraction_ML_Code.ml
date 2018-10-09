
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
| ([], uu____172) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (Prims.op_Equality x1 x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____195, uu____196) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((Prims.op_Equality ns' currentModule)) with
| true -> begin
[]
end
| uu____224 -> begin
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

let uu____258 = (FStar_Util.first_N cg_len ns)
in (match (uu____258) with
| (pfx, sfx) -> begin
(match ((Prims.op_Equality pfx cg_path)) with
| true -> begin
(

let uu____291 = (

let uu____294 = (

let uu____297 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____297)::[])
in (FStar_List.append pfx uu____294))
in FStar_Pervasives_Native.Some (uu____291))
end
| uu____300 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____303 -> begin
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

let uu____325 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____325) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____330 -> begin
(

let uu____331 = x
in (match (uu____331) with
| (ns, x1) -> begin
(

let uu____338 = (path_of_ns currentModule ns)
in ((uu____338), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____348 = (

let uu____349 = (

let uu____351 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____351))
in (

let uu____353 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____349 uu____353)))
in (match (uu____348) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____356 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____371 -> begin
(

let uu____372 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____372) with
| (p, s) -> begin
(

let uu____379 = (

let uu____382 = (

let uu____385 = (ptsym_of_symbol s)
in (uu____385)::[])
in (FStar_List.append p uu____382))
in (FStar_String.concat "." uu____379))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____396 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____396) with
| (p, s) -> begin
(

let s1 = (

let uu____404 = (

let uu____405 = (

let uu____407 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____407))
in (

let uu____409 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____405 uu____409)))
in (match (uu____404) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____412 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____641 -> (

let op_minus = (

let uu____643 = (

let uu____644 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____644 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____643) with
| true -> begin
"-"
end
| uu____649 -> begin
"~-"
end))
in ((("op_Negation"), ("not")))::((("op_Minus"), (op_minus)))::((("op_Bang"), ("Support.ST.read")))::[]))


let prim_types : 'Auu____668 . unit  ->  'Auu____668 Prims.list = (fun uu____671 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (Prims.op_Equality ns (("Prims")::[])))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____725 -> (match (uu____725) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____770 -> (match (uu____770) with
| (y, uu____782, uu____783) -> begin
(Prims.op_Equality x y)
end)) infix_prim_ops)
end
| uu____792 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____808 = (as_bin_op p)
in (Prims.op_disEquality uu____808 FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____853 -> (match (uu____853) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(

let uu____872 = (prim_uni_ops ())
in (FStar_List.tryFind (fun uu____886 -> (match (uu____886) with
| (y, uu____892) -> begin
(Prims.op_Equality x y)
end)) uu____872))
end
| uu____893 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____903 = (as_uni_op p)
in (Prims.op_disEquality uu____903 FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____935 -> (match (uu____935) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____961 -> (match (uu____961) with
| (y, uu____967) -> begin
(Prims.op_Equality x y)
end)) prim_constructors)
end
| uu____968 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____978 = (as_standard_constructor p)
in (Prims.op_disEquality uu____978 FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____1019 inner doc1 -> (match (uu____1019) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____1076 = _inner
in (match (uu____1076) with
| (pi, fi) -> begin
(

let uu____1083 = _outer
in (match (uu____1083) with
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
| (uu____1090, NonAssoc) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fi fo))
end
| (uu____1091, uu____1092) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____1093 -> begin
(FStar_Format.parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_BaseTypes.char  ->  Prims.string)  ->  FStar_BaseTypes.char  ->  Prims.string = (fun fallback uu___273_1120 -> if (Prims.op_Equality uu___273_1120 92 (*\*)) then begin
"\\\\"
end else begin
if (Prims.op_Equality uu___273_1120 32 (* *)) then begin
" "
end else begin
if (Prims.op_Equality uu___273_1120 8) then begin
"\\b"
end else begin
if (Prims.op_Equality uu___273_1120 9) then begin
"\\t"
end else begin
if (Prims.op_Equality uu___273_1120 13) then begin
"\\r"
end else begin
if (Prims.op_Equality uu___273_1120 10) then begin
"\\n"
end else begin
if (Prims.op_Equality uu___273_1120 39 (*'*)) then begin
"\\\'"
end else begin
if (Prims.op_Equality uu___273_1120 34) then begin
"\\\""
end else begin
if (FStar_Util.is_letter_or_digit uu___273_1120) then begin
(FStar_Util.string_of_char uu___273_1120)
end else begin
if (FStar_Util.is_punctuation uu___273_1120) then begin
(FStar_Util.string_of_char uu___273_1120)
end else begin
if (FStar_Util.is_symbol uu___273_1120) then begin
(FStar_Util.string_of_char uu___273_1120)
end else begin
(fallback uu___273_1120)
end
end
end
end
end
end
end
end
end
end
end)


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

let uu____1149 = (FStar_Util.string_of_int nc)
in (Prims.strcat uu____1149 (match ((((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127"))) && (Prims.op_disEquality nc (Prims.parse_int "34")))) with
| true -> begin
(Prims.strcat " (*" (Prims.strcat (FStar_Util.string_of_char c) "*)"))
end
| uu____1172 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1196, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1208, FStar_Const.Int16)) -> begin
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

let uu____1234 = (

let uu____1235 = (FStar_Compiler_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____1235 "\""))
in (Prims.strcat "\"" uu____1234))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____1237 = (

let uu____1238 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____1238 "\""))
in (Prims.strcat "\"" uu____1237))
end
| uu____1239 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____1276 -> begin
s
end))
in (FStar_Format.text (escape_tyvar x)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____1284 = (

let uu____1285 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____1285))
in (FStar_Format.parens uu____1284))
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
| uu____1294 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1300 = (

let uu____1301 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____1301))
in (FStar_Format.parens uu____1300)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____1303 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____1303))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____1305, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____1309 = (

let uu____1310 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____1310))
in (maybe_paren outer t_prio_fun uu____1309))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____1311 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1311) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____1312 -> begin
(FStar_Format.text "Obj.t")
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(FStar_Format.text "unit")
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____1316 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____1316)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1400 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1400) with
| true -> begin
(

let uu____1401 = (FStar_Format.reduce (((FStar_Format.text "Prims.unsafe_coerce "))::(doc1)::[]))
in (FStar_Format.parens uu____1401))
end
| uu____1402 -> begin
(

let uu____1403 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____1403))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs1 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (

let uu____1415 = (FStar_Format.reduce docs1)
in (FStar_Format.parens uu____1415))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____1417 = (string_of_mlconstant c)
in (FStar_Format.text uu____1417))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____1420 = (ptsym currentModule path)
in (FStar_Format.text uu____1420))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____1448 -> (match (uu____1448) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1456 = (

let uu____1459 = (

let uu____1460 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1460))
in (uu____1459)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____1456)))
end))
in (

let uu____1463 = (

let uu____1464 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1464))
in (FStar_Format.cbrackets uu____1463)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____1475 = (is_standard_constructor ctor)
in (match (uu____1475) with
| true -> begin
(

let uu____1476 = (

let uu____1481 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1481))
in (FStar_Pervasives_Native.snd uu____1476))
end
| uu____1492 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____1500 = (is_standard_constructor ctor)
in (match (uu____1500) with
| true -> begin
(

let uu____1501 = (

let uu____1506 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1506))
in (FStar_Pervasives_Native.snd uu____1501))
end
| uu____1517 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____1528, uu____1529) -> begin
(

let uu____1534 = (

let uu____1537 = (

let uu____1540 = (

let uu____1541 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1541))
in (uu____1540)::[])
in ((FStar_Format.text name))::uu____1537)
in (FStar_Format.reduce1 uu____1534))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____1551 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____1551))) es)
in (

let docs1 = (

let uu____1553 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens uu____1553))
in docs1))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = (match ((Prims.op_disEquality e.FStar_Extraction_ML_Syntax.loc FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____1568 = (

let uu____1571 = (

let uu____1574 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____1574)::[])
in (FStar_Format.hardline)::uu____1571)
in (FStar_Format.reduce uu____1568))
end
| uu____1575 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____1580 = (

let uu____1581 = (

let uu____1584 = (

let uu____1587 = (

let uu____1590 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____1590)::[])
in (doc1)::uu____1587)
in (pre)::uu____1584)
in (FStar_Format.combine FStar_Format.hardline uu____1581))
in (FStar_Format.parens uu____1580)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1600)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1602; FStar_Extraction_ML_Syntax.loc = uu____1603})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1605))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1607; FStar_Extraction_ML_Syntax.loc = uu____1608})::[]) when (

let uu____1643 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____1643 "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1666; FStar_Extraction_ML_Syntax.loc = uu____1667}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1669; FStar_Extraction_ML_Syntax.loc = uu____1670} when (Prims.op_Equality arg arg') -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1726; FStar_Extraction_ML_Syntax.loc = uu____1727}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1740; FStar_Extraction_ML_Syntax.loc = uu____1741}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1748 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1759 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1759))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1764 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1764) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1767 -> begin
(

let uu____1768 = (

let uu____1771 = (

let uu____1774 = (

let uu____1777 = (

let uu____1778 = (ptsym currentModule f)
in (FStar_Format.text uu____1778))
in (uu____1777)::[])
in ((FStar_Format.text "."))::uu____1774)
in (e2)::uu____1771)
in (FStar_Format.reduce uu____1768))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1808 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1808) with
| true -> begin
(

let uu____1809 = (

let uu____1812 = (

let uu____1815 = (

let uu____1818 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1820 = (

let uu____1823 = (

let uu____1826 = (doc_of_mltype currentModule outer xxt)
in (uu____1826)::[])
in ((FStar_Format.text " : "))::uu____1823)
in (FStar_Format.reduce1 uu____1820))
end
| uu____1827 -> begin
(FStar_Format.text "")
end)
in (uu____1818)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1815)
in ((FStar_Format.text "("))::uu____1812)
in (FStar_Format.reduce1 uu____1809))
end
| uu____1830 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1841 -> (match (uu____1841) with
| (x, xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1850 = (

let uu____1853 = (

let uu____1856 = (FStar_Format.reduce1 ids1)
in (uu____1856)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1853)
in (FStar_Format.reduce1 uu____1850))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1863 = (

let uu____1866 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1867 = (

let uu____1870 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1870)::((FStar_Format.text "end"))::[])
in (uu____1866)::uu____1867))
in (FStar_Format.combine FStar_Format.hardline uu____1863))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1878 = (

let uu____1881 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1882 = (

let uu____1885 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1886 = (

let uu____1889 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1890 = (

let uu____1893 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1893)::((FStar_Format.text "end"))::[])
in (uu____1889)::uu____1890))
in (uu____1885)::uu____1886))
in (uu____1881)::uu____1882))
in (FStar_Format.combine FStar_Format.hardline uu____1878))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1931 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1931)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1936 = (

let uu____1939 = (

let uu____1942 = (

let uu____1943 = (ptctor currentModule exn)
in (FStar_Format.text uu____1943))
in (uu____1942)::[])
in ((FStar_Format.text "raise"))::uu____1939)
in (FStar_Format.reduce1 uu____1936))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1953 = (

let uu____1956 = (

let uu____1959 = (

let uu____1960 = (ptctor currentModule exn)
in (FStar_Format.text uu____1960))
in (

let uu____1961 = (

let uu____1964 = (

let uu____1965 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1965))
in (uu____1964)::[])
in (uu____1959)::uu____1961))
in ((FStar_Format.text "raise"))::uu____1956)
in (FStar_Format.reduce1 uu____1953)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1988 = (

let uu____1991 = (

let uu____1994 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1995 = (

let uu____1998 = (

let uu____2001 = (

let uu____2002 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____2002))
in (uu____2001)::[])
in ((FStar_Format.text "with"))::uu____1998)
in (uu____1994)::uu____1995))
in ((FStar_Format.text "try"))::uu____1991)
in (FStar_Format.combine FStar_Format.hardline uu____1988))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(doc_of_expr currentModule outer head1)
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____2023 = (

let uu____2034 = (as_bin_op p)
in (FStar_Option.get uu____2034))
in (match (uu____2023) with
| (uu____2057, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____2074 = (

let uu____2079 = (as_uni_op p)
in (FStar_Option.get uu____2079))
in (match (uu____2074) with
| (uu____2090, txt) -> begin
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

let uu____2097 = (string_of_mlconstant c)
in (FStar_Format.text uu____2097))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____2126 -> (match (uu____2126) with
| (name, p) -> begin
(

let uu____2133 = (

let uu____2136 = (

let uu____2137 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____2137))
in (

let uu____2140 = (

let uu____2143 = (

let uu____2146 = (doc_of_pattern currentModule p)
in (uu____2146)::[])
in ((FStar_Format.text "="))::uu____2143)
in (uu____2136)::uu____2140))
in (FStar_Format.reduce1 uu____2133))
end))
in (

let uu____2147 = (

let uu____2148 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2148))
in (FStar_Format.cbrackets uu____2147)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____2159 = (is_standard_constructor ctor)
in (match (uu____2159) with
| true -> begin
(

let uu____2160 = (

let uu____2165 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2165))
in (FStar_Pervasives_Native.snd uu____2160))
end
| uu____2176 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____2184 = (is_standard_constructor ctor)
in (match (uu____2184) with
| true -> begin
(

let uu____2185 = (

let uu____2190 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2190))
in (FStar_Pervasives_Native.snd uu____2185))
end
| uu____2201 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____2209 = (

let uu____2212 = (

let uu____2213 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____2213))
in (

let uu____2214 = (

let uu____2217 = (

let uu____2220 = (doc_of_pattern currentModule xs)
in (uu____2220)::[])
in ((FStar_Format.text "::"))::uu____2217)
in (uu____2212)::uu____2214))
in (FStar_Format.reduce uu____2209))
end
| (uu____2221, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____2222))::[]) -> begin
(

let uu____2227 = (

let uu____2230 = (

let uu____2233 = (

let uu____2234 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____2234))
in (uu____2233)::[])
in ((FStar_Format.text name))::uu____2230)
in (FStar_Format.reduce1 uu____2227))
end
| uu____2235 -> begin
(

let uu____2242 = (

let uu____2245 = (

let uu____2248 = (

let uu____2249 = (

let uu____2250 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____2250))
in (FStar_Format.parens uu____2249))
in (uu____2248)::[])
in ((FStar_Format.text name))::uu____2245)
in (FStar_Format.reduce1 uu____2242))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____2263 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____2263)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____2274 -> (match (uu____2274) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2283 = (

let uu____2286 = (

let uu____2289 = (doc_of_pattern currentModule p)
in (uu____2289)::[])
in ((FStar_Format.text "|"))::uu____2286)
in (FStar_Format.reduce1 uu____2283))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____2292 = (

let uu____2295 = (

let uu____2298 = (doc_of_pattern currentModule p)
in (uu____2298)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____2295)
in (FStar_Format.reduce1 uu____2292)))
end)
in (

let uu____2299 = (

let uu____2302 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____2303 = (

let uu____2306 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2306)::((FStar_Format.text "end"))::[])
in (uu____2302)::uu____2303))
in (FStar_Format.combine FStar_Format.hardline uu____2299)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____2308 -> (match (uu____2308) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____2329 -> (match (uu____2329) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2332; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = uu____2334; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____2343 -> begin
(

let uu____2344 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____2344) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____2345)::uu____2346, uu____2347) -> begin
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
| uu____2352 -> begin
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

let uu____2359 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____2359 FStar_Format.reduce1))
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(vars)::((FStar_Format.text "."))::(ty1)::[]))))
end)
end
| uu____2370 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____2371 = (

let uu____2374 = (

let uu____2377 = (FStar_Format.reduce1 ids)
in (uu____2377)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in ((FStar_Format.text name))::uu____2374)
in (FStar_Format.reduce1 uu____2371)))))
end))
in (

let letdoc = (match ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____2379 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____2390 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____2391 -> (match (uu____2391) with
| (lineno, file) -> begin
(

let uu____2394 = (((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (Prims.op_Equality file "<dummy>"))
in (match (uu____2394) with
| true -> begin
FStar_Format.empty
end
| uu____2395 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____2430 -> (match (uu____2430) with
| (uu____2449, x, mangle_opt, tparams, uu____2453, body) -> begin
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
| uu____2471 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (FStar_Format.text x2)) tparams)
in (

let uu____2479 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____2479)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____2503 -> (match (uu____2503) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____2512 = (

let uu____2513 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2513))
in (FStar_Format.cbrackets uu____2512)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____2548 -> (match (uu____2548) with
| (name, tys) -> begin
(

let uu____2573 = (FStar_List.split tys)
in (match (uu____2573) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____2592 -> begin
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

let uu____2618 = (

let uu____2621 = (

let uu____2624 = (

let uu____2625 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____2625))
in (uu____2624)::[])
in (tparams1)::uu____2621)
in (FStar_Format.reduce1 uu____2618))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____2630 = (

let uu____2633 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____2633)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____2630)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2638 = (

let uu____2641 = (

let uu____2644 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____2644)::[])
in ((FStar_Format.text "type"))::uu____2641)
in (FStar_Format.reduce1 uu____2638))
end
| uu____2645 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____2670 = (

let uu____2673 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____2674 = (

let uu____2677 = (doc_of_sig currentModule subsig)
in (

let uu____2678 = (

let uu____2681 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____2681)::[])
in (uu____2677)::uu____2678))
in (uu____2673)::uu____2674))
in (FStar_Format.combine FStar_Format.hardline uu____2670))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____2695 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____2695))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____2697, ty)) -> begin
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

let uu____2757 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____2757))
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

let uu____2768 = (

let uu____2771 = (

let uu____2774 = (

let uu____2777 = (

let uu____2780 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2780)::[])
in ((FStar_Format.text "="))::uu____2777)
in ((FStar_Format.text "_"))::uu____2774)
in ((FStar_Format.text "let"))::uu____2771)
in (FStar_Format.reduce1 uu____2768))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2804) -> begin
FStar_Format.empty
end
| uu____2805 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____2816 -> (match (uu____2816) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____2882 -> (match (uu____2882) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____2937 -> (match (uu____2937) with
| (s, uu____2943) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____2964 = (

let uu____2967 = (

let uu____2970 = (

let uu____2973 = (FStar_Format.reduce sub3)
in (uu____2973)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____2970)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____2967)
in (FStar_Format.reduce uu____2964))))))))
end))
and for1_mod = (fun istop uu____2976 -> (match (uu____2976) with
| (mod_name1, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name1)
in (

let maybe_open_pervasives = (match (mod_name1) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____3044 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____3055 = (

let uu____3058 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3058) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____3061 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____3064 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____3055))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____3066 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____3077 -> (match (uu____3077) with
| (uu____3082, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____3107 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3107) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____3110 -> begin
[]
end))
in (

let uu____3111 = (

let uu____3114 = (

let uu____3117 = (

let uu____3120 = (

let uu____3123 = (

let uu____3126 = (

let uu____3129 = (FStar_Format.reduce sub3)
in (uu____3129)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3126)
in (FStar_Format.hardline)::uu____3123)
in (FStar_List.append maybe_open_pervasives uu____3120))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____3117))
in (FStar_List.append prefix1 uu____3114))
in (FStar_All.pipe_left FStar_Format.reduce uu____3111))))))))))
end))
in (

let docs = (FStar_List.map (fun uu____3168 -> (match (uu____3168) with
| (x, s, m) -> begin
(

let uu____3218 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____3219 = (for1_mod true ((x), (s), (m)))
in ((uu____3218), (uu____3219))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3254 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____3254 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3266 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____3266 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





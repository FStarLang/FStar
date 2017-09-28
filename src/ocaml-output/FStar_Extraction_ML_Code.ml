
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
| uu____5 -> begin
false
end))


let uu___is_IRight : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IRight -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_Left : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____15 -> begin
false
end))


let uu___is_Right : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_NonAssoc : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____25 -> begin
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
| uu____34 -> begin
false
end))


let uu___is_Postfix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Postfix -> begin
true
end
| uu____39 -> begin
false
end))


let uu___is_Infix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
true
end
| uu____45 -> begin
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
| ([], uu____163) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (Prims.op_Equality x1 x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____186, uu____187) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((Prims.op_Equality ns' currentModule)) with
| true -> begin
[]
end
| uu____213 -> begin
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

let uu____247 = (FStar_Util.first_N cg_len ns)
in (match (uu____247) with
| (pfx, sfx) -> begin
(match ((Prims.op_Equality pfx cg_path)) with
| true -> begin
(

let uu____280 = (

let uu____283 = (

let uu____286 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____286)::[])
in (FStar_List.append pfx uu____283))
in FStar_Pervasives_Native.Some (uu____280))
end
| uu____289 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____292 -> begin
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

let uu____312 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____312) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____317 -> begin
(

let uu____318 = x
in (match (uu____318) with
| (ns, x1) -> begin
(

let uu____325 = (path_of_ns currentModule ns)
in ((uu____325), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____334 = (

let uu____335 = (

let uu____336 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____336))
in (

let uu____337 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____335 uu____337)))
in (match (uu____334) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____338 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____351 -> begin
(

let uu____352 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____352) with
| (p, s) -> begin
(

let uu____359 = (

let uu____362 = (

let uu____365 = (ptsym_of_symbol s)
in (uu____365)::[])
in (FStar_List.append p uu____362))
in (FStar_String.concat "." uu____359))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____374 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____374) with
| (p, s) -> begin
(

let s1 = (

let uu____382 = (

let uu____383 = (

let uu____384 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____384))
in (

let uu____385 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____383 uu____385)))
in (match (uu____382) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____386 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types : 'Auu____629 . Prims.unit  ->  'Auu____629 Prims.list = (fun uu____632 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (Prims.op_Equality ns (("Prims")::[])))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____684 -> (match (uu____684) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____729 -> (match (uu____729) with
| (y, uu____741, uu____742) -> begin
(Prims.op_Equality x y)
end)) infix_prim_ops)
end
| uu____751 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____766 = (as_bin_op p)
in (Prims.op_disEquality uu____766 FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____810 -> (match (uu____810) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____836 -> (match (uu____836) with
| (y, uu____842) -> begin
(Prims.op_Equality x y)
end)) prim_uni_ops)
end
| uu____843 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____852 = (as_uni_op p)
in (Prims.op_disEquality uu____852 FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____882 -> (match (uu____882) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____908 -> (match (uu____908) with
| (y, uu____914) -> begin
(Prims.op_Equality x y)
end)) prim_constructors)
end
| uu____915 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____924 = (as_standard_constructor p)
in (Prims.op_disEquality uu____924 FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____962 inner doc1 -> (match (uu____962) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____1013 = _inner
in (match (uu____1013) with
| (pi, fi) -> begin
(

let uu____1020 = _outer
in (match (uu____1020) with
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
| (uu____1027, NonAssoc) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fi fo))
end
| (uu____1028, uu____1029) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____1030 -> begin
(FStar_Format.parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___126_1049 -> (match (uu___126_1049) with
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

let uu____1070 = (FStar_Util.string_of_int nc)
in (Prims.strcat uu____1070 (match ((((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127"))) && (Prims.op_disEquality nc (Prims.parse_int "34")))) with
| true -> begin
(Prims.strcat " (*" (Prims.strcat (FStar_Util.string_of_char c) "*)"))
end
| uu____1115 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1139, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1151, FStar_Const.Int16)) -> begin
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

let uu____1177 = (

let uu____1178 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____1178 "\""))
in (Prims.strcat "\"" uu____1177))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____1180 = (

let uu____1181 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____1181 "\""))
in (Prims.strcat "\"" uu____1180))
end
| uu____1182 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____1203 -> begin
s
end))
in (FStar_Format.text (escape_tyvar x)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____1215 = (

let uu____1216 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____1216))
in (FStar_Format.parens uu____1215))
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
| uu____1229 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1239 = (

let uu____1240 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____1240))
in (FStar_Format.parens uu____1239)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____1242 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____1242))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____1244, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____1256 = (

let uu____1257 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____1257))
in (maybe_paren outer t_prio_fun uu____1256))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____1258 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1258) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____1259 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____1263 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____1263)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1317 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1317) with
| true -> begin
(

let uu____1318 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc1)::[]))
in (FStar_Format.parens uu____1318))
end
| uu____1319 -> begin
(

let uu____1320 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____1320))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs2 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs1)
in (

let uu____1336 = (FStar_Format.reduce docs2)
in (FStar_Format.parens uu____1336))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____1338 = (string_of_mlconstant c)
in (FStar_Format.text uu____1338))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____1341 = (ptsym currentModule path)
in (FStar_Format.text uu____1341))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____1367 -> (match (uu____1367) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1379 = (

let uu____1382 = (

let uu____1383 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1383))
in (uu____1382)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____1379)))
end))
in (

let uu____1386 = (

let uu____1387 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1387))
in (FStar_Format.cbrackets uu____1386)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____1398 = (is_standard_constructor ctor)
in (match (uu____1398) with
| true -> begin
(

let uu____1399 = (

let uu____1404 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1404))
in (FStar_Pervasives_Native.snd uu____1399))
end
| uu____1415 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____1423 = (is_standard_constructor ctor)
in (match (uu____1423) with
| true -> begin
(

let uu____1424 = (

let uu____1429 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1429))
in (FStar_Pervasives_Native.snd uu____1424))
end
| uu____1440 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____1455, uu____1456) -> begin
(

let uu____1461 = (

let uu____1464 = (

let uu____1467 = (

let uu____1468 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1468))
in (uu____1467)::[])
in ((FStar_Format.text name))::uu____1464)
in (FStar_Format.reduce1 uu____1461))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs1 = (FStar_List.map (fun x -> (

let uu____1478 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____1478))) es)
in (

let docs2 = (

let uu____1484 = (FStar_Format.combine (FStar_Format.text ", ") docs1)
in (FStar_Format.parens uu____1484))
in docs2))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____1486, lets), body) -> begin
(

let pre = (match ((Prims.op_disEquality e.FStar_Extraction_ML_Syntax.loc FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____1502 = (

let uu____1505 = (

let uu____1508 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____1508)::[])
in (FStar_Format.hardline)::uu____1505)
in (FStar_Format.reduce uu____1502))
end
| uu____1509 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____1518 = (

let uu____1519 = (

let uu____1522 = (

let uu____1525 = (

let uu____1528 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____1528)::[])
in (doc1)::uu____1525)
in (pre)::uu____1522)
in (FStar_Format.combine FStar_Format.hardline uu____1519))
in (FStar_Format.parens uu____1518)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1538)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1540; FStar_Extraction_ML_Syntax.loc = uu____1541})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1543))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1545; FStar_Extraction_ML_Syntax.loc = uu____1546})::[]) when (

let uu____1581 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____1581 "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1604; FStar_Extraction_ML_Syntax.loc = uu____1605}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1607; FStar_Extraction_ML_Syntax.loc = uu____1608} when (Prims.op_Equality arg arg') -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1664; FStar_Extraction_ML_Syntax.loc = uu____1665}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1678; FStar_Extraction_ML_Syntax.loc = uu____1679}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1686 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1705 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1705))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1714 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1714) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1717 -> begin
(

let uu____1718 = (

let uu____1721 = (

let uu____1724 = (

let uu____1727 = (

let uu____1728 = (ptsym currentModule f)
in (FStar_Format.text uu____1728))
in (uu____1727)::[])
in ((FStar_Format.text "."))::uu____1724)
in (e2)::uu____1721)
in (FStar_Format.reduce uu____1718))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1754 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1754) with
| true -> begin
(

let uu____1755 = (

let uu____1758 = (

let uu____1761 = (

let uu____1764 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1766 = (

let uu____1769 = (

let uu____1772 = (doc_of_mltype currentModule outer xxt)
in (uu____1772)::[])
in ((FStar_Format.text " : "))::uu____1769)
in (FStar_Format.reduce1 uu____1766))
end
| uu____1773 -> begin
(FStar_Format.text "")
end)
in (uu____1764)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1761)
in ((FStar_Format.text "("))::uu____1758)
in (FStar_Format.reduce1 uu____1755))
end
| uu____1776 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1787 -> (match (uu____1787) with
| (x, xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1800 = (

let uu____1803 = (

let uu____1806 = (FStar_Format.reduce1 ids1)
in (uu____1806)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1803)
in (FStar_Format.reduce1 uu____1800))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1817 = (

let uu____1820 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1821 = (

let uu____1824 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1824)::((FStar_Format.text "end"))::[])
in (uu____1820)::uu____1821))
in (FStar_Format.combine FStar_Format.hardline uu____1817))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1840 = (

let uu____1843 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1844 = (

let uu____1847 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1852 = (

let uu____1855 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1856 = (

let uu____1859 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1859)::((FStar_Format.text "end"))::[])
in (uu____1855)::uu____1856))
in (uu____1847)::uu____1852))
in (uu____1843)::uu____1844))
in (FStar_Format.combine FStar_Format.hardline uu____1840))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1897 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1897)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1902 = (

let uu____1905 = (

let uu____1908 = (

let uu____1909 = (ptctor currentModule exn)
in (FStar_Format.text uu____1909))
in (uu____1908)::[])
in ((FStar_Format.text "raise"))::uu____1905)
in (FStar_Format.reduce1 uu____1902))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1923 = (

let uu____1926 = (

let uu____1929 = (

let uu____1930 = (ptctor currentModule exn)
in (FStar_Format.text uu____1930))
in (

let uu____1931 = (

let uu____1934 = (

let uu____1935 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1935))
in (uu____1934)::[])
in (uu____1929)::uu____1931))
in ((FStar_Format.text "raise"))::uu____1926)
in (FStar_Format.reduce1 uu____1923)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1958 = (

let uu____1961 = (

let uu____1964 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1969 = (

let uu____1972 = (

let uu____1975 = (

let uu____1976 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1976))
in (uu____1975)::[])
in ((FStar_Format.text "with"))::uu____1972)
in (uu____1964)::uu____1969))
in ((FStar_Format.text "try"))::uu____1961)
in (FStar_Format.combine FStar_Format.hardline uu____1958))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(doc_of_expr currentModule outer head1)
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1989 = (

let uu____2000 = (as_bin_op p)
in (FStar_Option.get uu____2000))
in (match (uu____1989) with
| (uu____2023, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____2048 = (

let uu____2053 = (as_uni_op p)
in (FStar_Option.get uu____2053))
in (match (uu____2048) with
| (uu____2064, txt) -> begin
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

let uu____2075 = (string_of_mlconstant c)
in (FStar_Format.text uu____2075))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____2102 -> (match (uu____2102) with
| (name, p) -> begin
(

let uu____2109 = (

let uu____2112 = (

let uu____2113 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____2113))
in (

let uu____2116 = (

let uu____2119 = (

let uu____2122 = (doc_of_pattern currentModule p)
in (uu____2122)::[])
in ((FStar_Format.text "="))::uu____2119)
in (uu____2112)::uu____2116))
in (FStar_Format.reduce1 uu____2109))
end))
in (

let uu____2123 = (

let uu____2124 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2124))
in (FStar_Format.cbrackets uu____2123)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____2135 = (is_standard_constructor ctor)
in (match (uu____2135) with
| true -> begin
(

let uu____2136 = (

let uu____2141 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2141))
in (FStar_Pervasives_Native.snd uu____2136))
end
| uu____2152 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____2160 = (is_standard_constructor ctor)
in (match (uu____2160) with
| true -> begin
(

let uu____2161 = (

let uu____2166 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2166))
in (FStar_Pervasives_Native.snd uu____2161))
end
| uu____2177 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____2185 = (

let uu____2188 = (

let uu____2189 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____2189))
in (

let uu____2190 = (

let uu____2193 = (

let uu____2196 = (doc_of_pattern currentModule xs)
in (uu____2196)::[])
in ((FStar_Format.text "::"))::uu____2193)
in (uu____2188)::uu____2190))
in (FStar_Format.reduce uu____2185))
end
| (uu____2197, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____2198))::[]) -> begin
(

let uu____2203 = (

let uu____2206 = (

let uu____2209 = (

let uu____2210 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____2210))
in (uu____2209)::[])
in ((FStar_Format.text name))::uu____2206)
in (FStar_Format.reduce1 uu____2203))
end
| uu____2211 -> begin
(

let uu____2218 = (

let uu____2221 = (

let uu____2224 = (

let uu____2225 = (

let uu____2226 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____2226))
in (FStar_Format.parens uu____2225))
in (uu____2224)::[])
in ((FStar_Format.text name))::uu____2221)
in (FStar_Format.reduce1 uu____2218))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____2239 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____2239)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____2250 -> (match (uu____2250) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2259 = (

let uu____2262 = (

let uu____2265 = (doc_of_pattern currentModule p)
in (uu____2265)::[])
in ((FStar_Format.text "|"))::uu____2262)
in (FStar_Format.reduce1 uu____2259))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____2272 = (

let uu____2275 = (

let uu____2278 = (doc_of_pattern currentModule p)
in (uu____2278)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____2275)
in (FStar_Format.reduce1 uu____2272)))
end)
in (

let uu____2279 = (

let uu____2282 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____2283 = (

let uu____2286 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2286)::((FStar_Format.text "end"))::[])
in (uu____2282)::uu____2283))
in (FStar_Format.combine FStar_Format.hardline uu____2279)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____2292 -> (match (uu____2292) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____2311 -> (match (uu____2311) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2314; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____2328 -> begin
(

let uu____2329 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____2329) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____2330)::uu____2331, uu____2332) -> begin
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
| uu____2357 -> begin
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

let uu____2384 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____2384 FStar_Format.reduce1))
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

let uu____2421 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
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

let for1 = (fun uu____2453 -> (match (uu____2453) with
| (uu____2472, x, mangle_opt, tparams, uu____2476, body) -> begin
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
| uu____2494 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (FStar_Format.text x2)) tparams)
in (

let uu____2502 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____2502)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____2526 -> (match (uu____2526) with
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

let forctor = (fun uu____2573 -> (match (uu____2573) with
| (name, tys) -> begin
(

let uu____2598 = (FStar_List.split tys)
in (match (uu____2598) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____2617 -> begin
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

let uu____2647 = (

let uu____2650 = (

let uu____2653 = (

let uu____2654 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____2654))
in (uu____2653)::[])
in (tparams1)::uu____2650)
in (FStar_Format.reduce1 uu____2647))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____2659 = (

let uu____2662 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____2662)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____2659)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2685 = (

let uu____2688 = (

let uu____2691 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____2691)::[])
in ((FStar_Format.text "type"))::uu____2688)
in (FStar_Format.reduce1 uu____2685))
end
| uu____2692 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____2709 = (

let uu____2712 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____2713 = (

let uu____2716 = (doc_of_sig currentModule subsig)
in (

let uu____2717 = (

let uu____2720 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____2720)::[])
in (uu____2716)::uu____2717))
in (uu____2712)::uu____2713))
in (FStar_Format.combine FStar_Format.hardline uu____2709))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____2738 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____2738))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____2740, ty)) -> begin
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

let uu____2810 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____2810))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____2813, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____2822 = (

let uu____2825 = (

let uu____2828 = (

let uu____2831 = (

let uu____2834 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2834)::[])
in ((FStar_Format.text "="))::uu____2831)
in ((FStar_Format.text "_"))::uu____2828)
in ((FStar_Format.text "let"))::uu____2825)
in (FStar_Format.reduce1 uu____2822))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs1 = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2860) -> begin
FStar_Format.empty
end
| uu____2861 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs1))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____2871 -> (match (uu____2871) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____2937 -> (match (uu____2937) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____3010 -> (match (uu____3010) with
| (s, uu____3016) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____3043 = (

let uu____3046 = (

let uu____3049 = (

let uu____3052 = (FStar_Format.reduce sub3)
in (uu____3052)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3049)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____3046)
in (FStar_Format.reduce uu____3043))))))))
end))
and for1_mod = (fun istop uu____3055 -> (match (uu____3055) with
| (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name)
in (

let maybe_open_pervasives = (match (mod_name) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____3123 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____3134 = (

let uu____3137 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3137) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____3140 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____3143 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____3134))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____3145 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____3156 -> (match (uu____3156) with
| (uu____3161, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____3192 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3192) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____3195 -> begin
[]
end))
in (

let uu____3196 = (

let uu____3199 = (

let uu____3202 = (

let uu____3205 = (

let uu____3208 = (

let uu____3211 = (

let uu____3214 = (FStar_Format.reduce sub3)
in (uu____3214)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3211)
in (FStar_Format.hardline)::uu____3208)
in (FStar_List.append maybe_open_pervasives uu____3205))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____3202))
in (FStar_List.append prefix1 uu____3199))
in (FStar_All.pipe_left FStar_Format.reduce uu____3196))))))))))
end))
in (

let docs1 = (FStar_List.map (fun uu____3253 -> (match (uu____3253) with
| (x, s, m) -> begin
(

let uu____3303 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____3304 = (for1_mod true ((x), (s), (m)))
in ((uu____3303), (uu____3304))))
end)) mllib)
in docs1))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3336 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____3336 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3350 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____3350 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))






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
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____186, uu____187) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
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
(match ((pfx = cg_path)) with
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
in (uu____335 <> uu____337)))
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
in (uu____383 <> uu____385)))
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


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____684 -> (match (uu____684) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____729 -> (match (uu____729) with
| (y, uu____741, uu____742) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____751 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____766 = (as_bin_op p)
in (uu____766 <> FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____810 -> (match (uu____810) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____836 -> (match (uu____836) with
| (y, uu____842) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____843 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____852 = (as_uni_op p)
in (uu____852 <> FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____882 -> (match (uu____882) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____908 -> (match (uu____908) with
| (y, uu____914) -> begin
(x = y)
end)) prim_constructors)
end
| uu____915 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____924 = (as_standard_constructor p)
in (uu____924 <> FStar_Pervasives_Native.None)))


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
| (uu____1027, NonAssoc) -> begin
((pi = po) && (fi = fo))
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___123_1049 -> (match (uu___123_1049) with
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
| c when (c = 34) -> begin
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
in (Prims.strcat uu____1070 (match ((((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127"))) && (nc <> (Prims.parse_int "34")))) with
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
in (

let uu____1204 = (

let uu____1205 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar uu____1205))
in (FStar_Format.text uu____1204)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____1217 = (

let uu____1218 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____1218))
in (FStar_Format.parens uu____1217))
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
| uu____1231 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1241 = (

let uu____1242 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____1242))
in (FStar_Format.parens uu____1241)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____1244 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____1244))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____1246, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____1258 = (

let uu____1259 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____1259))
in (maybe_paren outer t_prio_fun uu____1258))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____1260 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1260) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____1261 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____1265 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____1265)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1319 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1319) with
| true -> begin
(

let uu____1320 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc1)::[]))
in (FStar_Format.parens uu____1320))
end
| uu____1321 -> begin
(

let uu____1322 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____1322))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs2 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs1)
in (

let uu____1338 = (FStar_Format.reduce docs2)
in (FStar_Format.parens uu____1338))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____1340 = (string_of_mlconstant c)
in (FStar_Format.text uu____1340))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____1342) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____1344 = (ptsym currentModule path)
in (FStar_Format.text uu____1344))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____1370 -> (match (uu____1370) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1382 = (

let uu____1385 = (

let uu____1386 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1386))
in (uu____1385)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____1382)))
end))
in (

let uu____1389 = (

let uu____1390 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1390))
in (FStar_Format.cbrackets uu____1389)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____1401 = (is_standard_constructor ctor)
in (match (uu____1401) with
| true -> begin
(

let uu____1402 = (

let uu____1407 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1407))
in (FStar_Pervasives_Native.snd uu____1402))
end
| uu____1418 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____1426 = (is_standard_constructor ctor)
in (match (uu____1426) with
| true -> begin
(

let uu____1427 = (

let uu____1432 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1432))
in (FStar_Pervasives_Native.snd uu____1427))
end
| uu____1443 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____1458, uu____1459) -> begin
(

let uu____1464 = (

let uu____1467 = (

let uu____1470 = (

let uu____1471 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1471))
in (uu____1470)::[])
in ((FStar_Format.text name))::uu____1467)
in (FStar_Format.reduce1 uu____1464))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs1 = (FStar_List.map (fun x -> (

let uu____1481 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____1481))) es)
in (

let docs2 = (

let uu____1487 = (FStar_Format.combine (FStar_Format.text ", ") docs1)
in (FStar_Format.parens uu____1487))
in docs2))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____1489, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____1505 = (

let uu____1508 = (

let uu____1511 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____1511)::[])
in (FStar_Format.hardline)::uu____1508)
in (FStar_Format.reduce uu____1505))
end
| uu____1512 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____1521 = (

let uu____1522 = (

let uu____1525 = (

let uu____1528 = (

let uu____1531 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____1531)::[])
in (doc1)::uu____1528)
in (pre)::uu____1525)
in (FStar_Format.combine FStar_Format.hardline uu____1522))
in (FStar_Format.parens uu____1521)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1541)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1543; FStar_Extraction_ML_Syntax.loc = uu____1544})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1546))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1548; FStar_Extraction_ML_Syntax.loc = uu____1549})::[]) when (

let uu____1584 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____1584 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1607; FStar_Extraction_ML_Syntax.loc = uu____1608}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1610; FStar_Extraction_ML_Syntax.loc = uu____1611} when (

let uu____1632 = (FStar_Extraction_ML_Syntax.idsym arg)
in (

let uu____1633 = (FStar_Extraction_ML_Syntax.idsym arg')
in (uu____1632 = uu____1633))) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1669; FStar_Extraction_ML_Syntax.loc = uu____1670}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1683; FStar_Extraction_ML_Syntax.loc = uu____1684}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1691 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1710 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1710))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1719 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1719) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1722 -> begin
(

let uu____1723 = (

let uu____1726 = (

let uu____1729 = (

let uu____1732 = (

let uu____1733 = (ptsym currentModule f)
in (FStar_Format.text uu____1733))
in (uu____1732)::[])
in ((FStar_Format.text "."))::uu____1729)
in (e2)::uu____1726)
in (FStar_Format.reduce uu____1723))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1759 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1759) with
| true -> begin
(

let uu____1760 = (

let uu____1763 = (

let uu____1766 = (

let uu____1769 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1771 = (

let uu____1774 = (

let uu____1777 = (doc_of_mltype currentModule outer xxt)
in (uu____1777)::[])
in ((FStar_Format.text " : "))::uu____1774)
in (FStar_Format.reduce1 uu____1771))
end
| uu____1778 -> begin
(FStar_Format.text "")
end)
in (uu____1769)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1766)
in ((FStar_Format.text "("))::uu____1763)
in (FStar_Format.reduce1 uu____1760))
end
| uu____1781 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1797 -> (match (uu____1797) with
| ((x, uu____1807), xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1819 = (

let uu____1822 = (

let uu____1825 = (FStar_Format.reduce1 ids1)
in (uu____1825)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1822)
in (FStar_Format.reduce1 uu____1819))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1836 = (

let uu____1839 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1840 = (

let uu____1843 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1843)::((FStar_Format.text "end"))::[])
in (uu____1839)::uu____1840))
in (FStar_Format.combine FStar_Format.hardline uu____1836))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1859 = (

let uu____1862 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1863 = (

let uu____1866 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1871 = (

let uu____1874 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1875 = (

let uu____1878 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1878)::((FStar_Format.text "end"))::[])
in (uu____1874)::uu____1875))
in (uu____1866)::uu____1871))
in (uu____1862)::uu____1863))
in (FStar_Format.combine FStar_Format.hardline uu____1859))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1916 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1916)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1921 = (

let uu____1924 = (

let uu____1927 = (

let uu____1928 = (ptctor currentModule exn)
in (FStar_Format.text uu____1928))
in (uu____1927)::[])
in ((FStar_Format.text "raise"))::uu____1924)
in (FStar_Format.reduce1 uu____1921))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1942 = (

let uu____1945 = (

let uu____1948 = (

let uu____1949 = (ptctor currentModule exn)
in (FStar_Format.text uu____1949))
in (

let uu____1950 = (

let uu____1953 = (

let uu____1954 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1954))
in (uu____1953)::[])
in (uu____1948)::uu____1950))
in ((FStar_Format.text "raise"))::uu____1945)
in (FStar_Format.reduce1 uu____1942)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1977 = (

let uu____1980 = (

let uu____1983 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1988 = (

let uu____1991 = (

let uu____1994 = (

let uu____1995 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1995))
in (uu____1994)::[])
in ((FStar_Format.text "with"))::uu____1991)
in (uu____1983)::uu____1988))
in ((FStar_Format.text "try"))::uu____1980)
in (FStar_Format.combine FStar_Format.hardline uu____1977))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____2002 = (

let uu____2013 = (as_bin_op p)
in (FStar_Option.get uu____2013))
in (match (uu____2002) with
| (uu____2036, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____2061 = (

let uu____2066 = (as_uni_op p)
in (FStar_Option.get uu____2066))
in (match (uu____2061) with
| (uu____2077, txt) -> begin
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

let uu____2088 = (string_of_mlconstant c)
in (FStar_Format.text uu____2088))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (FStar_Pervasives_Native.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____2115 -> (match (uu____2115) with
| (name, p) -> begin
(

let uu____2122 = (

let uu____2125 = (

let uu____2126 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____2126))
in (

let uu____2129 = (

let uu____2132 = (

let uu____2135 = (doc_of_pattern currentModule p)
in (uu____2135)::[])
in ((FStar_Format.text "="))::uu____2132)
in (uu____2125)::uu____2129))
in (FStar_Format.reduce1 uu____2122))
end))
in (

let uu____2136 = (

let uu____2137 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2137))
in (FStar_Format.cbrackets uu____2136)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____2148 = (is_standard_constructor ctor)
in (match (uu____2148) with
| true -> begin
(

let uu____2149 = (

let uu____2154 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2154))
in (FStar_Pervasives_Native.snd uu____2149))
end
| uu____2165 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____2173 = (is_standard_constructor ctor)
in (match (uu____2173) with
| true -> begin
(

let uu____2174 = (

let uu____2179 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2179))
in (FStar_Pervasives_Native.snd uu____2174))
end
| uu____2190 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____2198 = (

let uu____2201 = (

let uu____2202 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____2202))
in (

let uu____2203 = (

let uu____2206 = (

let uu____2209 = (doc_of_pattern currentModule xs)
in (uu____2209)::[])
in ((FStar_Format.text "::"))::uu____2206)
in (uu____2201)::uu____2203))
in (FStar_Format.reduce uu____2198))
end
| (uu____2210, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____2211))::[]) -> begin
(

let uu____2216 = (

let uu____2219 = (

let uu____2222 = (

let uu____2223 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____2223))
in (uu____2222)::[])
in ((FStar_Format.text name))::uu____2219)
in (FStar_Format.reduce1 uu____2216))
end
| uu____2224 -> begin
(

let uu____2231 = (

let uu____2234 = (

let uu____2237 = (

let uu____2238 = (

let uu____2239 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____2239))
in (FStar_Format.parens uu____2238))
in (uu____2237)::[])
in ((FStar_Format.text name))::uu____2234)
in (FStar_Format.reduce1 uu____2231))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____2252 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____2252)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____2263 -> (match (uu____2263) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2272 = (

let uu____2275 = (

let uu____2278 = (doc_of_pattern currentModule p)
in (uu____2278)::[])
in ((FStar_Format.text "|"))::uu____2275)
in (FStar_Format.reduce1 uu____2272))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____2285 = (

let uu____2288 = (

let uu____2291 = (doc_of_pattern currentModule p)
in (uu____2291)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____2288)
in (FStar_Format.reduce1 uu____2285)))
end)
in (

let uu____2292 = (

let uu____2295 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____2296 = (

let uu____2299 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2299)::((FStar_Format.text "end"))::[])
in (uu____2295)::uu____2296))
in (FStar_Format.combine FStar_Format.hardline uu____2292)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____2305 -> (match (uu____2305) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____2324 -> (match (uu____2324) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____2327; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____2341 -> begin
(

let uu____2342 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____2342) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____2343)::uu____2344, uu____2345) -> begin
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
| uu____2370 -> begin
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

let uu____2397 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____2397 FStar_Format.reduce1))
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(vars)::((FStar_Format.text "."))::(ty1)::[]))))
end)
end
| uu____2410 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____2411 = (

let uu____2414 = (

let uu____2415 = (FStar_Extraction_ML_Syntax.idsym name)
in (FStar_Format.text uu____2415))
in (

let uu____2416 = (

let uu____2419 = (FStar_Format.reduce1 ids)
in (uu____2419)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in (uu____2414)::uu____2416))
in (FStar_Format.reduce1 uu____2411)))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____2421 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____2432 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____2433 -> (match (uu____2433) with
| (lineno, file) -> begin
(

let uu____2436 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____2436) with
| true -> begin
FStar_Format.empty
end
| uu____2437 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____2468 -> (match (uu____2468) with
| (uu____2487, x, mangle_opt, tparams, uu____2491, body) -> begin
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

let uu____2509 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____2509))
end
| uu____2510 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (

let uu____2519 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____2519))) tparams)
in (

let uu____2520 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____2520)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____2544 -> (match (uu____2544) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____2557 = (

let uu____2558 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____2558))
in (FStar_Format.cbrackets uu____2557)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____2591 -> (match (uu____2591) with
| (name, tys) -> begin
(

let uu____2616 = (FStar_List.split tys)
in (match (uu____2616) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____2635 -> begin
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

let uu____2665 = (

let uu____2668 = (

let uu____2671 = (

let uu____2672 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____2672))
in (uu____2671)::[])
in (tparams1)::uu____2668)
in (FStar_Format.reduce1 uu____2665))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____2677 = (

let uu____2680 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____2680)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____2677)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2703 = (

let uu____2706 = (

let uu____2709 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____2709)::[])
in ((FStar_Format.text "type"))::uu____2706)
in (FStar_Format.reduce1 uu____2703))
end
| uu____2710 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____2727 = (

let uu____2730 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____2731 = (

let uu____2734 = (doc_of_sig currentModule subsig)
in (

let uu____2735 = (

let uu____2738 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____2738)::[])
in (uu____2734)::uu____2735))
in (uu____2730)::uu____2731))
in (FStar_Format.combine FStar_Format.hardline uu____2727))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____2756 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____2756))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____2758, ty)) -> begin
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

let uu____2828 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____2828))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____2831, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____2840 = (

let uu____2843 = (

let uu____2846 = (

let uu____2849 = (

let uu____2852 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____2852)::[])
in ((FStar_Format.text "="))::uu____2849)
in ((FStar_Format.text "_"))::uu____2846)
in ((FStar_Format.text "let"))::uu____2843)
in (FStar_Format.reduce1 uu____2840))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs1 = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____2878) -> begin
FStar_Format.empty
end
| uu____2879 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs1))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____2889 -> (match (uu____2889) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____2955 -> (match (uu____2955) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____3028 -> (match (uu____3028) with
| (s, uu____3034) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let uu____3061 = (

let uu____3064 = (

let uu____3067 = (

let uu____3070 = (FStar_Format.reduce sub3)
in (uu____3070)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3067)
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____3064)
in (FStar_Format.reduce uu____3061))))))))
end))
and for1_mod = (fun istop uu____3073 -> (match (uu____3073) with
| (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name)
in (

let maybe_open_pervasives = (match (mod_name) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____3141 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____3152 = (

let uu____3155 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3155) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____3158 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____3161 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____3152))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____3163 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____3174 -> (match (uu____3174) with
| (uu____3179, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____3210 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____3210) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____3213 -> begin
[]
end))
in (

let uu____3214 = (

let uu____3217 = (

let uu____3220 = (

let uu____3223 = (

let uu____3226 = (

let uu____3229 = (

let uu____3232 = (FStar_Format.reduce sub3)
in (uu____3232)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____3229)
in (FStar_Format.hardline)::uu____3226)
in (FStar_List.append maybe_open_pervasives uu____3223))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____3220))
in (FStar_List.append prefix1 uu____3217))
in (FStar_All.pipe_left FStar_Format.reduce uu____3214))))))))))
end))
in (

let docs1 = (FStar_List.map (fun uu____3271 -> (match (uu____3271) with
| (x, s, m) -> begin
(

let uu____3321 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____3322 = (for1_mod true ((x), (s), (m)))
in ((uu____3321), (uu____3322))))
end)) mllib)
in docs1))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3354 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____3354 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____3368 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____3368 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





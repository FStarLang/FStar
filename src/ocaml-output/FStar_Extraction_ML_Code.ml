
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
| uu____9 -> begin
false
end))


let uu___is_IRight : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| IRight -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Left : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Left -> begin
true
end
| uu____31 -> begin
false
end))


let uu___is_Right : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Right -> begin
true
end
| uu____42 -> begin
false
end))


let uu___is_NonAssoc : assoc  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NonAssoc -> begin
true
end
| uu____53 -> begin
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
| uu____69 -> begin
false
end))


let uu___is_Postfix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Postfix -> begin
true
end
| uu____80 -> begin
false
end))


let uu___is_Infix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
true
end
| uu____92 -> begin
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

type doc =
| Doc of Prims.string


let uu___is_Doc : doc  ->  Prims.bool = (fun projectee -> true)


let __proj__Doc__item___0 : doc  ->  Prims.string = (fun projectee -> (match (projectee) with
| Doc (_0) -> begin
_0
end))


let empty : doc = Doc ("")


let hardline : doc = Doc ("\n")


let text : Prims.string  ->  doc = (fun s -> Doc (s))


let num : Prims.int  ->  doc = (fun i -> (

let uu____305 = (FStar_Util.string_of_int i)
in Doc (uu____305)))


let break1 : doc = (text " ")


let enclose : doc  ->  doc  ->  doc  ->  doc = (fun uu____322 uu____323 uu____324 -> (match (((uu____322), (uu____323), (uu____324))) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.op_Hat l (Prims.op_Hat x r)))
end))


let cbrackets : doc  ->  doc = (fun uu____336 -> (match (uu____336) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))


let parens : doc  ->  doc = (fun uu____346 -> (match (uu____346) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))


let cat : doc  ->  doc  ->  doc = (fun uu____360 uu____361 -> (match (((uu____360), (uu____361))) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.op_Hat d1 d2))
end))


let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))


let combine : doc  ->  doc Prims.list  ->  doc = (fun uu____387 docs -> (match (uu____387) with
| Doc (sep) -> begin
(

let select = (fun uu____401 -> (match (uu____401) with
| Doc (d) -> begin
(match ((Prims.op_Equality d "")) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____414 -> begin
FStar_Pervasives_Native.Some (d)
end)
end))
in (

let docs1 = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs1))))
end))


let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))


let hbox : doc  ->  doc = (fun d -> d)


let rec in_ns : 'a . ('a Prims.list * 'a Prims.list)  ->  Prims.bool = (fun x -> (match (x) with
| ([], uu____466) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (Prims.op_Equality x1 x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____490, uu____491) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((Prims.op_Equality ns' currentModule)) with
| true -> begin
[]
end
| uu____531 -> begin
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

let uu____572 = (FStar_Util.first_N cg_len ns)
in (match (uu____572) with
| (pfx, sfx) -> begin
(match ((Prims.op_Equality pfx cg_path)) with
| true -> begin
(

let uu____612 = (

let uu____616 = (

let uu____620 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____620)::[])
in (FStar_List.append pfx uu____616))
in FStar_Pervasives_Native.Some (uu____612))
end
| uu____628 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____633 -> begin
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

let uu____666 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____666) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____682 -> begin
(

let uu____684 = x
in (match (uu____684) with
| (ns, x1) -> begin
(

let uu____695 = (path_of_ns currentModule ns)
in ((uu____695), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____713 = (

let uu____715 = (

let uu____717 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____717))
in (

let uu____720 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____715 uu____720)))
in (match (uu____713) with
| true -> begin
(Prims.op_Hat "l__" s)
end
| uu____727 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____754 -> begin
(

let uu____756 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____756) with
| (p, s) -> begin
(

let uu____768 = (

let uu____772 = (

let uu____776 = (ptsym_of_symbol s)
in (uu____776)::[])
in (FStar_List.append p uu____772))
in (FStar_String.concat "." uu____768))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____797 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____797) with
| (p, s) -> begin
(

let s1 = (

let uu____811 = (

let uu____813 = (

let uu____815 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____815))
in (

let uu____818 = (FStar_String.get s (Prims.parse_int "0"))
in (Prims.op_disEquality uu____813 uu____818)))
in (match (uu____811) with
| true -> begin
(Prims.op_Hat "U__" s)
end
| uu____825 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1181 -> (

let op_minus = (

let uu____1184 = (

let uu____1186 = (FStar_Options.codegen ())
in (Prims.op_Equality uu____1186 (FStar_Pervasives_Native.Some (FStar_Options.FSharp))))
in (match (uu____1184) with
| true -> begin
"-"
end
| uu____1194 -> begin
"~-"
end))
in ((("op_Negation"), ("not")))::((("op_Minus"), (op_minus)))::((("op_Bang"), ("Support.ST.read")))::[]))


let prim_types : 'Auu____1235 . unit  ->  'Auu____1235 Prims.list = (fun uu____1238 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (Prims.op_Equality ns (("Prims")::[])))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____1333 -> (match (uu____1333) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____1392 -> (match (uu____1392) with
| (y, uu____1408, uu____1409) -> begin
(Prims.op_Equality x y)
end)) infix_prim_ops)
end
| uu____1425 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____1447 = (as_bin_op p)
in (Prims.op_disEquality uu____1447 FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____1504 -> (match (uu____1504) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(

let uu____1532 = (prim_uni_ops ())
in (FStar_List.tryFind (fun uu____1550 -> (match (uu____1550) with
| (y, uu____1559) -> begin
(Prims.op_Equality x y)
end)) uu____1532))
end
| uu____1565 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____1580 = (as_uni_op p)
in (Prims.op_disEquality uu____1580 FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____1624 -> (match (uu____1624) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____1661 -> (match (uu____1661) with
| (y, uu____1670) -> begin
(Prims.op_Equality x y)
end)) prim_constructors)
end
| uu____1676 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____1691 = (as_standard_constructor p)
in (Prims.op_disEquality uu____1691 FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  doc  ->  doc = (fun uu____1741 inner doc1 -> (match (uu____1741) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____1807 = _inner
in (match (uu____1807) with
| (pi, fi) -> begin
(

let uu____1818 = _outer
in (match (uu____1818) with
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
| (uu____1836, NonAssoc) -> begin
((Prims.op_Equality pi po) && (Prims.op_Equality fi fo))
end
| (uu____1838, uu____1839) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____1842 -> begin
(parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.op_Hat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_BaseTypes.char  ->  Prims.string)  ->  FStar_BaseTypes.char  ->  Prims.string = (fun fallback uu___0_1878 -> if (Prims.op_Equality uu___0_1878 92 (*\*)) then begin
"\\\\"
end else begin
if (Prims.op_Equality uu___0_1878 32 (* *)) then begin
" "
end else begin
if (Prims.op_Equality uu___0_1878 8) then begin
"\\b"
end else begin
if (Prims.op_Equality uu___0_1878 9) then begin
"\\t"
end else begin
if (Prims.op_Equality uu___0_1878 13) then begin
"\\r"
end else begin
if (Prims.op_Equality uu___0_1878 10) then begin
"\\n"
end else begin
if (Prims.op_Equality uu___0_1878 39 (*'*)) then begin
"\\\'"
end else begin
if (Prims.op_Equality uu___0_1878 34) then begin
"\\\""
end else begin
if (FStar_Util.is_letter_or_digit uu___0_1878) then begin
(FStar_Util.string_of_char uu___0_1878)
end else begin
if (FStar_Util.is_punctuation uu___0_1878) then begin
(FStar_Util.string_of_char uu___0_1878)
end else begin
if (FStar_Util.is_symbol uu___0_1878) then begin
(FStar_Util.string_of_char uu___0_1878)
end else begin
(fallback uu___0_1878)
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

let uu____1925 = (FStar_Util.string_of_int nc)
in (Prims.op_Hat uu____1925 (match ((((nc >= (Prims.parse_int "32")) && (nc <= (Prims.parse_int "127"))) && (Prims.op_disEquality nc (Prims.parse_int "34")))) with
| true -> begin
(Prims.op_Hat " (*" (Prims.op_Hat (FStar_Util.string_of_char c) "*)"))
end
| uu____1935 -> begin
""
end))))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.op_Hat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.op_Hat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1967, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____1981, FStar_Const.Int16)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.None) -> begin
(Prims.op_Hat "(Prims.parse_int \"" (Prims.op_Hat s "\")"))
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(

let uu____2013 = (

let uu____2015 = (FStar_Compiler_Bytes.f_encode escape_byte_hex bytes)
in (Prims.op_Hat uu____2015 "\""))
in (Prims.op_Hat "\"" uu____2013))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____2021 = (

let uu____2023 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.op_Hat uu____2023 "\""))
in (Prims.op_Hat "\"" uu____2021))
end
| uu____2027 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s 95 (*_*) 117 (*u*))
end
| uu____2077 -> begin
s
end))
in (text (escape_tyvar x)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____2086 = (

let uu____2087 = (combine (text " * ") doc1)
in (hbox uu____2087))
in (parens uu____2086))
in doc2))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args1 = (match (args) with
| [] -> begin
empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule ((t_prio_name), (Left)) arg)
end
| uu____2097 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____2103 = (

let uu____2104 = (combine (text ", ") args1)
in (hbox uu____2104))
in (parens uu____2103)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____2108 = (reduce1 ((args1)::((text name1))::[]))
in (hbox uu____2108))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____2110, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____2114 = (

let uu____2115 = (reduce1 ((d1)::((text " -> "))::(d2)::[]))
in (hbox uu____2115))
in (maybe_paren outer t_prio_fun uu____2114))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____2117 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2117) with
| true -> begin
(text "obj")
end
| uu____2121 -> begin
(text "Obj.t")
end))
end
| FStar_Extraction_ML_Syntax.MLTY_Erased -> begin
(text "unit")
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  doc = (fun currentModule outer ty -> (

let uu____2129 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____2129)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2222 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2222) with
| true -> begin
(

let uu____2225 = (reduce (((text "Prims.unsafe_coerce "))::(doc1)::[]))
in (parens uu____2225))
end
| uu____2227 -> begin
(

let uu____2229 = (reduce (((text "Obj.magic "))::((parens doc1))::[]))
in (parens uu____2229))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs1 = (FStar_List.map (fun d -> (reduce ((d)::((text ";"))::(hardline)::[]))) docs)
in (

let uu____2243 = (reduce docs1)
in (parens uu____2243))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____2245 = (string_of_mlconstant c)
in (text uu____2245))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x) -> begin
(text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____2250 = (ptsym currentModule path)
in (text uu____2250))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____2284 -> (match (uu____2284) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2295 = (

let uu____2298 = (

let uu____2299 = (ptsym currentModule ((path), (name)))
in (text uu____2299))
in (uu____2298)::((text "="))::(doc1)::[])
in (reduce1 uu____2295)))
end))
in (

let uu____2306 = (

let uu____2307 = (FStar_List.map for1 fields)
in (combine (text "; ") uu____2307))
in (cbrackets uu____2306)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____2321 = (is_standard_constructor ctor)
in (match (uu____2321) with
| true -> begin
(

let uu____2325 = (

let uu____2332 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2332))
in (FStar_Pervasives_Native.snd uu____2325))
end
| uu____2349 -> begin
(ptctor currentModule ctor)
end))
in (text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____2359 = (is_standard_constructor ctor)
in (match (uu____2359) with
| true -> begin
(

let uu____2363 = (

let uu____2370 = (as_standard_constructor ctor)
in (FStar_Option.get uu____2370))
in (FStar_Pervasives_Native.snd uu____2363))
end
| uu____2387 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(reduce (((parens x))::((text "::"))::(xs)::[]))
end
| (uu____2403, uu____2404) -> begin
(

let uu____2411 = (

let uu____2414 = (

let uu____2417 = (

let uu____2418 = (combine (text ", ") args1)
in (parens uu____2418))
in (uu____2417)::[])
in ((text name))::uu____2414)
in (reduce1 uu____2411))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____2429 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (parens uu____2429))) es)
in (

let docs1 = (

let uu____2431 = (combine (text ", ") docs)
in (parens uu____2431))
in docs1))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = (match ((Prims.op_disEquality e.FStar_Extraction_ML_Syntax.loc FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____2448 = (

let uu____2451 = (

let uu____2454 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____2454)::[])
in (hardline)::uu____2451)
in (reduce uu____2448))
end
| uu____2455 -> begin
empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____2463 = (

let uu____2464 = (

let uu____2467 = (

let uu____2470 = (

let uu____2473 = (reduce1 (((text "in"))::(body1)::[]))
in (uu____2473)::[])
in (doc1)::uu____2470)
in (pre)::uu____2467)
in (combine hardline uu____2464))
in (parens uu____2463)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____2484)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____2486; FStar_Extraction_ML_Syntax.loc = uu____2487})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____2489))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____2491; FStar_Extraction_ML_Syntax.loc = uu____2492})::[]) when (

let uu____2536 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (Prims.op_Equality uu____2536 "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____2562; FStar_Extraction_ML_Syntax.loc = uu____2563}, branches); FStar_Extraction_ML_Syntax.mlty = uu____2565; FStar_Extraction_ML_Syntax.loc = uu____2566} when (Prims.op_Equality arg arg') -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2624; FStar_Extraction_ML_Syntax.loc = uu____2625}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____2638; FStar_Extraction_ML_Syntax.loc = uu____2639}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (Prims.op_Equality unitVal FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____2646 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____2657 = (reduce1 ((e2)::args1))
in (parens uu____2657))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____2662 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2662) with
| true -> begin
(reduce ((e2)::((text "."))::((text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____2670 -> begin
(

let uu____2672 = (

let uu____2675 = (

let uu____2678 = (

let uu____2681 = (

let uu____2682 = (ptsym currentModule f)
in (text uu____2682))
in (uu____2681)::[])
in ((text "."))::uu____2678)
in (e2)::uu____2675)
in (reduce uu____2672))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____2718 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2718) with
| true -> begin
(

let uu____2721 = (

let uu____2724 = (

let uu____2727 = (

let uu____2730 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____2732 = (

let uu____2735 = (

let uu____2738 = (doc_of_mltype currentModule outer xxt)
in (uu____2738)::[])
in ((text " : "))::uu____2735)
in (reduce1 uu____2732))
end
| uu____2740 -> begin
(text "")
end)
in (uu____2730)::((text ")"))::[])
in ((text x))::uu____2727)
in ((text "("))::uu____2724)
in (reduce1 uu____2721))
end
| uu____2746 -> begin
(text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____2759 -> (match (uu____2759) with
| (x, xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____2771 = (

let uu____2774 = (

let uu____2777 = (reduce1 ids1)
in (uu____2777)::((text "->"))::(body1)::[])
in ((text "fun"))::uu____2774)
in (reduce1 uu____2771))
in (parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____2786 = (

let uu____2789 = (reduce1 (((text "if"))::(cond1)::((text "then"))::((text "begin"))::[]))
in (

let uu____2793 = (

let uu____2796 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____2796)::((text "end"))::[])
in (uu____2789)::uu____2793))
in (combine hardline uu____2786))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____2805 = (

let uu____2808 = (reduce1 (((text "if"))::(cond1)::((text "then"))::((text "begin"))::[]))
in (

let uu____2812 = (

let uu____2815 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2816 = (

let uu____2819 = (reduce1 (((text "end"))::((text "else"))::((text "begin"))::[]))
in (

let uu____2823 = (

let uu____2826 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____2826)::((text "end"))::[])
in (uu____2819)::uu____2823))
in (uu____2815)::uu____2816))
in (uu____2808)::uu____2812))
in (combine hardline uu____2805))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____2865 = (reduce1 (((text "match"))::((parens cond1))::((text "with"))::[]))
in (uu____2865)::pats1)
in (

let doc2 = (combine hardline doc1)
in (parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____2872 = (

let uu____2875 = (

let uu____2878 = (

let uu____2879 = (ptctor currentModule exn)
in (text uu____2879))
in (uu____2878)::[])
in ((text "raise"))::uu____2875)
in (reduce1 uu____2872))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____2891 = (

let uu____2894 = (

let uu____2897 = (

let uu____2898 = (ptctor currentModule exn)
in (text uu____2898))
in (

let uu____2900 = (

let uu____2903 = (

let uu____2904 = (combine (text ", ") args1)
in (parens uu____2904))
in (uu____2903)::[])
in (uu____2897)::uu____2900))
in ((text "raise"))::uu____2894)
in (reduce1 uu____2891)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____2929 = (

let uu____2932 = (

let uu____2935 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____2936 = (

let uu____2939 = (

let uu____2942 = (

let uu____2943 = (FStar_List.map (doc_of_branch currentModule) pats)
in (combine hardline uu____2943))
in (uu____2942)::[])
in ((text "with"))::uu____2939)
in (uu____2935)::uu____2936))
in ((text "try"))::uu____2932)
in (combine hardline uu____2929))
end
| FStar_Extraction_ML_Syntax.MLE_TApp (head1, ty_args) -> begin
(doc_of_expr currentModule outer head1)
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  doc = (fun currentModule p e1 e2 -> (

let uu____2967 = (

let uu____2981 = (as_bin_op p)
in (FStar_Option.get uu____2981))
in (match (uu____2967) with
| (uu____3010, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (reduce1 ((e11)::((text txt))::(e21)::[]))
in (parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  doc = (fun currentModule p e1 -> (

let uu____3034 = (

let uu____3041 = (as_uni_op p)
in (FStar_Option.get uu____3041))
in (match (uu____3034) with
| (uu____3056, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (reduce1 (((text txt))::((parens e11))::[]))
in (parens doc1)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(

let uu____3069 = (string_of_mlconstant c)
in (text uu____3069))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(text x)
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____3105 -> (match (uu____3105) with
| (name, p) -> begin
(

let uu____3115 = (

let uu____3118 = (

let uu____3119 = (ptsym currentModule ((path), (name)))
in (text uu____3119))
in (

let uu____3125 = (

let uu____3128 = (

let uu____3131 = (doc_of_pattern currentModule p)
in (uu____3131)::[])
in ((text "="))::uu____3128)
in (uu____3118)::uu____3125))
in (reduce1 uu____3115))
end))
in (

let uu____3133 = (

let uu____3134 = (FStar_List.map for1 fields)
in (combine (text "; ") uu____3134))
in (cbrackets uu____3133)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____3148 = (is_standard_constructor ctor)
in (match (uu____3148) with
| true -> begin
(

let uu____3152 = (

let uu____3159 = (as_standard_constructor ctor)
in (FStar_Option.get uu____3159))
in (FStar_Pervasives_Native.snd uu____3152))
end
| uu____3176 -> begin
(ptctor currentModule ctor)
end))
in (text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____3186 = (is_standard_constructor ctor)
in (match (uu____3186) with
| true -> begin
(

let uu____3190 = (

let uu____3197 = (as_standard_constructor ctor)
in (FStar_Option.get uu____3197))
in (FStar_Pervasives_Native.snd uu____3190))
end
| uu____3214 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____3226 = (

let uu____3229 = (

let uu____3230 = (doc_of_pattern currentModule x)
in (parens uu____3230))
in (

let uu____3231 = (

let uu____3234 = (

let uu____3237 = (doc_of_pattern currentModule xs)
in (uu____3237)::[])
in ((text "::"))::uu____3234)
in (uu____3229)::uu____3231))
in (reduce uu____3226))
end
| (uu____3239, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____3240))::[]) -> begin
(

let uu____3247 = (

let uu____3250 = (

let uu____3253 = (

let uu____3254 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____3254))
in (uu____3253)::[])
in ((text name))::uu____3250)
in (reduce1 uu____3247))
end
| uu____3255 -> begin
(

let uu____3263 = (

let uu____3266 = (

let uu____3269 = (

let uu____3270 = (

let uu____3271 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (combine (text ", ") uu____3271))
in (parens uu____3270))
in (uu____3269)::[])
in ((text name))::uu____3266)
in (reduce1 uu____3263))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____3286 = (combine (text ", ") ps1)
in (parens uu____3286)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map parens ps1)
in (combine (text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  doc = (fun currentModule uu____3299 -> (match (uu____3299) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3309 = (

let uu____3312 = (

let uu____3315 = (doc_of_pattern currentModule p)
in (uu____3315)::[])
in ((text "|"))::uu____3312)
in (reduce1 uu____3309))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____3319 = (

let uu____3322 = (

let uu____3325 = (doc_of_pattern currentModule p)
in (uu____3325)::((text "when"))::(c1)::[])
in ((text "|"))::uu____3322)
in (reduce1 uu____3319)))
end)
in (

let uu____3328 = (

let uu____3331 = (reduce1 ((case)::((text "->"))::((text "begin"))::[]))
in (

let uu____3334 = (

let uu____3337 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____3337)::((text "end"))::[])
in (uu____3331)::uu____3334))
in (combine hardline uu____3328)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  doc = (fun currentModule uu____3340 -> (match (uu____3340) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____3365 -> (match (uu____3365) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____3368; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.mllb_meta = uu____3370; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(text "")
end
| uu____3384 -> begin
(

let uu____3386 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____3386) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____3389)::uu____3390, uu____3391) -> begin
(text "")
end
| FStar_Pervasives_Native.None -> begin
(text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (reduce1 (((text ":"))::(ty1)::[])))
end)
end
| uu____3403 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.None -> begin
(text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (reduce1 (((text ":"))::(ty1)::[])))
end
| FStar_Pervasives_Native.Some (vs, ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (

let vars = (

let uu____3415 = (FStar_All.pipe_right vs (FStar_List.map (fun x -> (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) (FStar_Extraction_ML_Syntax.MLTY_Var (x))))))
in (FStar_All.pipe_right uu____3415 reduce1))
in (reduce1 (((text ":"))::(vars)::((text "."))::(ty1)::[]))))
end)
end
| uu____3431 -> begin
(text "")
end)
end))
end)
in (

let uu____3434 = (

let uu____3437 = (

let uu____3440 = (reduce1 ids)
in (uu____3440)::(ty_annot)::((text "="))::(e1)::[])
in ((text name))::uu____3437)
in (reduce1 uu____3434)))))
end))
in (

let letdoc = (match ((Prims.op_Equality rec_ FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(reduce1 (((text "let"))::((text "rec"))::[]))
end
| uu____3446 -> begin
(text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (reduce1 (((match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____3463 -> begin
(text "and")
end))::(doc1)::[]))) lets1)
in (combine hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  doc = (fun uu____3466 -> (match (uu____3466) with
| (lineno, file) -> begin
(

let uu____3473 = (((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) || (Prims.op_Equality file "<dummy>"))
in (match (uu____3473) with
| true -> begin
empty
end
| uu____3478 -> begin
(

let file1 = (FStar_Util.basename file)
in (

let uu____3482 = (

let uu____3485 = (

let uu____3488 = (num lineno)
in (uu____3488)::((text (Prims.op_Hat "\"" (Prims.op_Hat file1 "\""))))::[])
in ((text "#"))::uu____3485)
in (reduce1 uu____3482)))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  doc = (fun currentModule decls -> (

let for1 = (fun uu____3532 -> (match (uu____3532) with
| (uu____3555, x, mangle_opt, tparams, uu____3559, body) -> begin
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
empty
end
| (x2)::[] -> begin
(text x2)
end
| uu____3594 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (text x2)) tparams)
in (

let uu____3605 = (combine (text ", ") doc1)
in (parens uu____3605)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____3632 -> (match (uu____3632) with
| (name, ty) -> begin
(

let name1 = (text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (reduce1 ((name1)::((text ":"))::(ty1)::[]))))
end))
in (

let uu____3645 = (

let uu____3646 = (FStar_List.map forfield fields)
in (combine (text "; ") uu____3646))
in (cbrackets uu____3645)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____3687 -> (match (uu____3687) with
| (name, tys) -> begin
(

let uu____3718 = (FStar_List.split tys)
in (match (uu____3718) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(text name)
end
| uu____3741 -> begin
(

let tys2 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys1)
in (

let tys3 = (combine (text " * ") tys2)
in (reduce1 (((text name))::((text "of"))::(tys3)::[]))))
end)
end))
end))
in (

let ctors1 = (FStar_List.map forctor ctors)
in (

let ctors2 = (FStar_List.map (fun d -> (reduce1 (((text "|"))::(d)::[]))) ctors1)
in (combine hardline ctors2))))
end))
in (

let doc1 = (

let uu____3772 = (

let uu____3775 = (

let uu____3778 = (

let uu____3779 = (ptsym currentModule (([]), (x1)))
in (text uu____3779))
in (uu____3778)::[])
in (tparams1)::uu____3775)
in (reduce1 uu____3772))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____3788 = (

let uu____3791 = (reduce1 ((doc1)::((text "="))::[]))
in (uu____3791)::(body2)::[])
in (combine hardline uu____3788)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3799 = (

let uu____3802 = (

let uu____3805 = (combine (text " \n and ") doc1)
in (uu____3805)::[])
in ((text "type"))::uu____3802)
in (reduce1 uu____3799))
end
| uu____3808 -> begin
(text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____3841 = (

let uu____3844 = (reduce1 (((text "module"))::((text x))::((text "="))::[]))
in (

let uu____3847 = (

let uu____3850 = (doc_of_sig currentModule subsig)
in (

let uu____3851 = (

let uu____3854 = (reduce1 (((text "end"))::[]))
in (uu____3854)::[])
in (uu____3850)::uu____3851))
in (uu____3844)::uu____3847))
in (combine hardline uu____3841))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(reduce1 (((text "exception"))::((text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____3874 = (combine (text " * ") args1)
in (parens uu____3874))
in (reduce1 (((text "exception"))::((text x))::((text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____3879, ty)) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (reduce1 (((text "val"))::((text x))::((text ": "))::(ty1)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  doc = (fun currentModule s -> (

let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (

let docs1 = (FStar_List.map (fun x -> (reduce ((x)::(hardline)::(hardline)::[]))) docs)
in (reduce docs1))))


let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(reduce1 (((text "exception"))::((text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args1 = (FStar_List.map FStar_Pervasives_Native.snd args)
in (

let args2 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args1)
in (

let args3 = (

let uu____3958 = (combine (text " * ") args2)
in (parens uu____3958))
in (reduce1 (((text "exception"))::((text x))::((text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____3974 = (

let uu____3977 = (

let uu____3980 = (

let uu____3983 = (

let uu____3986 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____3986)::[])
in ((text "="))::uu____3983)
in ((text "_"))::uu____3980)
in ((text "let"))::uu____3977)
in (reduce1 uu____3974))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____4016) -> begin
empty
end
| uu____4017 -> begin
hardline
end))::(hardline)::[])) m)
in (reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * doc) Prims.list = (fun uu____4030 -> (match (uu____4030) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____4100 -> (match (uu____4100) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (reduce1 (((text "module"))::((text x1))::((text ":"))::((text "sig"))::[]))
in (

let tail1 = (reduce1 (((text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____4160 -> (match (uu____4160) with
| (s, uu____4166) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (reduce ((x2)::(hardline)::(hardline)::[]))) sub2)
in (

let uu____4187 = (

let uu____4190 = (

let uu____4193 = (

let uu____4196 = (reduce sub3)
in (uu____4196)::((cat tail1 hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(cat s hardline)
end))::uu____4193)
in ((cat head1 hardline))::uu____4190)
in (reduce uu____4187))))))))
end))
and for1_mod = (fun istop uu____4199 -> (match (uu____4199) with
| (mod_name1, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name1)
in (

let maybe_open_pervasives = (match (mod_name1) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____4281 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (hardline)::((text (Prims.op_Hat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____4302 = (

let uu____4305 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____4305) with
| true -> begin
((text "module"))::((text target_mod_name))::[]
end
| uu____4311 -> begin
(match ((not (istop))) with
| true -> begin
((text "module"))::((text target_mod_name))::((text "="))::((text "struct"))::[]
end
| uu____4319 -> begin
[]
end)
end))
in (reduce1 uu____4302))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(reduce1 (((text "end"))::[]))
end
| uu____4324 -> begin
(reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____4336 -> (match (uu____4336) with
| (uu____4341, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (reduce ((x)::(hardline)::(hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____4367 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____4367) with
| true -> begin
((cat (text "#light \"off\"") hardline))::[]
end
| uu____4373 -> begin
[]
end))
in (

let uu____4375 = (

let uu____4378 = (

let uu____4381 = (

let uu____4384 = (

let uu____4387 = (

let uu____4390 = (

let uu____4393 = (reduce sub3)
in (uu____4393)::((cat tail1 hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(cat s hardline)
end))::uu____4390)
in (hardline)::uu____4387)
in (FStar_List.append maybe_open_pervasives uu____4384))
in (FStar_List.append ((head1)::(hardline)::((text "open Prims"))::[]) uu____4381))
in (FStar_List.append prefix1 uu____4378))
in (FStar_All.pipe_left reduce uu____4375))))))))))
end))
in (

let docs = (FStar_List.map (fun uu____4437 -> (match (uu____4437) with
| (x, s, m) -> begin
(

let uu____4494 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____4496 = (for1_mod true ((x), (s), (m)))
in ((uu____4494), (uu____4496))))
end)) mllib)
in docs))
end))


let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz uu____4525 -> (match (uu____4525) with
| Doc (doc1) -> begin
doc1
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____4556 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____4556 ((min_op_prec), (NonAssoc)) e))
in (pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____4572 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____4572 ((min_op_prec), (NonAssoc)) e))
in (pretty (Prims.parse_int "0") doc1)))





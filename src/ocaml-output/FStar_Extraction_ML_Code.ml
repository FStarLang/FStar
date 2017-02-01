
open Prims
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
| uu____27 -> begin
false
end))


let uu___is_Postfix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Postfix -> begin
true
end
| uu____31 -> begin
false
end))


let uu___is_Infix : fixity  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Infix (_0) -> begin
true
end
| uu____36 -> begin
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
| ([], uu____101) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____115, uu____116) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| uu____132 -> begin
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

let uu____154 = (FStar_Util.first_N cg_len ns)
in (match (uu____154) with
| (pfx, sfx) -> begin
(match ((pfx = cg_path)) with
| true -> begin
(

let uu____172 = (

let uu____174 = (

let uu____176 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____176)::[])
in (FStar_List.append pfx uu____174))
in Some (uu____172))
end
| uu____178 -> begin
None
end)
end))
end
| uu____180 -> begin
None
end))))
in (match (found) with
| None -> begin
(ns')::[]
end
| Some (x) -> begin
x
end))))
end)))


let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____195 -> begin
(

let uu____196 = x
in (match (uu____196) with
| (ns, x) -> begin
(

let uu____201 = (path_of_ns currentModule ns)
in ((uu____201), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____207 = (

let uu____208 = (

let uu____209 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____209))
in (

let uu____210 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____208 <> uu____210)))
in (match (uu____207) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____211 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| uu____220 -> begin
(

let uu____221 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____221) with
| (p, s) -> begin
(

let uu____226 = (

let uu____228 = (

let uu____230 = (ptsym_of_symbol s)
in (uu____230)::[])
in (FStar_List.append p uu____228))
in (FStar_String.concat "." uu____226))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____237 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____237) with
| (p, s) -> begin
(

let s = (

let uu____243 = (

let uu____244 = (

let uu____245 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____245))
in (

let uu____246 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____244 <> uu____246)))
in (match (uu____243) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____247 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____371 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) Prims.option = (fun uu____399 -> (match (uu____399) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____421 -> (match (uu____421) with
| (y, uu____428, uu____429) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____434 -> begin
None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____443 = (as_bin_op p)
in (uu____443 <> None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____466 -> (match (uu____466) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____479 -> (match (uu____479) with
| (y, uu____483) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____484 -> begin
None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____490 = (as_uni_op p)
in (uu____490 <> None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____507 -> (match (uu____507) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____520 -> (match (uu____520) with
| (y, uu____524) -> begin
(x = y)
end)) prim_constructors)
end
| uu____525 -> begin
None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____531 = (as_standard_constructor p)
in (uu____531 <> None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____552 inner doc -> (match (uu____552) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let uu____585 = _inner
in (match (uu____585) with
| (pi, fi) -> begin
(

let uu____590 = _outer
in (match (uu____590) with
| (po, fo) -> begin
((pi > po) || (match (((fi), (side))) with
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
| (uu____595, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____596, uu____597) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc
end
| uu____598 -> begin
(FStar_Format.parens doc)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___112_613 -> (match (uu___112_613) with
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

let uu____632 = (

let uu____633 = (escape_or escape_char_hex c)
in (Prims.strcat uu____633 "\'"))
in (Prims.strcat "\'" uu____632))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int8))) | (FStar_Extraction_ML_Syntax.MLC_Int (s, Some (_, FStar_Const.Int16))) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, None) -> begin
(Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")"))
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(

let uu____668 = (

let uu____669 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____669 "\""))
in (Prims.strcat "\"" uu____668))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____671 = (

let uu____672 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____672 "\""))
in (Prims.strcat "\"" uu____671))
end
| uu____673 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____694 -> begin
s
end))
in (

let uu____695 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text uu____695)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (

let uu____703 = (

let uu____704 = (FStar_Format.combine (FStar_Format.text " * ") doc)
in (FStar_Format.hbox uu____704))
in (FStar_Format.parens uu____703))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(

let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule ((t_prio_name), (Left)) arg)
end
| uu____713 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____719 = (

let uu____720 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.hbox uu____720))
in (FStar_Format.parens uu____719)))
end)
in (

let name = (ptsym currentModule name)
in (

let uu____722 = (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[]))
in (FStar_Format.hbox uu____722))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____724, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____732 = (

let uu____733 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____733))
in (maybe_paren outer t_prio_fun uu____732))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____734 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____734) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____735 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____786 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____786) with
| true -> begin
(

let uu____787 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FStar_Format.parens uu____787))
end
| uu____788 -> begin
(

let uu____789 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[]))
in (FStar_Format.parens uu____789))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (

let uu____799 = (FStar_Format.reduce docs)
in (FStar_Format.parens uu____799))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____801 = (string_of_mlconstant c)
in (FStar_Format.text uu____801))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____803) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____805 = (ptsym currentModule path)
in (FStar_Format.text uu____805))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____821 -> (match (uu____821) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____829 = (

let uu____831 = (

let uu____832 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____832))
in (uu____831)::((FStar_Format.text "="))::(doc)::[])
in (FStar_Format.reduce1 uu____829)))
end))
in (

let uu____834 = (

let uu____835 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____835))
in (FStar_Format.cbrackets uu____834)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____842 = (is_standard_constructor ctor)
in (match (uu____842) with
| true -> begin
(

let uu____843 = (

let uu____846 = (as_standard_constructor ctor)
in (FStar_Option.get uu____846))
in (Prims.snd uu____843))
end
| uu____852 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____858 = (is_standard_constructor ctor)
in (match (uu____858) with
| true -> begin
(

let uu____859 = (

let uu____862 = (as_standard_constructor ctor)
in (FStar_Option.get uu____862))
in (Prims.snd uu____859))
end
| uu____868 -> begin
(ptctor currentModule ctor)
end))
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____878, uu____879) -> begin
(

let uu____882 = (

let uu____884 = (

let uu____886 = (

let uu____887 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens uu____887))
in (uu____886)::[])
in ((FStar_Format.text name))::uu____884)
in (FStar_Format.reduce1 uu____882))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____893 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____893))) es)
in (

let docs = (

let uu____897 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens uu____897))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____899, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____909 = (

let uu____911 = (

let uu____913 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____913)::[])
in (FStar_Format.hardline)::uu____911)
in (FStar_Format.reduce uu____909))
end
| uu____914 -> begin
FStar_Format.empty
end)
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____920 = (

let uu____921 = (

let uu____923 = (

let uu____925 = (

let uu____927 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (uu____927)::[])
in (doc)::uu____925)
in (pre)::uu____923)
in (FStar_Format.combine FStar_Format.hardline uu____921))
in (FStar_Format.parens uu____920)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____934)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____936; FStar_Extraction_ML_Syntax.loc = uu____937})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____939))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____941; FStar_Extraction_ML_Syntax.loc = uu____942})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____972; FStar_Extraction_ML_Syntax.loc = uu____973}, branches); FStar_Extraction_ML_Syntax.mlty = uu____975; FStar_Extraction_ML_Syntax.loc = uu____976} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
branches
end
| e -> begin
(((FStar_Extraction_ML_Syntax.MLP_Wild), (None), (e)))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try (((scrutinee), (branches))); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::(e2)::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1007; FStar_Extraction_ML_Syntax.loc = uu____1008}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1018; FStar_Extraction_ML_Syntax.loc = uu____1019}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| uu____1024 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1035 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens uu____1035))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = (

let uu____1042 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1042) with
| true -> begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end
| uu____1044 -> begin
(

let uu____1045 = (

let uu____1047 = (

let uu____1049 = (

let uu____1051 = (

let uu____1052 = (ptsym currentModule f)
in (FStar_Format.text uu____1052))
in (uu____1051)::[])
in ((FStar_Format.text "."))::uu____1049)
in (e)::uu____1047)
in (FStar_Format.reduce uu____1045))
end))
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1070 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1070) with
| true -> begin
(

let uu____1071 = (

let uu____1073 = (

let uu____1075 = (

let uu____1077 = (match (xt) with
| Some (xxt) -> begin
(

let uu____1079 = (

let uu____1081 = (

let uu____1083 = (doc_of_mltype currentModule outer xxt)
in (uu____1083)::[])
in ((FStar_Format.text " : "))::uu____1081)
in (FStar_Format.reduce1 uu____1079))
end
| uu____1084 -> begin
(FStar_Format.text "")
end)
in (uu____1077)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1075)
in ((FStar_Format.text "("))::uu____1073)
in (FStar_Format.reduce1 uu____1071))
end
| uu____1086 -> begin
(FStar_Format.text x)
end)))
in (

let ids = (FStar_List.map (fun uu____1093 -> (match (uu____1093) with
| ((x, uu____1099), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (

let uu____1107 = (

let uu____1109 = (

let uu____1111 = (FStar_Format.reduce1 ids)
in (uu____1111)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::uu____1109)
in (FStar_Format.reduce1 uu____1107))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (

let uu____1119 = (

let uu____1121 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1122 = (

let uu____1124 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1124)::((FStar_Format.text "end"))::[])
in (uu____1121)::uu____1122))
in (FStar_Format.combine FStar_Format.hardline uu____1119))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (

let uu____1135 = (

let uu____1137 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1138 = (

let uu____1140 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1143 = (

let uu____1145 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1146 = (

let uu____1148 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1148)::((FStar_Format.text "end"))::[])
in (uu____1145)::uu____1146))
in (uu____1140)::uu____1143))
in (uu____1137)::uu____1138))
in (FStar_Format.combine FStar_Format.hardline uu____1135))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (

let uu____1170 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (uu____1170)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1174 = (

let uu____1176 = (

let uu____1178 = (

let uu____1179 = (ptctor currentModule exn)
in (FStar_Format.text uu____1179))
in (uu____1178)::[])
in ((FStar_Format.text "raise"))::uu____1176)
in (FStar_Format.reduce1 uu____1174))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1188 = (

let uu____1190 = (

let uu____1192 = (

let uu____1193 = (ptctor currentModule exn)
in (FStar_Format.text uu____1193))
in (

let uu____1194 = (

let uu____1196 = (

let uu____1197 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens uu____1197))
in (uu____1196)::[])
in (uu____1192)::uu____1194))
in ((FStar_Format.text "raise"))::uu____1190)
in (FStar_Format.reduce1 uu____1188)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(

let uu____1210 = (

let uu____1212 = (

let uu____1214 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____1217 = (

let uu____1219 = (

let uu____1221 = (

let uu____1222 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1222))
in (uu____1221)::[])
in ((FStar_Format.text "with"))::uu____1219)
in (uu____1214)::uu____1217))
in ((FStar_Format.text "try"))::uu____1212)
in (FStar_Format.combine FStar_Format.hardline uu____1210))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1228 = (

let uu____1234 = (as_bin_op p)
in (FStar_Option.get uu____1234))
in (match (uu____1228) with
| (uu____1246, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1263 = (

let uu____1266 = (as_uni_op p)
in (FStar_Option.get uu____1266))
in (match (uu____1263) with
| (uu____1272, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (FStar_Format.reduce1 (((FStar_Format.text txt))::((FStar_Format.parens e1))::[]))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(

let uu____1281 = (string_of_mlconstant c)
in (FStar_Format.text uu____1281))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1298 -> (match (uu____1298) with
| (name, p) -> begin
(

let uu____1303 = (

let uu____1305 = (

let uu____1306 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1306))
in (

let uu____1308 = (

let uu____1310 = (

let uu____1312 = (doc_of_pattern currentModule p)
in (uu____1312)::[])
in ((FStar_Format.text "="))::uu____1310)
in (uu____1305)::uu____1308))
in (FStar_Format.reduce1 uu____1303))
end))
in (

let uu____1313 = (

let uu____1314 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1314))
in (FStar_Format.cbrackets uu____1313)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1321 = (is_standard_constructor ctor)
in (match (uu____1321) with
| true -> begin
(

let uu____1322 = (

let uu____1325 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1325))
in (Prims.snd uu____1322))
end
| uu____1331 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1337 = (is_standard_constructor ctor)
in (match (uu____1337) with
| true -> begin
(

let uu____1338 = (

let uu____1341 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1341))
in (Prims.snd uu____1338))
end
| uu____1347 -> begin
(ptctor currentModule ctor)
end))
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____1353 = (

let uu____1355 = (

let uu____1356 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____1356))
in (

let uu____1357 = (

let uu____1359 = (

let uu____1361 = (doc_of_pattern currentModule xs)
in (uu____1361)::[])
in ((FStar_Format.text "::"))::uu____1359)
in (uu____1355)::uu____1357))
in (FStar_Format.reduce uu____1353))
end
| (uu____1362, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1363))::[]) -> begin
(

let uu____1366 = (

let uu____1368 = (

let uu____1370 = (

let uu____1371 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____1371))
in (uu____1370)::[])
in ((FStar_Format.text name))::uu____1368)
in (FStar_Format.reduce1 uu____1366))
end
| uu____1372 -> begin
(

let uu____1376 = (

let uu____1378 = (

let uu____1380 = (

let uu____1381 = (

let uu____1382 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____1382))
in (FStar_Format.parens uu____1381))
in (uu____1380)::[])
in ((FStar_Format.text name))::uu____1378)
in (FStar_Format.reduce1 uu____1376))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____1390 = (FStar_Format.combine (FStar_Format.text ", ") ps)
in (FStar_Format.parens uu____1390)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1398 -> (match (uu____1398) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(

let uu____1405 = (

let uu____1407 = (

let uu____1409 = (doc_of_pattern currentModule p)
in (uu____1409)::[])
in ((FStar_Format.text "|"))::uu____1407)
in (FStar_Format.reduce1 uu____1405))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____1414 = (

let uu____1416 = (

let uu____1418 = (doc_of_pattern currentModule p)
in (uu____1418)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::uu____1416)
in (FStar_Format.reduce1 uu____1414)))
end)
in (

let uu____1419 = (

let uu____1421 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1422 = (

let uu____1424 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1424)::((FStar_Format.text "end"))::[])
in (uu____1421)::uu____1422))
in (FStar_Format.combine FStar_Format.hardline uu____1419)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1428 -> (match (uu____1428) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1441 -> (match (uu____1441) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1444; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun uu____1461 -> (match (uu____1461) with
| (x, uu____1465) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1467 -> begin
(

let uu____1468 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1468) with
| true -> begin
(match (tys) with
| (Some ((_)::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end
| uu____1484 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| (None) | (Some ((_)::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end
| uu____1500 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____1501 = (

let uu____1503 = (

let uu____1505 = (FStar_Format.reduce1 ids)
in (uu____1505)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in ((FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::uu____1503)
in (FStar_Format.reduce1 uu____1501))))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1507 -> begin
(FStar_Format.text "let")
end)
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1514 -> begin
(FStar_Format.text "and")
end))::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1515 -> (match (uu____1515) with
| (lineno, file) -> begin
(

let uu____1518 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1518) with
| true -> begin
FStar_Format.empty
end
| uu____1519 -> begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1538 -> (match (uu____1538) with
| (uu____1547, x, mangle_opt, tparams, body) -> begin
(

let x = (match (mangle_opt) with
| None -> begin
x
end
| Some (y) -> begin
y
end)
in (

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| uu____1562 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (

let uu____1567 = (FStar_Format.combine (FStar_Format.text ", ") doc)
in (FStar_Format.parens uu____1567)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1584 -> (match (uu____1584) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (

let uu____1593 = (

let uu____1594 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1594))
in (FStar_Format.cbrackets uu____1593)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1609 -> (match (uu____1609) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1617 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (FStar_Format.combine (FStar_Format.text " * ") tys)
in (FStar_Format.reduce1 (((FStar_Format.text name))::((FStar_Format.text "of"))::(tys)::[]))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (FStar_Format.reduce1 (((FStar_Format.text "|"))::(d)::[]))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (

let uu____1633 = (

let uu____1635 = (

let uu____1637 = (

let uu____1638 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text uu____1638))
in (uu____1637)::[])
in (tparams)::uu____1635)
in (FStar_Format.reduce1 uu____1633))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (

let uu____1642 = (

let uu____1644 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (uu____1644)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline uu____1642)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = (match (((FStar_List.length doc) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1659 = (

let uu____1661 = (

let uu____1663 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (uu____1663)::[])
in ((FStar_Format.text "type"))::uu____1661)
in (FStar_Format.reduce1 uu____1659))
end
| uu____1664 -> begin
(FStar_Format.text "")
end)
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____1679 = (

let uu____1681 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____1682 = (

let uu____1684 = (doc_of_sig currentModule subsig)
in (

let uu____1685 = (

let uu____1687 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____1687)::[])
in (uu____1684)::uu____1685))
in (uu____1681)::uu____1682))
in (FStar_Format.combine FStar_Format.hardline uu____1679))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (

let uu____1699 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens uu____1699))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1701, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text "val"))::((FStar_Format.text x))::((FStar_Format.text ": "))::(ty)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (

let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (

let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))


let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (

let uu____1733 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens uu____1733))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1736, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____1742 = (

let uu____1744 = (

let uu____1746 = (

let uu____1748 = (

let uu____1750 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1750)::[])
in ((FStar_Format.text "="))::uu____1748)
in ((FStar_Format.text "_"))::uu____1746)
in ((FStar_Format.text "let"))::uu____1744)
in (FStar_Format.reduce1 uu____1742))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1766) -> begin
FStar_Format.empty
end
| uu____1767 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1773 -> (match (uu____1773) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1811 -> (match (uu____1811) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun uu____1850 -> (match (uu____1850) with
| (s, uu____1854) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let uu____1869 = (

let uu____1871 = (

let uu____1873 = (

let uu____1875 = (FStar_Format.reduce sub)
in (uu____1875)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1873)
in ((FStar_Format.cat head FStar_Format.hardline))::uu____1871)
in (FStar_Format.reduce uu____1869))))))))
end))
and for1_mod = (fun istop uu____1878 -> (match (uu____1878) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (

let uu____1912 = (

let uu____1914 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1914) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end
| uu____1916 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1918 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____1912))
in (

let tail = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1920 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc = (FStar_Option.map (fun uu____1925 -> (match (uu____1925) with
| (uu____1928, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = (

let uu____1946 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1946) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____1948 -> begin
[]
end))
in (

let uu____1949 = (

let uu____1951 = (

let uu____1953 = (

let uu____1955 = (

let uu____1957 = (

let uu____1959 = (

let uu____1961 = (

let uu____1963 = (FStar_Format.reduce sub)
in (uu____1963)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1961)
in (FStar_Format.hardline)::uu____1959)
in ((FStar_Format.text "open Prims"))::uu____1957)
in (FStar_Format.hardline)::uu____1955)
in (head)::uu____1953)
in (FStar_List.append prefix uu____1951))
in (FStar_All.pipe_left FStar_Format.reduce uu____1949)))))))))
end))
in (

let docs = (FStar_List.map (fun uu____1981 -> (match (uu____1981) with
| (x, s, m) -> begin
(

let uu____2008 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____2009 = (for1_mod true ((x), (s), (m)))
in ((uu____2008), (uu____2009))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (

let uu____2029 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____2029 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (

let uu____2039 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____2039 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





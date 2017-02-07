
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


let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (

let uu____193 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____193) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____196 -> begin
(

let uu____197 = x
in (match (uu____197) with
| (ns, x) -> begin
(

let uu____202 = (path_of_ns currentModule ns)
in ((uu____202), (x)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____208 = (

let uu____209 = (

let uu____210 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____210))
in (

let uu____211 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____209 <> uu____211)))
in (match (uu____208) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____212 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| uu____221 -> begin
(

let uu____222 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____222) with
| (p, s) -> begin
(

let uu____227 = (

let uu____229 = (

let uu____231 = (ptsym_of_symbol s)
in (uu____231)::[])
in (FStar_List.append p uu____229))
in (FStar_String.concat "." uu____227))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____238 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____238) with
| (p, s) -> begin
(

let s = (

let uu____244 = (

let uu____245 = (

let uu____246 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____246))
in (

let uu____247 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____245 <> uu____247)))
in (match (uu____244) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____248 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____372 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) Prims.option = (fun uu____400 -> (match (uu____400) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____422 -> (match (uu____422) with
| (y, uu____429, uu____430) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____435 -> begin
None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____444 = (as_bin_op p)
in (uu____444 <> None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____467 -> (match (uu____467) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____480 -> (match (uu____480) with
| (y, uu____484) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____485 -> begin
None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____491 = (as_uni_op p)
in (uu____491 <> None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____508 -> (match (uu____508) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____521 -> (match (uu____521) with
| (y, uu____525) -> begin
(x = y)
end)) prim_constructors)
end
| uu____526 -> begin
None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____532 = (as_standard_constructor p)
in (uu____532 <> None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____553 inner doc -> (match (uu____553) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let uu____586 = _inner
in (match (uu____586) with
| (pi, fi) -> begin
(

let uu____591 = _outer
in (match (uu____591) with
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
| (uu____596, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____597, uu____598) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc
end
| uu____599 -> begin
(FStar_Format.parens doc)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___113_614 -> (match (uu___113_614) with
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

let uu____633 = (

let uu____634 = (escape_or escape_char_hex c)
in (Prims.strcat uu____634 "\'"))
in (Prims.strcat "\'" uu____633))
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

let uu____669 = (

let uu____670 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____670 "\""))
in (Prims.strcat "\"" uu____669))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____672 = (

let uu____673 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____673 "\""))
in (Prims.strcat "\"" uu____672))
end
| uu____674 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____695 -> begin
s
end))
in (

let uu____696 = (

let uu____697 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar uu____697))
in (FStar_Format.text uu____696)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (

let uu____705 = (

let uu____706 = (FStar_Format.combine (FStar_Format.text " * ") doc)
in (FStar_Format.hbox uu____706))
in (FStar_Format.parens uu____705))
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
| uu____715 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____721 = (

let uu____722 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.hbox uu____722))
in (FStar_Format.parens uu____721)))
end)
in (

let name = (ptsym currentModule name)
in (

let uu____724 = (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[]))
in (FStar_Format.hbox uu____724))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____726, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____734 = (

let uu____735 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____735))
in (maybe_paren outer t_prio_fun uu____734))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____736 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____736) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____737 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____788 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____788) with
| true -> begin
(

let uu____789 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FStar_Format.parens uu____789))
end
| uu____790 -> begin
(

let uu____791 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[]))
in (FStar_Format.parens uu____791))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (

let uu____801 = (FStar_Format.reduce docs)
in (FStar_Format.parens uu____801))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____803 = (string_of_mlconstant c)
in (FStar_Format.text uu____803))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____805) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____807 = (ptsym currentModule path)
in (FStar_Format.text uu____807))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____823 -> (match (uu____823) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____831 = (

let uu____833 = (

let uu____834 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____834))
in (uu____833)::((FStar_Format.text "="))::(doc)::[])
in (FStar_Format.reduce1 uu____831)))
end))
in (

let uu____836 = (

let uu____837 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____837))
in (FStar_Format.cbrackets uu____836)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____844 = (is_standard_constructor ctor)
in (match (uu____844) with
| true -> begin
(

let uu____845 = (

let uu____848 = (as_standard_constructor ctor)
in (FStar_Option.get uu____848))
in (Prims.snd uu____845))
end
| uu____854 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____860 = (is_standard_constructor ctor)
in (match (uu____860) with
| true -> begin
(

let uu____861 = (

let uu____864 = (as_standard_constructor ctor)
in (FStar_Option.get uu____864))
in (Prims.snd uu____861))
end
| uu____870 -> begin
(ptctor currentModule ctor)
end))
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____880, uu____881) -> begin
(

let uu____884 = (

let uu____886 = (

let uu____888 = (

let uu____889 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens uu____889))
in (uu____888)::[])
in ((FStar_Format.text name))::uu____886)
in (FStar_Format.reduce1 uu____884))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (

let uu____895 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____895))) es)
in (

let docs = (

let uu____899 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens uu____899))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____901, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____911 = (

let uu____913 = (

let uu____915 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____915)::[])
in (FStar_Format.hardline)::uu____913)
in (FStar_Format.reduce uu____911))
end
| uu____916 -> begin
FStar_Format.empty
end)
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____922 = (

let uu____923 = (

let uu____925 = (

let uu____927 = (

let uu____929 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (uu____929)::[])
in (doc)::uu____927)
in (pre)::uu____925)
in (FStar_Format.combine FStar_Format.hardline uu____923))
in (FStar_Format.parens uu____922)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____936)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____938; FStar_Extraction_ML_Syntax.loc = uu____939})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____941))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____943; FStar_Extraction_ML_Syntax.loc = uu____944})::[]) when (

let uu____962 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____962 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____975; FStar_Extraction_ML_Syntax.loc = uu____976}, branches); FStar_Extraction_ML_Syntax.mlty = uu____978; FStar_Extraction_ML_Syntax.loc = uu____979} when (

let uu____990 = (FStar_Extraction_ML_Syntax.idsym arg)
in (

let uu____991 = (FStar_Extraction_ML_Syntax.idsym arg')
in (uu____990 = uu____991))) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1012; FStar_Extraction_ML_Syntax.loc = uu____1013}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1023; FStar_Extraction_ML_Syntax.loc = uu____1024}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| uu____1029 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1040 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens uu____1040))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = (

let uu____1047 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1047) with
| true -> begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end
| uu____1049 -> begin
(

let uu____1050 = (

let uu____1052 = (

let uu____1054 = (

let uu____1056 = (

let uu____1057 = (ptsym currentModule f)
in (FStar_Format.text uu____1057))
in (uu____1056)::[])
in ((FStar_Format.text "."))::uu____1054)
in (e)::uu____1052)
in (FStar_Format.reduce uu____1050))
end))
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1075 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1075) with
| true -> begin
(

let uu____1076 = (

let uu____1078 = (

let uu____1080 = (

let uu____1082 = (match (xt) with
| Some (xxt) -> begin
(

let uu____1084 = (

let uu____1086 = (

let uu____1088 = (doc_of_mltype currentModule outer xxt)
in (uu____1088)::[])
in ((FStar_Format.text " : "))::uu____1086)
in (FStar_Format.reduce1 uu____1084))
end
| uu____1089 -> begin
(FStar_Format.text "")
end)
in (uu____1082)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1080)
in ((FStar_Format.text "("))::uu____1078)
in (FStar_Format.reduce1 uu____1076))
end
| uu____1091 -> begin
(FStar_Format.text x)
end)))
in (

let ids = (FStar_List.map (fun uu____1098 -> (match (uu____1098) with
| ((x, uu____1104), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (

let uu____1112 = (

let uu____1114 = (

let uu____1116 = (FStar_Format.reduce1 ids)
in (uu____1116)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::uu____1114)
in (FStar_Format.reduce1 uu____1112))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (

let uu____1124 = (

let uu____1126 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1127 = (

let uu____1129 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1129)::((FStar_Format.text "end"))::[])
in (uu____1126)::uu____1127))
in (FStar_Format.combine FStar_Format.hardline uu____1124))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (

let uu____1140 = (

let uu____1142 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1143 = (

let uu____1145 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1148 = (

let uu____1150 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1151 = (

let uu____1153 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1153)::((FStar_Format.text "end"))::[])
in (uu____1150)::uu____1151))
in (uu____1145)::uu____1148))
in (uu____1142)::uu____1143))
in (FStar_Format.combine FStar_Format.hardline uu____1140))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (

let uu____1175 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (uu____1175)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1179 = (

let uu____1181 = (

let uu____1183 = (

let uu____1184 = (ptctor currentModule exn)
in (FStar_Format.text uu____1184))
in (uu____1183)::[])
in ((FStar_Format.text "raise"))::uu____1181)
in (FStar_Format.reduce1 uu____1179))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1193 = (

let uu____1195 = (

let uu____1197 = (

let uu____1198 = (ptctor currentModule exn)
in (FStar_Format.text uu____1198))
in (

let uu____1199 = (

let uu____1201 = (

let uu____1202 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens uu____1202))
in (uu____1201)::[])
in (uu____1197)::uu____1199))
in ((FStar_Format.text "raise"))::uu____1195)
in (FStar_Format.reduce1 uu____1193)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(

let uu____1215 = (

let uu____1217 = (

let uu____1219 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____1222 = (

let uu____1224 = (

let uu____1226 = (

let uu____1227 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1227))
in (uu____1226)::[])
in ((FStar_Format.text "with"))::uu____1224)
in (uu____1219)::uu____1222))
in ((FStar_Format.text "try"))::uu____1217)
in (FStar_Format.combine FStar_Format.hardline uu____1215))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1233 = (

let uu____1239 = (as_bin_op p)
in (FStar_Option.get uu____1239))
in (match (uu____1233) with
| (uu____1251, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1268 = (

let uu____1271 = (as_uni_op p)
in (FStar_Option.get uu____1271))
in (match (uu____1268) with
| (uu____1277, txt) -> begin
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

let uu____1286 = (string_of_mlconstant c)
in (FStar_Format.text uu____1286))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1303 -> (match (uu____1303) with
| (name, p) -> begin
(

let uu____1308 = (

let uu____1310 = (

let uu____1311 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1311))
in (

let uu____1313 = (

let uu____1315 = (

let uu____1317 = (doc_of_pattern currentModule p)
in (uu____1317)::[])
in ((FStar_Format.text "="))::uu____1315)
in (uu____1310)::uu____1313))
in (FStar_Format.reduce1 uu____1308))
end))
in (

let uu____1318 = (

let uu____1319 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1319))
in (FStar_Format.cbrackets uu____1318)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1326 = (is_standard_constructor ctor)
in (match (uu____1326) with
| true -> begin
(

let uu____1327 = (

let uu____1330 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1330))
in (Prims.snd uu____1327))
end
| uu____1336 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1342 = (is_standard_constructor ctor)
in (match (uu____1342) with
| true -> begin
(

let uu____1343 = (

let uu____1346 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1346))
in (Prims.snd uu____1343))
end
| uu____1352 -> begin
(ptctor currentModule ctor)
end))
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____1358 = (

let uu____1360 = (

let uu____1361 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____1361))
in (

let uu____1362 = (

let uu____1364 = (

let uu____1366 = (doc_of_pattern currentModule xs)
in (uu____1366)::[])
in ((FStar_Format.text "::"))::uu____1364)
in (uu____1360)::uu____1362))
in (FStar_Format.reduce uu____1358))
end
| (uu____1367, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1368))::[]) -> begin
(

let uu____1371 = (

let uu____1373 = (

let uu____1375 = (

let uu____1376 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____1376))
in (uu____1375)::[])
in ((FStar_Format.text name))::uu____1373)
in (FStar_Format.reduce1 uu____1371))
end
| uu____1377 -> begin
(

let uu____1381 = (

let uu____1383 = (

let uu____1385 = (

let uu____1386 = (

let uu____1387 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____1387))
in (FStar_Format.parens uu____1386))
in (uu____1385)::[])
in ((FStar_Format.text name))::uu____1383)
in (FStar_Format.reduce1 uu____1381))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____1395 = (FStar_Format.combine (FStar_Format.text ", ") ps)
in (FStar_Format.parens uu____1395)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1403 -> (match (uu____1403) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(

let uu____1410 = (

let uu____1412 = (

let uu____1414 = (doc_of_pattern currentModule p)
in (uu____1414)::[])
in ((FStar_Format.text "|"))::uu____1412)
in (FStar_Format.reduce1 uu____1410))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____1419 = (

let uu____1421 = (

let uu____1423 = (doc_of_pattern currentModule p)
in (uu____1423)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::uu____1421)
in (FStar_Format.reduce1 uu____1419)))
end)
in (

let uu____1424 = (

let uu____1426 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1427 = (

let uu____1429 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1429)::((FStar_Format.text "end"))::[])
in (uu____1426)::uu____1427))
in (FStar_Format.combine FStar_Format.hardline uu____1424)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1433 -> (match (uu____1433) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1446 -> (match (uu____1446) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1449; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun uu____1466 -> (match (uu____1466) with
| (x, uu____1470) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1472 -> begin
(

let uu____1473 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1473) with
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
| uu____1489 -> begin
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
| uu____1505 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____1506 = (

let uu____1508 = (

let uu____1509 = (FStar_Extraction_ML_Syntax.idsym name)
in (FStar_Format.text uu____1509))
in (

let uu____1510 = (

let uu____1512 = (FStar_Format.reduce1 ids)
in (uu____1512)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in (uu____1508)::uu____1510))
in (FStar_Format.reduce1 uu____1506))))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1514 -> begin
(FStar_Format.text "let")
end)
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1521 -> begin
(FStar_Format.text "and")
end))::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1522 -> (match (uu____1522) with
| (lineno, file) -> begin
(

let uu____1525 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1525) with
| true -> begin
FStar_Format.empty
end
| uu____1526 -> begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1545 -> (match (uu____1545) with
| (uu____1554, x, mangle_opt, tparams, body) -> begin
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
(

let uu____1569 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_Format.text uu____1569))
end
| uu____1570 -> begin
(

let doc = (FStar_List.map (fun x -> (

let uu____1575 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_Format.text uu____1575))) tparams)
in (

let uu____1576 = (FStar_Format.combine (FStar_Format.text ", ") doc)
in (FStar_Format.parens uu____1576)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1593 -> (match (uu____1593) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (

let uu____1602 = (

let uu____1603 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1603))
in (FStar_Format.cbrackets uu____1602)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1618 -> (match (uu____1618) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1626 -> begin
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

let uu____1642 = (

let uu____1644 = (

let uu____1646 = (

let uu____1647 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text uu____1647))
in (uu____1646)::[])
in (tparams)::uu____1644)
in (FStar_Format.reduce1 uu____1642))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (

let uu____1651 = (

let uu____1653 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (uu____1653)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline uu____1651)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = (match (((FStar_List.length doc) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1668 = (

let uu____1670 = (

let uu____1672 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (uu____1672)::[])
in ((FStar_Format.text "type"))::uu____1670)
in (FStar_Format.reduce1 uu____1668))
end
| uu____1673 -> begin
(FStar_Format.text "")
end)
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____1688 = (

let uu____1690 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____1691 = (

let uu____1693 = (doc_of_sig currentModule subsig)
in (

let uu____1694 = (

let uu____1696 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____1696)::[])
in (uu____1693)::uu____1694))
in (uu____1690)::uu____1691))
in (FStar_Format.combine FStar_Format.hardline uu____1688))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (

let uu____1708 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens uu____1708))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1710, ty)) -> begin
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

let uu____1742 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens uu____1742))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1745, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____1751 = (

let uu____1753 = (

let uu____1755 = (

let uu____1757 = (

let uu____1759 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1759)::[])
in ((FStar_Format.text "="))::uu____1757)
in ((FStar_Format.text "_"))::uu____1755)
in ((FStar_Format.text "let"))::uu____1753)
in (FStar_Format.reduce1 uu____1751))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1775) -> begin
FStar_Format.empty
end
| uu____1776 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1782 -> (match (uu____1782) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1820 -> (match (uu____1820) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun uu____1859 -> (match (uu____1859) with
| (s, uu____1863) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let uu____1878 = (

let uu____1880 = (

let uu____1882 = (

let uu____1884 = (FStar_Format.reduce sub)
in (uu____1884)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1882)
in ((FStar_Format.cat head FStar_Format.hardline))::uu____1880)
in (FStar_Format.reduce uu____1878))))))))
end))
and for1_mod = (fun istop uu____1887 -> (match (uu____1887) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (

let uu____1921 = (

let uu____1923 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1923) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end
| uu____1925 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1927 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____1921))
in (

let tail = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1929 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc = (FStar_Option.map (fun uu____1934 -> (match (uu____1934) with
| (uu____1937, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = (

let uu____1955 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1955) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____1957 -> begin
[]
end))
in (

let uu____1958 = (

let uu____1960 = (

let uu____1962 = (

let uu____1964 = (

let uu____1966 = (

let uu____1968 = (

let uu____1970 = (

let uu____1972 = (FStar_Format.reduce sub)
in (uu____1972)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____1970)
in (FStar_Format.hardline)::uu____1968)
in ((FStar_Format.text "open Prims"))::uu____1966)
in (FStar_Format.hardline)::uu____1964)
in (head)::uu____1962)
in (FStar_List.append prefix uu____1960))
in (FStar_All.pipe_left FStar_Format.reduce uu____1958)))))))))
end))
in (

let docs = (FStar_List.map (fun uu____1990 -> (match (uu____1990) with
| (x, s, m) -> begin
(

let uu____2017 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____2018 = (for1_mod true ((x), (s), (m)))
in ((uu____2017), (uu____2018))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (

let uu____2038 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____2038 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (

let uu____2048 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____2048 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





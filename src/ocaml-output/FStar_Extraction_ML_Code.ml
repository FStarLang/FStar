
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


let rec in_ns = (fun x -> (match (x) with
| ([], uu____113) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (uu____127, uu____128) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| uu____146 -> begin
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

let uu____181 = (FStar_Util.first_N cg_len ns)
in (match (uu____181) with
| (pfx, sfx) -> begin
(match ((pfx = cg_path)) with
| true -> begin
(

let uu____201 = (

let uu____203 = (

let uu____205 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (uu____205)::[])
in (FStar_List.append pfx uu____203))
in FStar_Pervasives_Native.Some (uu____201))
end
| uu____207 -> begin
FStar_Pervasives_Native.None
end)
end))
end
| uu____209 -> begin
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

let uu____224 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____224) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____227 -> begin
(

let uu____228 = x
in (match (uu____228) with
| (ns, x1) -> begin
(

let uu____233 = (path_of_ns currentModule ns)
in ((uu____233), (x1)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____240 = (

let uu____241 = (

let uu____242 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase uu____242))
in (

let uu____243 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____241 <> uu____243)))
in (match (uu____240) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____244 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (FStar_Pervasives_Native.fst mlp))) with
| true -> begin
(ptsym_of_symbol (FStar_Pervasives_Native.snd mlp))
end
| uu____255 -> begin
(

let uu____256 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____256) with
| (p, s) -> begin
(

let uu____261 = (

let uu____263 = (

let uu____265 = (ptsym_of_symbol s)
in (uu____265)::[])
in (FStar_List.append p uu____263))
in (FStar_String.concat "." uu____261))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____274 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____274) with
| (p, s) -> begin
(

let s1 = (

let uu____280 = (

let uu____281 = (

let uu____282 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase uu____282))
in (

let uu____283 = (FStar_String.get s (Prims.parse_int "0"))
in (uu____281 <> uu____283)))
in (match (uu____280) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____284 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s1)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____409 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) FStar_Pervasives_Native.option = (fun uu____439 -> (match (uu____439) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____465 -> (match (uu____465) with
| (y, uu____472, uu____473) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____478 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____488 = (as_bin_op p)
in (uu____488 <> FStar_Pervasives_Native.None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____512 -> (match (uu____512) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____528 -> (match (uu____528) with
| (y, uu____532) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____533 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____540 = (as_uni_op p)
in (uu____540 <> FStar_Pervasives_Native.None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) FStar_Pervasives_Native.option = (fun uu____559 -> (match (uu____559) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____575 -> (match (uu____575) with
| (y, uu____579) -> begin
(x = y)
end)) prim_constructors)
end
| uu____580 -> begin
FStar_Pervasives_Native.None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (

let uu____587 = (as_standard_constructor p)
in (uu____587 <> FStar_Pervasives_Native.None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____611 inner doc1 -> (match (uu____611) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side1 -> (

let uu____644 = _inner
in (match (uu____644) with
| (pi, fi) -> begin
(

let uu____649 = _outer
in (match (uu____649) with
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
| (uu____654, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____655, uu____656) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc1
end
| uu____657 -> begin
(FStar_Format.parens doc1)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___118_676 -> (match (uu___118_676) with
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

let uu____696 = (

let uu____697 = (escape_or escape_char_hex c)
in (Prims.strcat uu____697 "\'"))
in (Prims.strcat "\'" uu____696))
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int32)) -> begin
(Prims.strcat s "l")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (FStar_Const.Signed, FStar_Const.Int64)) -> begin
(Prims.strcat s "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____711, FStar_Const.Int8)) -> begin
s
end
| FStar_Extraction_ML_Syntax.MLC_Int (s, FStar_Pervasives_Native.Some (uu____718, FStar_Const.Int16)) -> begin
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

let uu____733 = (

let uu____734 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat uu____734 "\""))
in (Prims.strcat "\"" uu____733))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(

let uu____736 = (

let uu____737 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat uu____737 "\""))
in (Prims.strcat "\"" uu____736))
end
| uu____738 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____759 -> begin
s
end))
in (

let uu____760 = (

let uu____761 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar uu____761))
in (FStar_Format.text uu____760)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc1 = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc2 = (

let uu____769 = (

let uu____770 = (FStar_Format.combine (FStar_Format.text " * ") doc1)
in (FStar_Format.hbox uu____770))
in (FStar_Format.parens uu____769))
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
| uu____779 -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____785 = (

let uu____786 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.hbox uu____786))
in (FStar_Format.parens uu____785)))
end)
in (

let name1 = (ptsym currentModule name)
in (

let uu____788 = (FStar_Format.reduce1 ((args1)::((FStar_Format.text name1))::[]))
in (FStar_Format.hbox uu____788))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____790, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (

let uu____798 = (

let uu____799 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox uu____799))
in (maybe_paren outer t_prio_fun uu____798))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____800 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____800) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____801 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (

let uu____805 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer uu____805)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t, t') -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____853 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____853) with
| true -> begin
(

let uu____854 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc1)::[]))
in (FStar_Format.parens uu____854))
end
| uu____855 -> begin
(

let uu____856 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc1))::[]))
in (FStar_Format.parens uu____856))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs2 = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs1)
in (

let uu____867 = (FStar_Format.reduce docs2)
in (FStar_Format.parens uu____867))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(

let uu____869 = (string_of_mlconstant c)
in (FStar_Format.text uu____869))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____871) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(

let uu____873 = (ptsym currentModule path)
in (FStar_Format.text uu____873))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____889 -> (match (uu____889) with
| (name, e1) -> begin
(

let doc1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____897 = (

let uu____899 = (

let uu____900 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____900))
in (uu____899)::((FStar_Format.text "="))::(doc1)::[])
in (FStar_Format.reduce1 uu____897)))
end))
in (

let uu____902 = (

let uu____903 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____903))
in (FStar_Format.cbrackets uu____902)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____910 = (is_standard_constructor ctor)
in (match (uu____910) with
| true -> begin
(

let uu____911 = (

let uu____914 = (as_standard_constructor ctor)
in (FStar_Option.get uu____914))
in (FStar_Pervasives_Native.snd uu____911))
end
| uu____920 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____926 = (is_standard_constructor ctor)
in (match (uu____926) with
| true -> begin
(

let uu____927 = (

let uu____930 = (as_standard_constructor ctor)
in (FStar_Option.get uu____930))
in (FStar_Pervasives_Native.snd uu____927))
end
| uu____936 -> begin
(ptctor currentModule ctor)
end))
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc1 = (match (((name), (args1))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____946, uu____947) -> begin
(

let uu____950 = (

let uu____952 = (

let uu____954 = (

let uu____955 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____955))
in (uu____954)::[])
in ((FStar_Format.text name))::uu____952)
in (FStar_Format.reduce1 uu____950))
end)
in (maybe_paren outer e_app_prio doc1))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs1 = (FStar_List.map (fun x -> (

let uu____963 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens uu____963))) es)
in (

let docs2 = (

let uu____967 = (FStar_Format.combine (FStar_Format.text ", ") docs1)
in (FStar_Format.parens uu____967))
in docs2))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____969, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(

let uu____979 = (

let uu____981 = (

let uu____983 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (uu____983)::[])
in (FStar_Format.hardline)::uu____981)
in (FStar_Format.reduce uu____979))
end
| uu____984 -> begin
FStar_Format.empty
end)
in (

let doc1 = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let uu____990 = (

let uu____991 = (

let uu____993 = (

let uu____995 = (

let uu____997 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body1)::[]))
in (uu____997)::[])
in (doc1)::uu____995)
in (pre)::uu____993)
in (FStar_Format.combine FStar_Format.hardline uu____991))
in (FStar_Format.parens uu____990)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e1, args) -> begin
(match (((e1.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____1004)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____1006; FStar_Extraction_ML_Syntax.loc = uu____1007})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____1009))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____1011; FStar_Extraction_ML_Syntax.loc = uu____1012})::[]) when (

let uu____1030 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (uu____1030 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____1043; FStar_Extraction_ML_Syntax.loc = uu____1044}, branches); FStar_Extraction_ML_Syntax.mlty = uu____1046; FStar_Extraction_ML_Syntax.loc = uu____1047} when (

let uu____1058 = (FStar_Extraction_ML_Syntax.idsym arg)
in (

let uu____1059 = (FStar_Extraction_ML_Syntax.idsym arg')
in (uu____1058 = uu____1059))) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1080; FStar_Extraction_ML_Syntax.loc = uu____1081}, (unitVal)::[]), (e11)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e11 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e11)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e11)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____1091; FStar_Extraction_ML_Syntax.loc = uu____1092}, (unitVal)::[]), (e11)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e11)
end
| uu____1097 -> begin
(

let e2 = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e1)
in (

let args1 = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (

let uu____1108 = (FStar_Format.reduce1 ((e2)::args1))
in (FStar_Format.parens uu____1108))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e1, f) -> begin
(

let e2 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc1 = (

let uu____1115 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1115) with
| true -> begin
(FStar_Format.reduce ((e2)::((FStar_Format.text "."))::((FStar_Format.text (FStar_Pervasives_Native.snd f)))::[]))
end
| uu____1117 -> begin
(

let uu____1118 = (

let uu____1120 = (

let uu____1122 = (

let uu____1124 = (

let uu____1125 = (ptsym currentModule f)
in (FStar_Format.text uu____1125))
in (uu____1124)::[])
in ((FStar_Format.text "."))::uu____1122)
in (e2)::uu____1120)
in (FStar_Format.reduce uu____1118))
end))
in doc1))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____1143 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1143) with
| true -> begin
(

let uu____1144 = (

let uu____1146 = (

let uu____1148 = (

let uu____1150 = (match (xt) with
| FStar_Pervasives_Native.Some (xxt) -> begin
(

let uu____1152 = (

let uu____1154 = (

let uu____1156 = (doc_of_mltype currentModule outer xxt)
in (uu____1156)::[])
in ((FStar_Format.text " : "))::uu____1154)
in (FStar_Format.reduce1 uu____1152))
end
| uu____1157 -> begin
(FStar_Format.text "")
end)
in (uu____1150)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::uu____1148)
in ((FStar_Format.text "("))::uu____1146)
in (FStar_Format.reduce1 uu____1144))
end
| uu____1159 -> begin
(FStar_Format.text x)
end)))
in (

let ids1 = (FStar_List.map (fun uu____1170 -> (match (uu____1170) with
| ((x, uu____1176), xt) -> begin
(bvar_annot x (FStar_Pervasives_Native.Some (xt)))
end)) ids)
in (

let body1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc1 = (

let uu____1184 = (

let uu____1186 = (

let uu____1188 = (FStar_Format.reduce1 ids1)
in (uu____1188)::((FStar_Format.text "->"))::(body1)::[])
in ((FStar_Format.text "fun"))::uu____1186)
in (FStar_Format.reduce1 uu____1184))
in (FStar_Format.parens doc1)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.None) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1196 = (

let uu____1198 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1199 = (

let uu____1201 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (uu____1201)::((FStar_Format.text "end"))::[])
in (uu____1198)::uu____1199))
in (FStar_Format.combine FStar_Format.hardline uu____1196))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, FStar_Pervasives_Native.Some (e2)) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc1 = (

let uu____1212 = (

let uu____1214 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond1)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1215 = (

let uu____1217 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1220 = (

let uu____1222 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1223 = (

let uu____1225 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (uu____1225)::((FStar_Format.text "end"))::[])
in (uu____1222)::uu____1223))
in (uu____1217)::uu____1220))
in (uu____1214)::uu____1215))
in (FStar_Format.combine FStar_Format.hardline uu____1212))
in (maybe_paren outer e_bin_prio_if doc1)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats1 = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc1 = (

let uu____1247 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond1))::((FStar_Format.text "with"))::[]))
in (uu____1247)::pats1)
in (

let doc2 = (FStar_Format.combine FStar_Format.hardline doc1)
in (FStar_Format.parens doc2)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(

let uu____1251 = (

let uu____1253 = (

let uu____1255 = (

let uu____1256 = (ptctor currentModule exn)
in (FStar_Format.text uu____1256))
in (uu____1255)::[])
in ((FStar_Format.text "raise"))::uu____1253)
in (FStar_Format.reduce1 uu____1251))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args1 = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let uu____1265 = (

let uu____1267 = (

let uu____1269 = (

let uu____1270 = (ptctor currentModule exn)
in (FStar_Format.text uu____1270))
in (

let uu____1271 = (

let uu____1273 = (

let uu____1274 = (FStar_Format.combine (FStar_Format.text ", ") args1)
in (FStar_Format.parens uu____1274))
in (uu____1273)::[])
in (uu____1269)::uu____1271))
in ((FStar_Format.text "raise"))::uu____1267)
in (FStar_Format.reduce1 uu____1265)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e1, pats) -> begin
(

let uu____1287 = (

let uu____1289 = (

let uu____1291 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let uu____1294 = (

let uu____1296 = (

let uu____1298 = (

let uu____1299 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline uu____1299))
in (uu____1298)::[])
in ((FStar_Format.text "with"))::uu____1296)
in (uu____1291)::uu____1294))
in ((FStar_Format.text "try"))::uu____1289)
in (FStar_Format.combine FStar_Format.hardline uu____1287))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1305 = (

let uu____1311 = (as_bin_op p)
in (FStar_Option.get uu____1311))
in (match (uu____1305) with
| (uu____1323, prio, txt) -> begin
(

let e11 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e21 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc1 = (FStar_Format.reduce1 ((e11)::((FStar_Format.text txt))::(e21)::[]))
in (FStar_Format.parens doc1))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1340 = (

let uu____1343 = (as_uni_op p)
in (FStar_Option.get uu____1343))
in (match (uu____1340) with
| (uu____1349, txt) -> begin
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

let uu____1358 = (string_of_mlconstant c)
in (FStar_Format.text uu____1358))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (FStar_Pervasives_Native.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1375 -> (match (uu____1375) with
| (name, p) -> begin
(

let uu____1380 = (

let uu____1382 = (

let uu____1383 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text uu____1383))
in (

let uu____1385 = (

let uu____1387 = (

let uu____1389 = (doc_of_pattern currentModule p)
in (uu____1389)::[])
in ((FStar_Format.text "="))::uu____1387)
in (uu____1382)::uu____1385))
in (FStar_Format.reduce1 uu____1380))
end))
in (

let uu____1390 = (

let uu____1391 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1391))
in (FStar_Format.cbrackets uu____1390)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1398 = (is_standard_constructor ctor)
in (match (uu____1398) with
| true -> begin
(

let uu____1399 = (

let uu____1402 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1402))
in (FStar_Pervasives_Native.snd uu____1399))
end
| uu____1408 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1414 = (is_standard_constructor ctor)
in (match (uu____1414) with
| true -> begin
(

let uu____1415 = (

let uu____1418 = (as_standard_constructor ctor)
in (FStar_Option.get uu____1418))
in (FStar_Pervasives_Native.snd uu____1415))
end
| uu____1424 -> begin
(ptctor currentModule ctor)
end))
in (

let doc1 = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(

let uu____1430 = (

let uu____1432 = (

let uu____1433 = (doc_of_pattern currentModule x)
in (FStar_Format.parens uu____1433))
in (

let uu____1434 = (

let uu____1436 = (

let uu____1438 = (doc_of_pattern currentModule xs)
in (uu____1438)::[])
in ((FStar_Format.text "::"))::uu____1436)
in (uu____1432)::uu____1434))
in (FStar_Format.reduce uu____1430))
end
| (uu____1439, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1440))::[]) -> begin
(

let uu____1443 = (

let uu____1445 = (

let uu____1447 = (

let uu____1448 = (FStar_List.hd pats)
in (doc_of_pattern currentModule uu____1448))
in (uu____1447)::[])
in ((FStar_Format.text name))::uu____1445)
in (FStar_Format.reduce1 uu____1443))
end
| uu____1449 -> begin
(

let uu____1453 = (

let uu____1455 = (

let uu____1457 = (

let uu____1458 = (

let uu____1459 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") uu____1459))
in (FStar_Format.parens uu____1458))
in (uu____1457)::[])
in ((FStar_Format.text name))::uu____1455)
in (FStar_Format.reduce1 uu____1453))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc1)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let uu____1467 = (FStar_Format.combine (FStar_Format.text ", ") ps1)
in (FStar_Format.parens uu____1467)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps1 = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps2 = (FStar_List.map FStar_Format.parens ps1)
in (FStar_Format.combine (FStar_Format.text " | ") ps2)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1475 -> (match (uu____1475) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1482 = (

let uu____1484 = (

let uu____1486 = (doc_of_pattern currentModule p)
in (uu____1486)::[])
in ((FStar_Format.text "|"))::uu____1484)
in (FStar_Format.reduce1 uu____1482))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let c1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (

let uu____1491 = (

let uu____1493 = (

let uu____1495 = (doc_of_pattern currentModule p)
in (uu____1495)::((FStar_Format.text "when"))::(c1)::[])
in ((FStar_Format.text "|"))::uu____1493)
in (FStar_Format.reduce1 uu____1491)))
end)
in (

let uu____1496 = (

let uu____1498 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (

let uu____1499 = (

let uu____1501 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1501)::((FStar_Format.text "end"))::[])
in (uu____1498)::uu____1499))
in (FStar_Format.combine FStar_Format.hardline uu____1496)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1505 -> (match (uu____1505) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1518 -> (match (uu____1518) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1521; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1531 -> begin
(

let uu____1532 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1532) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.Some ((uu____1533)::uu____1534, uu____1535) -> begin
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
| uu____1549 -> begin
(match (top_level) with
| true -> begin
(match (tys) with
| FStar_Pervasives_Native.None -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ((uu____1550)::uu____1551, uu____1552) -> begin
(FStar_Format.text "")
end
| FStar_Pervasives_Native.Some ([], ty) -> begin
(

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty1)::[])))
end)
end
| uu____1566 -> begin
(FStar_Format.text "")
end)
end))
end)
in (

let uu____1567 = (

let uu____1569 = (

let uu____1570 = (FStar_Extraction_ML_Syntax.idsym name)
in (FStar_Format.text uu____1570))
in (

let uu____1571 = (

let uu____1573 = (FStar_Format.reduce1 ids)
in (uu____1573)::(ty_annot)::((FStar_Format.text "="))::(e1)::[])
in (uu____1569)::uu____1571))
in (FStar_Format.reduce1 uu____1567)))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1575 -> begin
(FStar_Format.text "let")
end)
in (

let lets1 = (FStar_List.map for1 lets)
in (

let lets2 = (FStar_List.mapi (fun i doc1 -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1584 -> begin
(FStar_Format.text "and")
end))::(doc1)::[]))) lets1)
in (FStar_Format.combine FStar_Format.hardline lets2)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1585 -> (match (uu____1585) with
| (lineno, file) -> begin
(

let uu____1588 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1588) with
| true -> begin
FStar_Format.empty
end
| uu____1589 -> begin
(

let file1 = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file1 "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1611 -> (match (uu____1611) with
| (uu____1621, x, mangle_opt, tparams, uu____1625, body) -> begin
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

let uu____1637 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1637))
end
| uu____1638 -> begin
(

let doc1 = (FStar_List.map (fun x2 -> (

let uu____1645 = (FStar_Extraction_ML_Syntax.idsym x2)
in (FStar_Format.text uu____1645))) tparams)
in (

let uu____1646 = (FStar_Format.combine (FStar_Format.text ", ") doc1)
in (FStar_Format.parens uu____1646)))
end)
in (

let forbody = (fun body1 -> (match (body1) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1663 -> (match (uu____1663) with
| (name, ty) -> begin
(

let name1 = (FStar_Format.text name)
in (

let ty1 = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name1)::((FStar_Format.text ":"))::(ty1)::[]))))
end))
in (

let uu____1672 = (

let uu____1673 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") uu____1673))
in (FStar_Format.cbrackets uu____1672)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1692 -> (match (uu____1692) with
| (name, tys) -> begin
(

let uu____1706 = (FStar_List.split tys)
in (match (uu____1706) with
| (_names, tys1) -> begin
(match (tys1) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1717 -> begin
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

let uu____1736 = (

let uu____1738 = (

let uu____1740 = (

let uu____1741 = (ptsym currentModule (([]), (x1)))
in (FStar_Format.text uu____1741))
in (uu____1740)::[])
in (tparams1)::uu____1738)
in (FStar_Format.reduce1 uu____1736))
in (match (body) with
| FStar_Pervasives_Native.None -> begin
doc1
end
| FStar_Pervasives_Native.Some (body1) -> begin
(

let body2 = (forbody body1)
in (

let uu____1745 = (

let uu____1747 = (FStar_Format.reduce1 ((doc1)::((FStar_Format.text "="))::[]))
in (uu____1747)::(body2)::[])
in (FStar_Format.combine FStar_Format.hardline uu____1745)))
end)))))
end))
in (

let doc1 = (FStar_List.map for1 decls)
in (

let doc2 = (match (((FStar_List.length doc1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1766 = (

let uu____1768 = (

let uu____1770 = (FStar_Format.combine (FStar_Format.text " \n and ") doc1)
in (uu____1770)::[])
in ((FStar_Format.text "type"))::uu____1768)
in (FStar_Format.reduce1 uu____1766))
end
| uu____1771 -> begin
(FStar_Format.text "")
end)
in doc2))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(

let uu____1786 = (

let uu____1788 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (

let uu____1789 = (

let uu____1791 = (doc_of_sig currentModule subsig)
in (

let uu____1792 = (

let uu____1794 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (uu____1794)::[])
in (uu____1791)::uu____1792))
in (uu____1788)::uu____1789))
in (FStar_Format.combine FStar_Format.hardline uu____1786))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args1 = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args2 = (

let uu____1806 = (FStar_Format.combine (FStar_Format.text " * ") args1)
in (FStar_Format.parens uu____1806))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args2)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1808, ty)) -> begin
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

let uu____1855 = (FStar_Format.combine (FStar_Format.text " * ") args2)
in (FStar_Format.parens uu____1855))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args3)::[])))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1858, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(

let uu____1864 = (

let uu____1866 = (

let uu____1868 = (

let uu____1870 = (

let uu____1872 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (uu____1872)::[])
in ((FStar_Format.text "="))::uu____1870)
in ((FStar_Format.text "_"))::uu____1868)
in ((FStar_Format.text "let"))::uu____1866)
in (FStar_Format.reduce1 uu____1864))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs1 = (FStar_List.map (fun x -> (

let doc1 = (doc_of_mod1 currentModule x)
in (doc1)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1893) -> begin
FStar_Format.empty
end
| uu____1894 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs1))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1901 -> (match (uu____1901) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1939 -> (match (uu____1939) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let x1 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head1 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x1))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail1 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc1 = (FStar_Option.map (fun uu____1981 -> (match (uu____1981) with
| (s, uu____1985) -> begin
(doc_of_sig x1 s)
end)) sigmod)
in (

let sub2 = (FStar_List.map for1_sig sub1)
in (

let sub3 = (FStar_List.map (fun x2 -> (FStar_Format.reduce ((x2)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

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
in ((FStar_Format.cat head1 FStar_Format.hardline))::uu____2003)
in (FStar_Format.reduce uu____2001))))))))
end))
and for1_mod = (fun istop uu____2010 -> (match (uu____2010) with
| (mod_name, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub1)) -> begin
(

let target_mod_name = (FStar_Extraction_ML_Util.flatten_mlpath mod_name)
in (

let maybe_open_pervasives = (match (mod_name) with
| (("FStar")::[], "Pervasives") -> begin
[]
end
| uu____2047 -> begin
(

let pervasives1 = (FStar_Extraction_ML_Util.flatten_mlpath ((("FStar")::[]), ("Pervasives")))
in (FStar_Format.hardline)::((FStar_Format.text (Prims.strcat "open " pervasives1)))::[])
end)
in (

let head1 = (

let uu____2054 = (

let uu____2056 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2056) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::[]
end
| uu____2058 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text target_mod_name))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____2060 -> begin
[]
end)
end))
in (FStar_Format.reduce1 uu____2054))
in (

let tail1 = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____2062 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc1 = (FStar_Option.map (fun uu____2070 -> (match (uu____2070) with
| (uu____2073, m) -> begin
(doc_of_mod target_mod_name m)
end)) sigmod)
in (

let sub2 = (FStar_List.map (for1_mod false) sub1)
in (

let sub3 = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub2)
in (

let prefix1 = (

let uu____2092 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____2092) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____2094 -> begin
[]
end))
in (

let uu____2095 = (

let uu____2097 = (

let uu____2099 = (

let uu____2101 = (

let uu____2103 = (

let uu____2105 = (

let uu____2107 = (FStar_Format.reduce sub3)
in (uu____2107)::((FStar_Format.cat tail1 FStar_Format.hardline))::[])
in ((match (doc1) with
| FStar_Pervasives_Native.None -> begin
FStar_Format.empty
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::uu____2105)
in (FStar_Format.hardline)::uu____2103)
in (FStar_List.append maybe_open_pervasives uu____2101))
in (FStar_List.append ((head1)::(FStar_Format.hardline)::((FStar_Format.text "open Prims"))::[]) uu____2099))
in (FStar_List.append prefix1 uu____2097))
in (FStar_All.pipe_left FStar_Format.reduce uu____2095))))))))))
end))
in (

let docs1 = (FStar_List.map (fun uu____2131 -> (match (uu____2131) with
| (x, s, m) -> begin
(

let uu____2158 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let uu____2159 = (for1_mod true ((x), (s), (m)))
in ((uu____2158), (uu____2159))))
end)) mllib)
in docs1))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2182 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr uu____2182 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc1 = (

let uu____2194 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype uu____2194 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc1)))





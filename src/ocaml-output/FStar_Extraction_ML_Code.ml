
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
Some ((let _0_284 = (let _0_283 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_0_283)::[])
in (FStar_List.append pfx _0_284)))
end
| uu____173 -> begin
None
end)
end))
end
| uu____175 -> begin
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
| uu____190 -> begin
(

let uu____191 = x
in (match (uu____191) with
| (ns, x) -> begin
(let _0_285 = (path_of_ns currentModule ns)
in ((_0_285), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____200 = (let _0_287 = (FStar_Char.lowercase (FStar_String.get s (Prims.parse_int "0")))
in (let _0_286 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_287 <> _0_286)))
in (match (uu____200) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____201 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| uu____210 -> begin
(

let uu____211 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____211) with
| (p, s) -> begin
(let _0_290 = (let _0_289 = (let _0_288 = (ptsym_of_symbol s)
in (_0_288)::[])
in (FStar_List.append p _0_289))
in (FStar_String.concat "." _0_290))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____222 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____222) with
| (p, s) -> begin
(

let s = (

let uu____228 = (let _0_292 = (FStar_Char.uppercase (FStar_String.get s (Prims.parse_int "0")))
in (let _0_291 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_292 <> _0_291)))
in (match (uu____228) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____229 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____353 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) Prims.option = (fun uu____381 -> (match (uu____381) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____403 -> (match (uu____403) with
| (y, uu____410, uu____411) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____416 -> begin
None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_293 = (as_bin_op p)
in (_0_293 <> None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____441 -> (match (uu____441) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____454 -> (match (uu____454) with
| (y, uu____458) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____459 -> begin
None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_294 = (as_uni_op p)
in (_0_294 <> None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____478 -> (match (uu____478) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____491 -> (match (uu____491) with
| (y, uu____495) -> begin
(x = y)
end)) prim_constructors)
end
| uu____496 -> begin
None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_295 = (as_standard_constructor p)
in (_0_295 <> None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____519 inner doc -> (match (uu____519) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let uu____552 = _inner
in (match (uu____552) with
| (pi, fi) -> begin
(

let uu____557 = _outer
in (match (uu____557) with
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
| (uu____562, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____563, uu____564) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc
end
| uu____565 -> begin
(FStar_Format.parens doc)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___126_580 -> (match (uu___126_580) with
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
(let _0_297 = (let _0_296 = (escape_or escape_char_hex c)
in (Prims.strcat _0_296 "\'"))
in (Prims.strcat "\'" _0_297))
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
(let _0_299 = (let _0_298 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _0_298 "\""))
in (Prims.strcat "\"" _0_299))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _0_301 = (let _0_300 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _0_300 "\""))
in (Prims.strcat "\"" _0_301))
end
| uu____634 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____655 -> begin
s
end))
in (FStar_Format.text (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (FStar_Format.parens (FStar_Format.hbox (FStar_Format.combine (FStar_Format.text " * ") doc)))
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
| uu____671 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (FStar_Format.parens (FStar_Format.hbox (FStar_Format.combine (FStar_Format.text ", ") args))))
end)
in (

let name = (ptsym currentModule name)
in (FStar_Format.hbox (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[])))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____679, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _0_302 = (FStar_Format.hbox (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[])))
in (maybe_paren outer t_prio_fun _0_302))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____687 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____687) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____688 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _0_303 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _0_303)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____739 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____739) with
| true -> begin
(FStar_Format.parens (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[])))
end
| uu____740 -> begin
(FStar_Format.parens (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[])))
end)))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.parens (FStar_Format.reduce docs))))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(FStar_Format.text (string_of_mlconstant c))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____752) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(FStar_Format.text (ptsym currentModule path))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____769 -> (match (uu____769) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (FStar_Format.reduce1 (let _0_304 = (FStar_Format.text (ptsym currentModule ((path), (name))))
in (_0_304)::((FStar_Format.text "="))::(doc)::[])))
end))
in (FStar_Format.cbrackets (let _0_305 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_305))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____783 = (is_standard_constructor ctor)
in (match (uu____783) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____786 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____792 = (is_standard_constructor ctor)
in (match (uu____792) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____795 -> begin
(ptctor currentModule ctor)
end))
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____805, uu____806) -> begin
(FStar_Format.reduce1 (let _0_307 = (let _0_306 = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") args))
in (_0_306)::[])
in ((FStar_Format.text name))::_0_307))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (FStar_Format.parens (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x))) es)
in (

let docs = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") docs))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____818, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(FStar_Format.reduce (let _0_309 = (let _0_308 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_0_308)::[])
in (FStar_Format.hardline)::_0_309))
end
| uu____828 -> begin
FStar_Format.empty
end)
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (FStar_Format.parens (let _0_313 = (let _0_312 = (let _0_311 = (let _0_310 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (_0_310)::[])
in (doc)::_0_311)
in (pre)::_0_312)
in (FStar_Format.combine FStar_Format.hardline _0_313))))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____840)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____842; FStar_Extraction_ML_Syntax.loc = uu____843})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____845))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____847; FStar_Extraction_ML_Syntax.loc = uu____848})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____878; FStar_Extraction_ML_Syntax.loc = uu____879}, branches); FStar_Extraction_ML_Syntax.mlty = uu____881; FStar_Extraction_ML_Syntax.loc = uu____882} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____913; FStar_Extraction_ML_Syntax.loc = uu____914}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____924; FStar_Extraction_ML_Syntax.loc = uu____925}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| uu____930 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (FStar_Format.parens (FStar_Format.reduce1 ((e)::args)))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = (

let uu____947 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____947) with
| true -> begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end
| uu____949 -> begin
(FStar_Format.reduce (let _0_316 = (let _0_315 = (let _0_314 = (FStar_Format.text (ptsym currentModule f))
in (_0_314)::[])
in ((FStar_Format.text "."))::_0_315)
in (e)::_0_316))
end))
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____967 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____967) with
| true -> begin
(FStar_Format.reduce1 (let _0_321 = (let _0_320 = (let _0_319 = (match (xt) with
| Some (xxt) -> begin
(FStar_Format.reduce1 (let _0_318 = (let _0_317 = (doc_of_mltype currentModule outer xxt)
in (_0_317)::[])
in ((FStar_Format.text " : "))::_0_318))
end
| uu____969 -> begin
(FStar_Format.text "")
end)
in (_0_319)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::_0_320)
in ((FStar_Format.text "("))::_0_321))
end
| uu____971 -> begin
(FStar_Format.text x)
end)))
in (

let ids = (FStar_List.map (fun uu____978 -> (match (uu____978) with
| ((x, uu____984), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (FStar_Format.reduce1 (let _0_323 = (let _0_322 = (FStar_Format.reduce1 ids)
in (_0_322)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::_0_323))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _0_327 = (let _0_326 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _0_325 = (let _0_324 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (_0_324)::((FStar_Format.text "end"))::[])
in (_0_326)::_0_325))
in (FStar_Format.combine FStar_Format.hardline _0_327))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _0_335 = (let _0_334 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _0_333 = (let _0_332 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _0_331 = (let _0_330 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (let _0_329 = (let _0_328 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (_0_328)::((FStar_Format.text "end"))::[])
in (_0_330)::_0_329))
in (_0_332)::_0_331))
in (_0_334)::_0_333))
in (FStar_Format.combine FStar_Format.hardline _0_335))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _0_336 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (_0_336)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(FStar_Format.reduce1 (let _0_338 = (let _0_337 = (FStar_Format.text (ptctor currentModule exn))
in (_0_337)::[])
in ((FStar_Format.text "raise"))::_0_338))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (FStar_Format.reduce1 (let _0_342 = (let _0_341 = (FStar_Format.text (ptctor currentModule exn))
in (let _0_340 = (let _0_339 = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") args))
in (_0_339)::[])
in (_0_341)::_0_340))
in ((FStar_Format.text "raise"))::_0_342)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _0_349 = (let _0_348 = (let _0_347 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _0_346 = (let _0_345 = (let _0_344 = (let _0_343 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _0_343))
in (_0_344)::[])
in ((FStar_Format.text "with"))::_0_345)
in (_0_347)::_0_346))
in ((FStar_Format.text "try"))::_0_348)
in (FStar_Format.combine FStar_Format.hardline _0_349))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1061 = (FStar_Option.get (as_bin_op p))
in (match (uu____1061) with
| (uu____1072, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1089 = (FStar_Option.get (as_uni_op p))
in (match (uu____1089) with
| (uu____1094, txt) -> begin
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
(FStar_Format.text (string_of_mlconstant c))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun uu____1119 -> (match (uu____1119) with
| (name, p) -> begin
(FStar_Format.reduce1 (let _0_353 = (FStar_Format.text (ptsym currentModule ((path), (name))))
in (let _0_352 = (let _0_351 = (let _0_350 = (doc_of_pattern currentModule p)
in (_0_350)::[])
in ((FStar_Format.text "="))::_0_351)
in (_0_353)::_0_352)))
end))
in (FStar_Format.cbrackets (let _0_354 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_354))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1130 = (is_standard_constructor ctor)
in (match (uu____1130) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____1133 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1139 = (is_standard_constructor ctor)
in (match (uu____1139) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____1142 -> begin
(ptctor currentModule ctor)
end))
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (let _0_358 = (FStar_Format.parens (doc_of_pattern currentModule x))
in (let _0_357 = (let _0_356 = (let _0_355 = (doc_of_pattern currentModule xs)
in (_0_355)::[])
in ((FStar_Format.text "::"))::_0_356)
in (_0_358)::_0_357)))
end
| (uu____1148, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1149))::[]) -> begin
(FStar_Format.reduce1 (let _0_361 = (let _0_360 = (let _0_359 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _0_359))
in (_0_360)::[])
in ((FStar_Format.text name))::_0_361))
end
| uu____1152 -> begin
(FStar_Format.reduce1 (let _0_364 = (let _0_363 = (FStar_Format.parens (let _0_362 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") _0_362)))
in (_0_363)::[])
in ((FStar_Format.text name))::_0_364))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") ps)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1169 -> (match (uu____1169) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(FStar_Format.reduce1 (let _0_366 = (let _0_365 = (doc_of_pattern currentModule p)
in (_0_365)::[])
in ((FStar_Format.text "|"))::_0_366))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (FStar_Format.reduce1 (let _0_368 = (let _0_367 = (doc_of_pattern currentModule p)
in (_0_367)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::_0_368)))
end)
in (let _0_372 = (let _0_371 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (let _0_370 = (let _0_369 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_0_369)::((FStar_Format.text "end"))::[])
in (_0_371)::_0_370))
in (FStar_Format.combine FStar_Format.hardline _0_372)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1183 -> (match (uu____1183) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1196 -> (match (uu____1196) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1199; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun uu____1216 -> (match (uu____1216) with
| (x, uu____1220) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1222 -> begin
(

let uu____1223 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1223) with
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
| uu____1239 -> begin
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
| uu____1255 -> begin
(FStar_Format.text "")
end)
end))
end)
in (FStar_Format.reduce1 (let _0_374 = (let _0_373 = (FStar_Format.reduce1 ids)
in (_0_373)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in ((FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_0_374))))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1257 -> begin
(FStar_Format.text "let")
end)
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1264 -> begin
(FStar_Format.text "and")
end))::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1265 -> (match (uu____1265) with
| (lineno, file) -> begin
(

let uu____1268 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1268) with
| true -> begin
FStar_Format.empty
end
| uu____1269 -> begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1288 -> (match (uu____1288) with
| (uu____1297, x, mangle_opt, tparams, body) -> begin
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
| uu____1312 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") doc)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun uu____1333 -> (match (uu____1333) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (FStar_Format.cbrackets (let _0_375 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_375))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1355 -> (match (uu____1355) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1363 -> begin
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

let doc = (FStar_Format.reduce1 (let _0_377 = (let _0_376 = (FStar_Format.text (ptsym currentModule (([]), (x))))
in (_0_376)::[])
in (tparams)::_0_377))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _0_379 = (let _0_378 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (_0_378)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _0_379)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = (match (((FStar_List.length doc) > (Prims.parse_int "0"))) with
| true -> begin
(FStar_Format.reduce1 (let _0_381 = (let _0_380 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (_0_380)::[])
in ((FStar_Format.text "type"))::_0_381))
end
| uu____1396 -> begin
(FStar_Format.text "")
end)
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _0_387 = (let _0_386 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (let _0_385 = (let _0_384 = (doc_of_sig currentModule subsig)
in (let _0_383 = (let _0_382 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (_0_382)::[])
in (_0_384)::_0_383))
in (_0_386)::_0_385))
in (FStar_Format.combine FStar_Format.hardline _0_387))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text " * ") args))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1423, ty)) -> begin
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

let args = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text " * ") args))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1457, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(FStar_Format.reduce1 (let _0_391 = (let _0_390 = (let _0_389 = (let _0_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_0_388)::[])
in ((FStar_Format.text "="))::_0_389)
in ((FStar_Format.text "_"))::_0_390)
in ((FStar_Format.text "let"))::_0_391))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1478) -> begin
FStar_Format.empty
end
| uu____1479 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1485 -> (match (uu____1485) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1523 -> (match (uu____1523) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun uu____1562 -> (match (uu____1562) with
| (s, uu____1566) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (FStar_Format.reduce (let _0_394 = (let _0_393 = (let _0_392 = (FStar_Format.reduce sub)
in (_0_392)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_0_393)
in ((FStar_Format.cat head FStar_Format.hardline))::_0_394))))))))
end))
and for1_mod = (fun istop uu____1583 -> (match (uu____1583) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (

let uu____1617 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1617) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end
| uu____1619 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1621 -> begin
[]
end)
end)))
in (

let tail = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1623 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc = (FStar_Option.map (fun uu____1628 -> (match (uu____1628) with
| (uu____1631, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = (

let uu____1649 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1649) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____1651 -> begin
[]
end))
in (let _0_402 = (let _0_401 = (let _0_400 = (let _0_399 = (let _0_398 = (let _0_397 = (let _0_396 = (let _0_395 = (FStar_Format.reduce sub)
in (_0_395)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_0_396)
in (FStar_Format.hardline)::_0_397)
in ((FStar_Format.text "open Prims"))::_0_398)
in (FStar_Format.hardline)::_0_399)
in (head)::_0_400)
in (FStar_List.append prefix _0_401))
in (FStar_All.pipe_left FStar_Format.reduce _0_402)))))))))
end))
in (

let docs = (FStar_List.map (fun uu____1669 -> (match (uu____1669) with
| (x, s, m) -> begin
(let _0_404 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _0_403 = (for1_mod true ((x), (s), (m)))
in ((_0_404), (_0_403))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _0_405 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _0_405 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _0_406 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _0_406 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





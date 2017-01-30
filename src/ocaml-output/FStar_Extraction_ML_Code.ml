
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
Some ((let _0_208 = (let _0_207 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_0_207)::[])
in (FStar_List.append pfx _0_208)))
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


let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (

let uu____188 = (FStar_Extraction_ML_Syntax.string_of_mlpath x)
in (match (uu____188) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| uu____191 -> begin
(

let uu____192 = x
in (match (uu____192) with
| (ns, x) -> begin
(let _0_209 = (path_of_ns currentModule ns)
in ((_0_209), (x)))
end))
end)))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> (

let uu____201 = (let _0_211 = (FStar_Char.lowercase (FStar_String.get s (Prims.parse_int "0")))
in (let _0_210 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_211 <> _0_210)))
in (match (uu____201) with
| true -> begin
(Prims.strcat "l__" s)
end
| uu____202 -> begin
s
end)))


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| uu____211 -> begin
(

let uu____212 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____212) with
| (p, s) -> begin
(let _0_214 = (let _0_213 = (let _0_212 = (ptsym_of_symbol s)
in (_0_212)::[])
in (FStar_List.append p _0_213))
in (FStar_String.concat "." _0_214))
end))
end))


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let uu____223 = (mlpath_of_mlpath currentModule mlp)
in (match (uu____223) with
| (p, s) -> begin
(

let s = (

let uu____229 = (let _0_216 = (FStar_Char.uppercase (FStar_String.get s (Prims.parse_int "0")))
in (let _0_215 = (FStar_String.get s (Prims.parse_int "0"))
in (_0_216 <> _0_215)))
in (match (uu____229) with
| true -> begin
(Prims.strcat "U__" s)
end
| uu____230 -> begin
s
end))
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = (fun uu____354 -> [])


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * (Prims.int * fixity) * Prims.string) Prims.option = (fun uu____382 -> (match (uu____382) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____404 -> (match (uu____404) with
| (y, uu____411, uu____412) -> begin
(x = y)
end)) infix_prim_ops)
end
| uu____417 -> begin
None
end)
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_217 = (as_bin_op p)
in (_0_217 <> None)))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____442 -> (match (uu____442) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____455 -> (match (uu____455) with
| (y, uu____459) -> begin
(x = y)
end)) prim_uni_ops)
end
| uu____460 -> begin
None
end)
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_218 = (as_uni_op p)
in (_0_218 <> None)))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> false)


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (FStar_Extraction_ML_Syntax.mlsymbol * Prims.string) Prims.option = (fun uu____479 -> (match (uu____479) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun uu____492 -> (match (uu____492) with
| (y, uu____496) -> begin
(x = y)
end)) prim_constructors)
end
| uu____497 -> begin
None
end)
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> (let _0_219 = (as_standard_constructor p)
in (_0_219 <> None)))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun uu____520 inner doc -> (match (uu____520) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let uu____553 = _inner
in (match (uu____553) with
| (pi, fi) -> begin
(

let uu____558 = _outer
in (match (uu____558) with
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
| (uu____563, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (uu____564, uu____565) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc
end
| uu____566 -> begin
(FStar_Format.parens doc)
end))
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___112_581 -> (match (uu___112_581) with
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
(let _0_221 = (let _0_220 = (escape_or escape_char_hex c)
in (Prims.strcat _0_220 "\'"))
in (Prims.strcat "\'" _0_221))
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
(let _0_223 = (let _0_222 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _0_222 "\""))
in (Prims.strcat "\"" _0_223))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _0_225 = (let _0_224 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _0_224 "\""))
in (Prims.strcat "\"" _0_225))
end
| uu____635 -> begin
(failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| uu____656 -> begin
s
end))
in (FStar_Format.text (let _0_226 = (FStar_Extraction_ML_Syntax.idsym x)
in (FStar_All.pipe_left escape_tyvar _0_226))))
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
| uu____672 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (FStar_Format.parens (FStar_Format.hbox (FStar_Format.combine (FStar_Format.text ", ") args))))
end)
in (

let name = (ptsym currentModule name)
in (FStar_Format.hbox (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[])))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu____680, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _0_227 = (FStar_Format.hbox (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[])))
in (maybe_paren outer t_prio_fun _0_227))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(

let uu____688 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____688) with
| true -> begin
(FStar_Format.text "obj")
end
| uu____689 -> begin
(FStar_Format.text "Obj.t")
end))
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let uu____740 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____740) with
| true -> begin
(FStar_Format.parens (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[])))
end
| uu____741 -> begin
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
| FStar_Extraction_ML_Syntax.MLE_Var (x, uu____753) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(FStar_Format.text (ptsym currentModule path))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun uu____770 -> (match (uu____770) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (FStar_Format.reduce1 (let _0_228 = (FStar_Format.text (ptsym currentModule ((path), (name))))
in (_0_228)::((FStar_Format.text "="))::(doc)::[])))
end))
in (FStar_Format.cbrackets (let _0_229 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_229))))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = (

let uu____784 = (is_standard_constructor ctor)
in (match (uu____784) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____787 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = (

let uu____793 = (is_standard_constructor ctor)
in (match (uu____793) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____796 -> begin
(ptctor currentModule ctor)
end))
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (uu____806, uu____807) -> begin
(FStar_Format.reduce1 (let _0_231 = (let _0_230 = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") args))
in (_0_230)::[])
in ((FStar_Format.text name))::_0_231))
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
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, uu____819, lets), body) -> begin
(

let pre = (match ((e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc)) with
| true -> begin
(FStar_Format.reduce (let _0_233 = (let _0_232 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_0_232)::[])
in (FStar_Format.hardline)::_0_233))
end
| uu____829 -> begin
FStar_Format.empty
end)
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (FStar_Format.parens (let _0_237 = (let _0_236 = (let _0_235 = (let _0_234 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (_0_234)::[])
in (doc)::_0_235)
in (pre)::_0_236)
in (FStar_Format.combine FStar_Format.hardline _0_237))))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((uu____841)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = uu____843; FStar_Extraction_ML_Syntax.loc = uu____844})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, uu____846))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = uu____848; FStar_Extraction_ML_Syntax.loc = uu____849})::[]) when (let _0_238 = (FStar_Extraction_ML_Syntax.string_of_mlpath p)
in (_0_238 = "FStar.All.try_with")) -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = uu____879; FStar_Extraction_ML_Syntax.loc = uu____880}, branches); FStar_Extraction_ML_Syntax.mlty = uu____882; FStar_Extraction_ML_Syntax.loc = uu____883} when (let _0_240 = (FStar_Extraction_ML_Syntax.idsym arg)
in (let _0_239 = (FStar_Extraction_ML_Syntax.idsym arg')
in (_0_240 = _0_239))) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____914; FStar_Extraction_ML_Syntax.loc = uu____915}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = uu____925; FStar_Extraction_ML_Syntax.loc = uu____926}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| uu____931 -> begin
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

let uu____948 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____948) with
| true -> begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end
| uu____950 -> begin
(FStar_Format.reduce (let _0_243 = (let _0_242 = (let _0_241 = (FStar_Format.text (ptsym currentModule f))
in (_0_241)::[])
in ((FStar_Format.text "."))::_0_242)
in (e)::_0_243))
end))
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> (

let uu____968 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____968) with
| true -> begin
(FStar_Format.reduce1 (let _0_248 = (let _0_247 = (let _0_246 = (match (xt) with
| Some (xxt) -> begin
(FStar_Format.reduce1 (let _0_245 = (let _0_244 = (doc_of_mltype currentModule outer xxt)
in (_0_244)::[])
in ((FStar_Format.text " : "))::_0_245))
end
| uu____970 -> begin
(FStar_Format.text "")
end)
in (_0_246)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::_0_247)
in ((FStar_Format.text "("))::_0_248))
end
| uu____972 -> begin
(FStar_Format.text x)
end)))
in (

let ids = (FStar_List.map (fun uu____979 -> (match (uu____979) with
| ((x, uu____985), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (FStar_Format.reduce1 (let _0_250 = (let _0_249 = (FStar_Format.reduce1 ids)
in (_0_249)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::_0_250))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _0_254 = (let _0_253 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _0_252 = (let _0_251 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (_0_251)::((FStar_Format.text "end"))::[])
in (_0_253)::_0_252))
in (FStar_Format.combine FStar_Format.hardline _0_254))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _0_262 = (let _0_261 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _0_260 = (let _0_259 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _0_258 = (let _0_257 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (let _0_256 = (let _0_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (_0_255)::((FStar_Format.text "end"))::[])
in (_0_257)::_0_256))
in (_0_259)::_0_258))
in (_0_261)::_0_260))
in (FStar_Format.combine FStar_Format.hardline _0_262))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _0_263 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (_0_263)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(FStar_Format.reduce1 (let _0_265 = (let _0_264 = (FStar_Format.text (ptctor currentModule exn))
in (_0_264)::[])
in ((FStar_Format.text "raise"))::_0_265))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (FStar_Format.reduce1 (let _0_269 = (let _0_268 = (FStar_Format.text (ptctor currentModule exn))
in (let _0_267 = (let _0_266 = (FStar_Format.parens (FStar_Format.combine (FStar_Format.text ", ") args))
in (_0_266)::[])
in (_0_268)::_0_267))
in ((FStar_Format.text "raise"))::_0_269)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _0_276 = (let _0_275 = (let _0_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _0_273 = (let _0_272 = (let _0_271 = (let _0_270 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _0_270))
in (_0_271)::[])
in ((FStar_Format.text "with"))::_0_272)
in (_0_274)::_0_273))
in ((FStar_Format.text "try"))::_0_275)
in (FStar_Format.combine FStar_Format.hardline _0_276))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let uu____1062 = (FStar_Option.get (as_bin_op p))
in (match (uu____1062) with
| (uu____1073, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let uu____1090 = (FStar_Option.get (as_uni_op p))
in (match (uu____1090) with
| (uu____1095, txt) -> begin
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

let for1 = (fun uu____1120 -> (match (uu____1120) with
| (name, p) -> begin
(FStar_Format.reduce1 (let _0_280 = (FStar_Format.text (ptsym currentModule ((path), (name))))
in (let _0_279 = (let _0_278 = (let _0_277 = (doc_of_pattern currentModule p)
in (_0_277)::[])
in ((FStar_Format.text "="))::_0_278)
in (_0_280)::_0_279)))
end))
in (FStar_Format.cbrackets (let _0_281 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_281))))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = (

let uu____1131 = (is_standard_constructor ctor)
in (match (uu____1131) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____1134 -> begin
(ptctor currentModule ctor)
end))
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = (

let uu____1140 = (is_standard_constructor ctor)
in (match (uu____1140) with
| true -> begin
(Prims.snd (FStar_Option.get (as_standard_constructor ctor)))
end
| uu____1143 -> begin
(ptctor currentModule ctor)
end))
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (let _0_285 = (FStar_Format.parens (doc_of_pattern currentModule x))
in (let _0_284 = (let _0_283 = (let _0_282 = (doc_of_pattern currentModule xs)
in (_0_282)::[])
in ((FStar_Format.text "::"))::_0_283)
in (_0_285)::_0_284)))
end
| (uu____1149, (FStar_Extraction_ML_Syntax.MLP_Tuple (uu____1150))::[]) -> begin
(FStar_Format.reduce1 (let _0_288 = (let _0_287 = (let _0_286 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _0_286))
in (_0_287)::[])
in ((FStar_Format.text name))::_0_288))
end
| uu____1153 -> begin
(FStar_Format.reduce1 (let _0_291 = (let _0_290 = (FStar_Format.parens (let _0_289 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") _0_289)))
in (_0_290)::[])
in ((FStar_Format.text name))::_0_291))
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
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule uu____1170 -> (match (uu____1170) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(FStar_Format.reduce1 (let _0_293 = (let _0_292 = (doc_of_pattern currentModule p)
in (_0_292)::[])
in ((FStar_Format.text "|"))::_0_293))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (FStar_Format.reduce1 (let _0_295 = (let _0_294 = (doc_of_pattern currentModule p)
in (_0_294)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::_0_295)))
end)
in (let _0_299 = (let _0_298 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (let _0_297 = (let _0_296 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_0_296)::((FStar_Format.text "end"))::[])
in (_0_298)::_0_297))
in (FStar_Format.combine FStar_Format.hardline _0_299)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule uu____1184 -> (match (uu____1184) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun uu____1197 -> (match (uu____1197) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = uu____1200; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun uu____1217 -> (match (uu____1217) with
| (x, uu____1221) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = (match ((not (pt))) with
| true -> begin
(FStar_Format.text "")
end
| uu____1223 -> begin
(

let uu____1224 = ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level))
in (match (uu____1224) with
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
| uu____1240 -> begin
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
| uu____1256 -> begin
(FStar_Format.text "")
end)
end))
end)
in (FStar_Format.reduce1 (let _0_302 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _0_301 = (let _0_300 = (FStar_Format.reduce1 ids)
in (_0_300)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in (_0_302)::_0_301)))))))
end))
in (

let letdoc = (match ((rec_ = FStar_Extraction_ML_Syntax.Rec)) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end
| uu____1258 -> begin
(FStar_Format.text "let")
end)
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 (((match ((i = (Prims.parse_int "0"))) with
| true -> begin
letdoc
end
| uu____1265 -> begin
(FStar_Format.text "and")
end))::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun uu____1266 -> (match (uu____1266) with
| (lineno, file) -> begin
(

let uu____1269 = ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ()))
in (match (uu____1269) with
| true -> begin
FStar_Format.empty
end
| uu____1270 -> begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end))
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun uu____1289 -> (match (uu____1289) with
| (uu____1298, x, mangle_opt, tparams, body) -> begin
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
| uu____1313 -> begin
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

let forfield = (fun uu____1334 -> (match (uu____1334) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (FStar_Format.cbrackets (let _0_303 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") _0_303))))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun uu____1356 -> (match (uu____1356) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| uu____1364 -> begin
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

let doc = (FStar_Format.reduce1 (let _0_305 = (let _0_304 = (FStar_Format.text (ptsym currentModule (([]), (x))))
in (_0_304)::[])
in (tparams)::_0_305))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _0_307 = (let _0_306 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (_0_306)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _0_307)))
end)))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = (match (((FStar_List.length doc) > (Prims.parse_int "0"))) with
| true -> begin
(FStar_Format.reduce1 (let _0_309 = (let _0_308 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (_0_308)::[])
in ((FStar_Format.text "type"))::_0_309))
end
| uu____1397 -> begin
(FStar_Format.text "")
end)
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _0_315 = (let _0_314 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (let _0_313 = (let _0_312 = (doc_of_sig currentModule subsig)
in (let _0_311 = (let _0_310 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (_0_310)::[])
in (_0_312)::_0_311))
in (_0_314)::_0_313))
in (FStar_Format.combine FStar_Format.hardline _0_315))
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
| FStar_Extraction_ML_Syntax.MLS_Val (x, (uu____1424, ty)) -> begin
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
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, uu____1458, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(FStar_Format.reduce1 (let _0_319 = (let _0_318 = (let _0_317 = (let _0_316 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_0_316)::[])
in ((FStar_Format.text "="))::_0_317)
in ((FStar_Format.text "_"))::_0_318)
in ((FStar_Format.text "let"))::_0_319))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (uu____1479) -> begin
FStar_Format.empty
end
| uu____1480 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun uu____1486 -> (match (uu____1486) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun uu____1524 -> (match (uu____1524) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun uu____1563 -> (match (uu____1563) with
| (s, uu____1567) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (FStar_Format.reduce (let _0_322 = (let _0_321 = (let _0_320 = (FStar_Format.reduce sub)
in (_0_320)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_0_321)
in ((FStar_Format.cat head FStar_Format.hardline))::_0_322))))))))
end))
and for1_mod = (fun istop uu____1584 -> (match (uu____1584) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (

let uu____1618 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1618) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end
| uu____1620 -> begin
(match ((not (istop))) with
| true -> begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end
| uu____1622 -> begin
[]
end)
end)))
in (

let tail = (match ((not (istop))) with
| true -> begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end
| uu____1624 -> begin
(FStar_Format.reduce1 [])
end)
in (

let doc = (FStar_Option.map (fun uu____1629 -> (match (uu____1629) with
| (uu____1632, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = (

let uu____1650 = (FStar_Extraction_ML_Util.codegen_fsharp ())
in (match (uu____1650) with
| true -> begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end
| uu____1652 -> begin
[]
end))
in (let _0_330 = (let _0_329 = (let _0_328 = (let _0_327 = (let _0_326 = (let _0_325 = (let _0_324 = (let _0_323 = (FStar_Format.reduce sub)
in (_0_323)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_0_324)
in (FStar_Format.hardline)::_0_325)
in ((FStar_Format.text "open Prims"))::_0_326)
in (FStar_Format.hardline)::_0_327)
in (head)::_0_328)
in (FStar_List.append prefix _0_329))
in (FStar_All.pipe_left FStar_Format.reduce _0_330)))))))))
end))
in (

let docs = (FStar_List.map (fun uu____1670 -> (match (uu____1670) with
| (x, s, m) -> begin
(let _0_332 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _0_331 = (for1_mod true ((x), (s), (m)))
in ((_0_332), (_0_331))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _0_333 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _0_333 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _0_334 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _0_334 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





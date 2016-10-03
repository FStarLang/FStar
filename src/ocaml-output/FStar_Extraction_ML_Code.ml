
open Prims

type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc


let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))


let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))


let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))


let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))


let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))


type fixity =
| Prefix
| Postfix
| Infix of assoc


let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))


let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))


let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))


let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_75_4) -> begin
_75_4
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
| ([], _75_9) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (_75_19, _75_21) -> begin
false
end))


let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (

let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(

let cg_libs = (FStar_Options.codegen_libs ())
in (

let ns_len = (FStar_List.length ns)
in (

let found = (FStar_Util.find_map cg_libs (fun cg_path -> (

let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(

let _75_32 = (FStar_Util.first_N cg_len ns)
in (match (_75_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _172_31 = (let _172_30 = (let _172_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_172_29)::[])
in (FStar_List.append pfx _172_30))
in Some (_172_31))
end else begin
None
end
end))
end else begin
None
end)))
in (match (found) with
| None -> begin
(ns')::[]
end
| Some (x) -> begin
x
end))))
end))


let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| _75_42 -> begin
(

let _75_45 = x
in (match (_75_45) with
| (ns, x) -> begin
(let _172_36 = (path_of_ns currentModule ns)
in ((_172_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _172_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _172_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _75_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_75_51) with
| (p, s) -> begin
(let _172_46 = (let _172_45 = (let _172_44 = (ptsym_of_symbol s)
in (_172_44)::[])
in (FStar_List.append p _172_45))
in (FStar_String.concat "." _172_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _75_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_75_56) with
| (p, s) -> begin
(

let s = if ((let _172_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _172_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_Colon_Equals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("~-")))::((("op_Bang"), ("Support.ST.read")))::[]


let prim_types = []


let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]


let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _75_61 -> (match (_75_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_67 -> (match (_75_67) with
| (y, _75_64, _75_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _75_71 -> (match (_75_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_75 -> (match (_75_75) with
| (y, _75_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _75_79 -> (match (_75_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_83 -> (match (_75_83) with
| (y, _75_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _75_87 -> (match (_75_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _75_91 -> (match (_75_91) with
| (y, _75_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _75_95 inner doc -> (match (_75_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _75_104 = _inner
in (match (_75_104) with
| (pi, fi) -> begin
(

let _75_107 = _outer
in (match (_75_107) with
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
| (_75_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_75_135, _75_137) -> begin
false
end))
end))
end)))
in if (noparens inner outer side) then begin
doc
end else begin
(FStar_Format.parens doc)
end)
end))


let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))


let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _75_1 -> (match (_75_1) with
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
(let _172_101 = (let _172_100 = (escape_or escape_char_hex c)
in (Prims.strcat _172_100 "\'"))
in (Prims.strcat "\'" _172_101))
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
(let _172_103 = (let _172_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _172_102 "\""))
in (Prims.strcat "\"" _172_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _172_105 = (let _172_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _172_104 "\""))
in (Prims.strcat "\"" _172_105))
end
| _75_203 -> begin
(FStar_All.failwith "TODO: extract integer constants properly into OCaml")
end))


let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(

let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _172_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _172_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _172_119 = (let _172_118 = (FStar_Format.combine (FStar_Format.text " * ") doc)
in (FStar_Format.hbox _172_118))
in (FStar_Format.parens _172_119))
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
| _75_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _172_121 = (let _172_120 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.hbox _172_120))
in (FStar_Format.parens _172_121)))
end)
in (

let name = if (is_standard_type name) then begin
(let _172_123 = (let _172_122 = (as_standard_type name)
in (FStar_Option.get _172_122))
in (Prims.snd _172_123))
end else begin
(ptsym currentModule name)
end
in (let _172_124 = (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[]))
in (FStar_Format.hbox _172_124))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _75_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _172_126 = (let _172_125 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox _172_125))
in (maybe_paren outer t_prio_fun _172_126))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _172_130 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _172_130)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _172_151 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FStar_Format.parens _172_151))
end else begin
(let _172_152 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[]))
in (FStar_Format.parens _172_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _172_154 = (string_of_mlconstant c)
in (FStar_Format.text _172_154))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _75_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _172_155 = (ptsym currentModule path)
in (FStar_Format.text _172_155))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _75_269 -> (match (_75_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _172_160 = (let _172_159 = (let _172_158 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _172_158))
in (_172_159)::((FStar_Format.text "="))::(doc)::[])
in (FStar_Format.reduce1 _172_160)))
end))
in (let _172_162 = (let _172_161 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _172_161))
in (FStar_Format.cbrackets _172_162)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _172_164 = (let _172_163 = (as_standard_constructor ctor)
in (FStar_Option.get _172_163))
in (Prims.snd _172_164))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _172_166 = (let _172_165 = (as_standard_constructor ctor)
in (FStar_Option.get _172_165))
in (Prims.snd _172_166))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (_75_288, _75_290) -> begin
(let _172_170 = (let _172_169 = (let _172_168 = (let _172_167 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _172_167))
in (_172_168)::[])
in ((FStar_Format.text name))::_172_169)
in (FStar_Format.reduce1 _172_170))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _172_172 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _172_172))) es)
in (

let docs = (let _172_173 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens _172_173))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _172_176 = (let _172_175 = (let _172_174 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_172_174)::[])
in (FStar_Format.hardline)::_172_175)
in (FStar_Format.reduce _172_176))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _172_181 = (let _172_180 = (let _172_179 = (let _172_178 = (let _172_177 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (_172_177)::[])
in (doc)::_172_178)
in (pre)::_172_179)
in (FStar_Format.combine FStar_Format.hardline _172_180))
in (FStar_Format.parens _172_181)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_75_331)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _75_329; FStar_Extraction_ML_Syntax.loc = _75_327})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _75_319))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _75_316; FStar_Extraction_ML_Syntax.loc = _75_314})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _75_346; FStar_Extraction_ML_Syntax.loc = _75_344}, branches); FStar_Extraction_ML_Syntax.mlty = _75_342; FStar_Extraction_ML_Syntax.loc = _75_340} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_365; FStar_Extraction_ML_Syntax.loc = _75_363}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_385; FStar_Extraction_ML_Syntax.loc = _75_383}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _75_397 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _172_182 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _172_182))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end else begin
(let _172_187 = (let _172_186 = (let _172_185 = (let _172_184 = (let _172_183 = (ptsym currentModule f)
in (FStar_Format.text _172_183))
in (_172_184)::[])
in ((FStar_Format.text "."))::_172_185)
in (e)::_172_186)
in (FStar_Format.reduce _172_187))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _172_198 = (let _172_197 = (let _172_196 = (let _172_195 = (match (xt) with
| Some (xxt) -> begin
(let _172_194 = (let _172_193 = (let _172_192 = (doc_of_mltype currentModule outer xxt)
in (_172_192)::[])
in ((FStar_Format.text " : "))::_172_193)
in (FStar_Format.reduce1 _172_194))
end
| _75_416 -> begin
(FStar_Format.text "")
end)
in (_172_195)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::_172_196)
in ((FStar_Format.text "("))::_172_197)
in (FStar_Format.reduce1 _172_198))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _75_422 -> (match (_75_422) with
| ((x, _75_419), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _172_202 = (let _172_201 = (let _172_200 = (FStar_Format.reduce1 ids)
in (_172_200)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::_172_201)
in (FStar_Format.reduce1 _172_202))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _172_206 = (let _172_205 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _172_204 = (let _172_203 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (_172_203)::((FStar_Format.text "end"))::[])
in (_172_205)::_172_204))
in (FStar_Format.combine FStar_Format.hardline _172_206))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _172_214 = (let _172_213 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _172_212 = (let _172_211 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _172_210 = (let _172_209 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (let _172_208 = (let _172_207 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (_172_207)::((FStar_Format.text "end"))::[])
in (_172_209)::_172_208))
in (_172_211)::_172_210))
in (_172_213)::_172_212))
in (FStar_Format.combine FStar_Format.hardline _172_214))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _172_215 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (_172_215)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _172_219 = (let _172_218 = (let _172_217 = (let _172_216 = (ptctor currentModule exn)
in (FStar_Format.text _172_216))
in (_172_217)::[])
in ((FStar_Format.text "raise"))::_172_218)
in (FStar_Format.reduce1 _172_219))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _172_226 = (let _172_225 = (let _172_224 = (let _172_220 = (ptctor currentModule exn)
in (FStar_Format.text _172_220))
in (let _172_223 = (let _172_222 = (let _172_221 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _172_221))
in (_172_222)::[])
in (_172_224)::_172_223))
in ((FStar_Format.text "raise"))::_172_225)
in (FStar_Format.reduce1 _172_226)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _172_233 = (let _172_232 = (let _172_231 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _172_230 = (let _172_229 = (let _172_228 = (let _172_227 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _172_227))
in (_172_228)::[])
in ((FStar_Format.text "with"))::_172_229)
in (_172_231)::_172_230))
in ((FStar_Format.text "try"))::_172_232)
in (FStar_Format.combine FStar_Format.hardline _172_233))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _75_470 = (let _172_238 = (as_bin_op p)
in (FStar_Option.get _172_238))
in (match (_75_470) with
| (_75_467, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _75_480 = (let _172_242 = (as_uni_op p)
in (FStar_Option.get _172_242))
in (match (_75_480) with
| (_75_478, txt) -> begin
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
(let _172_245 = (string_of_mlconstant c)
in (FStar_Format.text _172_245))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _75_497 -> (match (_75_497) with
| (name, p) -> begin
(let _172_253 = (let _172_252 = (let _172_248 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _172_248))
in (let _172_251 = (let _172_250 = (let _172_249 = (doc_of_pattern currentModule p)
in (_172_249)::[])
in ((FStar_Format.text "="))::_172_250)
in (_172_252)::_172_251))
in (FStar_Format.reduce1 _172_253))
end))
in (let _172_255 = (let _172_254 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _172_254))
in (FStar_Format.cbrackets _172_255)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _172_257 = (let _172_256 = (as_standard_constructor ctor)
in (FStar_Option.get _172_256))
in (Prims.snd _172_257))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _172_259 = (let _172_258 = (as_standard_constructor ctor)
in (FStar_Option.get _172_258))
in (Prims.snd _172_259))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _172_265 = (let _172_264 = (let _172_260 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _172_260))
in (let _172_263 = (let _172_262 = (let _172_261 = (doc_of_pattern currentModule xs)
in (_172_261)::[])
in ((FStar_Format.text "::"))::_172_262)
in (_172_264)::_172_263))
in (FStar_Format.reduce _172_265))
end
| (_75_514, (FStar_Extraction_ML_Syntax.MLP_Tuple (_75_516))::[]) -> begin
(let _172_269 = (let _172_268 = (let _172_267 = (let _172_266 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _172_266))
in (_172_267)::[])
in ((FStar_Format.text name))::_172_268)
in (FStar_Format.reduce1 _172_269))
end
| _75_521 -> begin
(let _172_274 = (let _172_273 = (let _172_272 = (let _172_271 = (let _172_270 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") _172_270))
in (FStar_Format.parens _172_271))
in (_172_272)::[])
in ((FStar_Format.text name))::_172_273)
in (FStar_Format.reduce1 _172_274))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _172_275 = (FStar_Format.combine (FStar_Format.text ", ") ps)
in (FStar_Format.parens _172_275)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _75_534 -> (match (_75_534) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _172_280 = (let _172_279 = (let _172_278 = (doc_of_pattern currentModule p)
in (_172_278)::[])
in ((FStar_Format.text "|"))::_172_279)
in (FStar_Format.reduce1 _172_280))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _172_283 = (let _172_282 = (let _172_281 = (doc_of_pattern currentModule p)
in (_172_281)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::_172_282)
in (FStar_Format.reduce1 _172_283)))
end)
in (let _172_287 = (let _172_286 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (let _172_285 = (let _172_284 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_172_284)::((FStar_Format.text "end"))::[])
in (_172_286)::_172_285))
in (FStar_Format.combine FStar_Format.hardline _172_287)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _75_544 -> (match (_75_544) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _75_552 -> (match (_75_552) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _75_549; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _75_558 -> (match (_75_558) with
| (x, _75_557) -> begin
(FStar_Format.text x)
end)) ids)
in (

let ty_annot = if (not (pt)) then begin
(FStar_Format.text "")
end else begin
if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && ((rec_ = FStar_Extraction_ML_Syntax.Rec) || top_level)) then begin
(match (tys) with
| (Some ((_)::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some ((_)::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _172_295 = (let _172_294 = (let _172_293 = (FStar_Format.reduce1 ids)
in (_172_293)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in ((FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_172_294)
in (FStar_Format.reduce1 _172_295))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 ((if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end)::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _75_598 -> (match (_75_598) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _75_608 -> (match (_75_608) with
| (_75_604, x, tparams, body) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _75_613 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _172_306 = (FStar_Format.combine (FStar_Format.text ", ") doc)
in (FStar_Format.parens _172_306)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _75_626 -> (match (_75_626) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (let _172_312 = (let _172_311 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") _172_311))
in (FStar_Format.cbrackets _172_312)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _75_634 -> (match (_75_634) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _75_637 -> begin
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

let doc = (let _172_319 = (let _172_318 = (let _172_317 = (let _172_316 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _172_316))
in (_172_317)::[])
in (tparams)::_172_318)
in (FStar_Format.reduce1 _172_319))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _172_321 = (let _172_320 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (_172_320)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _172_321)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _172_324 = (let _172_323 = (let _172_322 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (_172_322)::[])
in ((FStar_Format.text "type"))::_172_323)
in (FStar_Format.reduce1 _172_324))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _172_336 = (let _172_335 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (let _172_334 = (let _172_333 = (doc_of_sig currentModule subsig)
in (let _172_332 = (let _172_331 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (_172_331)::[])
in (_172_333)::_172_332))
in (_172_335)::_172_334))
in (FStar_Format.combine FStar_Format.hardline _172_336))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _172_337 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _172_337))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_75_668, ty)) -> begin
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

let args = (let _172_345 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _172_345))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _172_350 = (let _172_349 = (let _172_348 = (let _172_347 = (let _172_346 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_172_346)::[])
in ((FStar_Format.text "="))::_172_347)
in ((FStar_Format.text "_"))::_172_348)
in ((FStar_Format.text "let"))::_172_349)
in (FStar_Format.reduce1 _172_350))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_75_708) -> begin
FStar_Format.empty
end
| _75_711 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _75_714 -> (match (_75_714) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _75_721 -> (match (_75_721) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (

let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (

let doc = (FStar_Option.map (fun _75_728 -> (match (_75_728) with
| (s, _75_727) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _172_367 = (let _172_366 = (let _172_365 = (let _172_364 = (FStar_Format.reduce sub)
in (_172_364)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_172_365)
in ((FStar_Format.cat head FStar_Format.hardline))::_172_366)
in (FStar_Format.reduce _172_367))))))))
end))
and for1_mod = (fun istop _75_741 -> (match (_75_741) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _172_370 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end else begin
if (not (istop)) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end else begin
[]
end
end
in (FStar_Format.reduce1 _172_370))
in (

let tail = if (not (istop)) then begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _75_748 -> (match (_75_748) with
| (_75_746, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end else begin
[]
end
in (let _172_380 = (let _172_379 = (let _172_378 = (let _172_377 = (let _172_376 = (let _172_375 = (let _172_374 = (let _172_373 = (FStar_Format.reduce sub)
in (_172_373)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_172_374)
in (FStar_Format.hardline)::_172_375)
in ((FStar_Format.text "open Prims"))::_172_376)
in (FStar_Format.hardline)::_172_377)
in (head)::_172_378)
in (FStar_List.append prefix _172_379))
in (FStar_All.pipe_left FStar_Format.reduce _172_380)))))))))
end))
in (

let docs = (FStar_List.map (fun _75_760 -> (match (_75_760) with
| (x, s, m) -> begin
(let _172_383 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _172_382 = (for1_mod true ((x), (s), (m)))
in ((_172_383), (_172_382))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _172_390 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _172_390 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _172_395 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _172_395 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





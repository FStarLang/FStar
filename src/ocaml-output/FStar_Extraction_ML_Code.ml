
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
(let _170_31 = (let _170_30 = (let _170_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_170_29)::[])
in (FStar_List.append pfx _170_30))
in Some (_170_31))
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
(let _170_36 = (path_of_ns currentModule ns)
in ((_170_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _170_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _170_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
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
(let _170_46 = (let _170_45 = (let _170_44 = (ptsym_of_symbol s)
in (_170_44)::[])
in (FStar_List.append p _170_45))
in (FStar_String.concat "." _170_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _75_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_75_56) with
| (p, s) -> begin
(

let s = if ((let _170_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _170_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
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
(let _170_101 = (let _170_100 = (escape_or escape_char_hex c)
in (Prims.strcat _170_100 "\'"))
in (Prims.strcat "\'" _170_101))
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
(let _170_103 = (let _170_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _170_102 "\""))
in (Prims.strcat "\"" _170_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _170_105 = (let _170_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _170_104 "\""))
in (Prims.strcat "\"" _170_105))
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
in (let _170_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _170_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _170_120 = (let _170_119 = (let _170_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _170_118 doc))
in (FStar_Format.hbox _170_119))
in (FStar_Format.parens _170_120))
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
in (let _170_123 = (let _170_122 = (let _170_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_121 args))
in (FStar_Format.hbox _170_122))
in (FStar_Format.parens _170_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _170_125 = (let _170_124 = (as_standard_type name)
in (FStar_Option.get _170_124))
in (Prims.snd _170_125))
end else begin
(ptsym currentModule name)
end
in (let _170_129 = (let _170_128 = (let _170_127 = (let _170_126 = (FStar_Format.text name)
in (_170_126)::[])
in (args)::_170_127)
in (FStar_Format.reduce1 _170_128))
in (FStar_Format.hbox _170_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _75_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _170_134 = (let _170_133 = (let _170_132 = (let _170_131 = (let _170_130 = (FStar_Format.text " -> ")
in (_170_130)::(d2)::[])
in (d1)::_170_131)
in (FStar_Format.reduce1 _170_132))
in (FStar_Format.hbox _170_133))
in (maybe_paren outer t_prio_fun _170_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _170_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _170_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _170_161 = (let _170_160 = (let _170_159 = (FStar_Format.text "Prims.checked_cast")
in (_170_159)::(doc)::[])
in (FStar_Format.reduce _170_160))
in (FStar_Format.parens _170_161))
end else begin
(let _170_166 = (let _170_165 = (let _170_164 = (FStar_Format.text "Obj.magic ")
in (let _170_163 = (let _170_162 = (FStar_Format.parens doc)
in (_170_162)::[])
in (_170_164)::_170_163))
in (FStar_Format.reduce _170_165))
in (FStar_Format.parens _170_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _170_170 = (let _170_169 = (let _170_168 = (FStar_Format.text ";")
in (_170_168)::(FStar_Format.hardline)::[])
in (d)::_170_169)
in (FStar_Format.reduce _170_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _170_171 = (string_of_mlconstant c)
in (FStar_Format.text _170_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _75_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _170_172 = (ptsym currentModule path)
in (FStar_Format.text _170_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _75_269 -> (match (_75_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _170_179 = (let _170_178 = (let _170_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _170_175))
in (let _170_177 = (let _170_176 = (FStar_Format.text "=")
in (_170_176)::(doc)::[])
in (_170_178)::_170_177))
in (FStar_Format.reduce1 _170_179)))
end))
in (let _170_182 = (let _170_181 = (FStar_Format.text "; ")
in (let _170_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _170_181 _170_180)))
in (FStar_Format.cbrackets _170_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _170_184 = (let _170_183 = (as_standard_constructor ctor)
in (FStar_Option.get _170_183))
in (Prims.snd _170_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _170_186 = (let _170_185 = (as_standard_constructor ctor)
in (FStar_Option.get _170_185))
in (Prims.snd _170_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _170_190 = (let _170_189 = (FStar_Format.parens x)
in (let _170_188 = (let _170_187 = (FStar_Format.text "::")
in (_170_187)::(xs)::[])
in (_170_189)::_170_188))
in (FStar_Format.reduce _170_190))
end
| (_75_288, _75_290) -> begin
(let _170_196 = (let _170_195 = (FStar_Format.text name)
in (let _170_194 = (let _170_193 = (let _170_192 = (let _170_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_191 args))
in (FStar_Format.parens _170_192))
in (_170_193)::[])
in (_170_195)::_170_194))
in (FStar_Format.reduce1 _170_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _170_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _170_198))) es)
in (

let docs = (let _170_200 = (let _170_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_199 docs))
in (FStar_Format.parens _170_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, _75_300, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _170_203 = (let _170_202 = (let _170_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_170_201)::[])
in (FStar_Format.hardline)::_170_202)
in (FStar_Format.reduce _170_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _170_210 = (let _170_209 = (let _170_208 = (let _170_207 = (let _170_206 = (let _170_205 = (let _170_204 = (FStar_Format.text "in")
in (_170_204)::(body)::[])
in (FStar_Format.reduce1 _170_205))
in (_170_206)::[])
in (doc)::_170_207)
in (pre)::_170_208)
in (FStar_Format.combine FStar_Format.hardline _170_209))
in (FStar_Format.parens _170_210)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_75_333)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _75_331; FStar_Extraction_ML_Syntax.loc = _75_329})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _75_321))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _75_318; FStar_Extraction_ML_Syntax.loc = _75_316})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _75_348; FStar_Extraction_ML_Syntax.loc = _75_346}, branches); FStar_Extraction_ML_Syntax.mlty = _75_344; FStar_Extraction_ML_Syntax.loc = _75_342} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_367; FStar_Extraction_ML_Syntax.loc = _75_365}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _75_387; FStar_Extraction_ML_Syntax.loc = _75_385}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _75_399 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _170_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _170_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _170_216 = (let _170_215 = (let _170_214 = (FStar_Format.text ".")
in (let _170_213 = (let _170_212 = (FStar_Format.text (Prims.snd f))
in (_170_212)::[])
in (_170_214)::_170_213))
in (e)::_170_215)
in (FStar_Format.reduce _170_216))
end else begin
(let _170_222 = (let _170_221 = (let _170_220 = (FStar_Format.text ".")
in (let _170_219 = (let _170_218 = (let _170_217 = (ptsym currentModule f)
in (FStar_Format.text _170_217))
in (_170_218)::[])
in (_170_220)::_170_219))
in (e)::_170_221)
in (FStar_Format.reduce _170_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _170_238 = (let _170_237 = (FStar_Format.text "(")
in (let _170_236 = (let _170_235 = (FStar_Format.text x)
in (let _170_234 = (let _170_233 = (match (xt) with
| Some (xxt) -> begin
(let _170_230 = (let _170_229 = (FStar_Format.text " : ")
in (let _170_228 = (let _170_227 = (doc_of_mltype currentModule outer xxt)
in (_170_227)::[])
in (_170_229)::_170_228))
in (FStar_Format.reduce1 _170_230))
end
| _75_418 -> begin
(FStar_Format.text "")
end)
in (let _170_232 = (let _170_231 = (FStar_Format.text ")")
in (_170_231)::[])
in (_170_233)::_170_232))
in (_170_235)::_170_234))
in (_170_237)::_170_236))
in (FStar_Format.reduce1 _170_238))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _75_424 -> (match (_75_424) with
| ((x, _75_421), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _170_245 = (let _170_244 = (FStar_Format.text "fun")
in (let _170_243 = (let _170_242 = (FStar_Format.reduce1 ids)
in (let _170_241 = (let _170_240 = (FStar_Format.text "->")
in (_170_240)::(body)::[])
in (_170_242)::_170_241))
in (_170_244)::_170_243))
in (FStar_Format.reduce1 _170_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _170_258 = (let _170_257 = (let _170_252 = (let _170_251 = (FStar_Format.text "if")
in (let _170_250 = (let _170_249 = (let _170_248 = (FStar_Format.text "then")
in (let _170_247 = (let _170_246 = (FStar_Format.text "begin")
in (_170_246)::[])
in (_170_248)::_170_247))
in (cond)::_170_249)
in (_170_251)::_170_250))
in (FStar_Format.reduce1 _170_252))
in (let _170_256 = (let _170_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _170_254 = (let _170_253 = (FStar_Format.text "end")
in (_170_253)::[])
in (_170_255)::_170_254))
in (_170_257)::_170_256))
in (FStar_Format.combine FStar_Format.hardline _170_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _170_281 = (let _170_280 = (let _170_265 = (let _170_264 = (FStar_Format.text "if")
in (let _170_263 = (let _170_262 = (let _170_261 = (FStar_Format.text "then")
in (let _170_260 = (let _170_259 = (FStar_Format.text "begin")
in (_170_259)::[])
in (_170_261)::_170_260))
in (cond)::_170_262)
in (_170_264)::_170_263))
in (FStar_Format.reduce1 _170_265))
in (let _170_279 = (let _170_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _170_277 = (let _170_276 = (let _170_271 = (let _170_270 = (FStar_Format.text "end")
in (let _170_269 = (let _170_268 = (FStar_Format.text "else")
in (let _170_267 = (let _170_266 = (FStar_Format.text "begin")
in (_170_266)::[])
in (_170_268)::_170_267))
in (_170_270)::_170_269))
in (FStar_Format.reduce1 _170_271))
in (let _170_275 = (let _170_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _170_273 = (let _170_272 = (FStar_Format.text "end")
in (_170_272)::[])
in (_170_274)::_170_273))
in (_170_276)::_170_275))
in (_170_278)::_170_277))
in (_170_280)::_170_279))
in (FStar_Format.combine FStar_Format.hardline _170_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _170_288 = (let _170_287 = (let _170_286 = (FStar_Format.text "match")
in (let _170_285 = (let _170_284 = (FStar_Format.parens cond)
in (let _170_283 = (let _170_282 = (FStar_Format.text "with")
in (_170_282)::[])
in (_170_284)::_170_283))
in (_170_286)::_170_285))
in (FStar_Format.reduce1 _170_287))
in (_170_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _170_293 = (let _170_292 = (FStar_Format.text "raise")
in (let _170_291 = (let _170_290 = (let _170_289 = (ptctor currentModule exn)
in (FStar_Format.text _170_289))
in (_170_290)::[])
in (_170_292)::_170_291))
in (FStar_Format.reduce1 _170_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _170_302 = (let _170_301 = (FStar_Format.text "raise")
in (let _170_300 = (let _170_299 = (let _170_294 = (ptctor currentModule exn)
in (FStar_Format.text _170_294))
in (let _170_298 = (let _170_297 = (let _170_296 = (let _170_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_295 args))
in (FStar_Format.parens _170_296))
in (_170_297)::[])
in (_170_299)::_170_298))
in (_170_301)::_170_300))
in (FStar_Format.reduce1 _170_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _170_311 = (let _170_310 = (FStar_Format.text "try")
in (let _170_309 = (let _170_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _170_307 = (let _170_306 = (FStar_Format.text "with")
in (let _170_305 = (let _170_304 = (let _170_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _170_303))
in (_170_304)::[])
in (_170_306)::_170_305))
in (_170_308)::_170_307))
in (_170_310)::_170_309))
in (FStar_Format.combine FStar_Format.hardline _170_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _75_472 = (let _170_316 = (as_bin_op p)
in (FStar_Option.get _170_316))
in (match (_75_472) with
| (_75_469, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _170_319 = (let _170_318 = (let _170_317 = (FStar_Format.text txt)
in (_170_317)::(e2)::[])
in (e1)::_170_318)
in (FStar_Format.reduce1 _170_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _75_482 = (let _170_323 = (as_uni_op p)
in (FStar_Option.get _170_323))
in (match (_75_482) with
| (_75_480, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _170_327 = (let _170_326 = (FStar_Format.text txt)
in (let _170_325 = (let _170_324 = (FStar_Format.parens e1)
in (_170_324)::[])
in (_170_326)::_170_325))
in (FStar_Format.reduce1 _170_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _170_330 = (string_of_mlconstant c)
in (FStar_Format.text _170_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _75_499 -> (match (_75_499) with
| (name, p) -> begin
(let _170_339 = (let _170_338 = (let _170_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _170_333))
in (let _170_337 = (let _170_336 = (FStar_Format.text "=")
in (let _170_335 = (let _170_334 = (doc_of_pattern currentModule p)
in (_170_334)::[])
in (_170_336)::_170_335))
in (_170_338)::_170_337))
in (FStar_Format.reduce1 _170_339))
end))
in (let _170_342 = (let _170_341 = (FStar_Format.text "; ")
in (let _170_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _170_341 _170_340)))
in (FStar_Format.cbrackets _170_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _170_344 = (let _170_343 = (as_standard_constructor ctor)
in (FStar_Option.get _170_343))
in (Prims.snd _170_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _170_346 = (let _170_345 = (as_standard_constructor ctor)
in (FStar_Option.get _170_345))
in (Prims.snd _170_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _170_353 = (let _170_352 = (let _170_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _170_347))
in (let _170_351 = (let _170_350 = (FStar_Format.text "::")
in (let _170_349 = (let _170_348 = (doc_of_pattern currentModule xs)
in (_170_348)::[])
in (_170_350)::_170_349))
in (_170_352)::_170_351))
in (FStar_Format.reduce _170_353))
end
| (_75_516, (FStar_Extraction_ML_Syntax.MLP_Tuple (_75_518))::[]) -> begin
(let _170_358 = (let _170_357 = (FStar_Format.text name)
in (let _170_356 = (let _170_355 = (let _170_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _170_354))
in (_170_355)::[])
in (_170_357)::_170_356))
in (FStar_Format.reduce1 _170_358))
end
| _75_523 -> begin
(let _170_365 = (let _170_364 = (FStar_Format.text name)
in (let _170_363 = (let _170_362 = (let _170_361 = (let _170_360 = (FStar_Format.text ", ")
in (let _170_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _170_360 _170_359)))
in (FStar_Format.parens _170_361))
in (_170_362)::[])
in (_170_364)::_170_363))
in (FStar_Format.reduce1 _170_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _170_367 = (let _170_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_366 ps))
in (FStar_Format.parens _170_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _170_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _170_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _75_536 -> (match (_75_536) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _170_374 = (let _170_373 = (FStar_Format.text "|")
in (let _170_372 = (let _170_371 = (doc_of_pattern currentModule p)
in (_170_371)::[])
in (_170_373)::_170_372))
in (FStar_Format.reduce1 _170_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _170_380 = (let _170_379 = (FStar_Format.text "|")
in (let _170_378 = (let _170_377 = (doc_of_pattern currentModule p)
in (let _170_376 = (let _170_375 = (FStar_Format.text "when")
in (_170_375)::(c)::[])
in (_170_377)::_170_376))
in (_170_379)::_170_378))
in (FStar_Format.reduce1 _170_380)))
end)
in (let _170_391 = (let _170_390 = (let _170_385 = (let _170_384 = (let _170_383 = (FStar_Format.text "->")
in (let _170_382 = (let _170_381 = (FStar_Format.text "begin")
in (_170_381)::[])
in (_170_383)::_170_382))
in (case)::_170_384)
in (FStar_Format.reduce1 _170_385))
in (let _170_389 = (let _170_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _170_387 = (let _170_386 = (FStar_Format.text "end")
in (_170_386)::[])
in (_170_388)::_170_387))
in (_170_390)::_170_389))
in (FStar_Format.combine FStar_Format.hardline _170_391)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _75_546 -> (match (_75_546) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _75_554 -> (match (_75_554) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _75_551; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _75_560 -> (match (_75_560) with
| (x, _75_559) -> begin
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
in (let _170_398 = (let _170_397 = (FStar_Format.text ":")
in (_170_397)::(ty)::[])
in (FStar_Format.reduce1 _170_398)))
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
in (let _170_400 = (let _170_399 = (FStar_Format.text ":")
in (_170_399)::(ty)::[])
in (FStar_Format.reduce1 _170_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _170_407 = (let _170_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _170_405 = (let _170_404 = (FStar_Format.reduce1 ids)
in (let _170_403 = (let _170_402 = (let _170_401 = (FStar_Format.text "=")
in (_170_401)::(e)::[])
in (ty_annot)::_170_402)
in (_170_404)::_170_403))
in (_170_406)::_170_405))
in (FStar_Format.reduce1 _170_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _170_411 = (let _170_410 = (FStar_Format.text "let")
in (let _170_409 = (let _170_408 = (FStar_Format.text "rec")
in (_170_408)::[])
in (_170_410)::_170_409))
in (FStar_Format.reduce1 _170_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _170_415 = (let _170_414 = if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_170_414)::(doc)::[])
in (FStar_Format.reduce1 _170_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _75_600 -> (match (_75_600) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _170_422 = (let _170_421 = (FStar_Format.text "#")
in (let _170_420 = (let _170_419 = (FStar_Format.num lineno)
in (let _170_418 = (let _170_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_170_417)::[])
in (_170_419)::_170_418))
in (_170_421)::_170_420))
in (FStar_Format.reduce1 _170_422)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _75_610 -> (match (_75_610) with
| (_75_606, x, tparams, body) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _75_615 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _170_431 = (let _170_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _170_430 doc))
in (FStar_Format.parens _170_431)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _75_628 -> (match (_75_628) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _170_438 = (let _170_437 = (let _170_436 = (FStar_Format.text ":")
in (_170_436)::(ty)::[])
in (name)::_170_437)
in (FStar_Format.reduce1 _170_438))))
end))
in (let _170_441 = (let _170_440 = (FStar_Format.text "; ")
in (let _170_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _170_440 _170_439)))
in (FStar_Format.cbrackets _170_441)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _75_636 -> (match (_75_636) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _75_639 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (let _170_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _170_444 tys))
in (let _170_448 = (let _170_447 = (FStar_Format.text name)
in (let _170_446 = (let _170_445 = (FStar_Format.text "of")
in (_170_445)::(tys)::[])
in (_170_447)::_170_446))
in (FStar_Format.reduce1 _170_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _170_451 = (let _170_450 = (FStar_Format.text "|")
in (_170_450)::(d)::[])
in (FStar_Format.reduce1 _170_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _170_455 = (let _170_454 = (let _170_453 = (let _170_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _170_452))
in (_170_453)::[])
in (tparams)::_170_454)
in (FStar_Format.reduce1 _170_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _170_460 = (let _170_459 = (let _170_458 = (let _170_457 = (let _170_456 = (FStar_Format.text "=")
in (_170_456)::[])
in (doc)::_170_457)
in (FStar_Format.reduce1 _170_458))
in (_170_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _170_460)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _170_465 = (let _170_464 = (FStar_Format.text "type")
in (let _170_463 = (let _170_462 = (let _170_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _170_461 doc))
in (_170_462)::[])
in (_170_464)::_170_463))
in (FStar_Format.reduce1 _170_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _170_485 = (let _170_484 = (let _170_477 = (let _170_476 = (FStar_Format.text "module")
in (let _170_475 = (let _170_474 = (FStar_Format.text x)
in (let _170_473 = (let _170_472 = (FStar_Format.text "=")
in (_170_472)::[])
in (_170_474)::_170_473))
in (_170_476)::_170_475))
in (FStar_Format.reduce1 _170_477))
in (let _170_483 = (let _170_482 = (doc_of_sig currentModule subsig)
in (let _170_481 = (let _170_480 = (let _170_479 = (let _170_478 = (FStar_Format.text "end")
in (_170_478)::[])
in (FStar_Format.reduce1 _170_479))
in (_170_480)::[])
in (_170_482)::_170_481))
in (_170_484)::_170_483))
in (FStar_Format.combine FStar_Format.hardline _170_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _170_489 = (let _170_488 = (FStar_Format.text "exception")
in (let _170_487 = (let _170_486 = (FStar_Format.text x)
in (_170_486)::[])
in (_170_488)::_170_487))
in (FStar_Format.reduce1 _170_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _170_491 = (let _170_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _170_490 args))
in (FStar_Format.parens _170_491))
in (let _170_497 = (let _170_496 = (FStar_Format.text "exception")
in (let _170_495 = (let _170_494 = (FStar_Format.text x)
in (let _170_493 = (let _170_492 = (FStar_Format.text "of")
in (_170_492)::(args)::[])
in (_170_494)::_170_493))
in (_170_496)::_170_495))
in (FStar_Format.reduce1 _170_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_75_670, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _170_503 = (let _170_502 = (FStar_Format.text "val")
in (let _170_501 = (let _170_500 = (FStar_Format.text x)
in (let _170_499 = (let _170_498 = (FStar_Format.text ": ")
in (_170_498)::(ty)::[])
in (_170_500)::_170_499))
in (_170_502)::_170_501))
in (FStar_Format.reduce1 _170_503)))
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
(let _170_514 = (let _170_513 = (FStar_Format.text "exception")
in (let _170_512 = (let _170_511 = (FStar_Format.text x)
in (_170_511)::[])
in (_170_513)::_170_512))
in (FStar_Format.reduce1 _170_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _170_516 = (let _170_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _170_515 args))
in (FStar_Format.parens _170_516))
in (let _170_522 = (let _170_521 = (FStar_Format.text "exception")
in (let _170_520 = (let _170_519 = (FStar_Format.text x)
in (let _170_518 = (let _170_517 = (FStar_Format.text "of")
in (_170_517)::(args)::[])
in (_170_519)::_170_518))
in (_170_521)::_170_520))
in (FStar_Format.reduce1 _170_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, _75_699, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _170_530 = (let _170_529 = (FStar_Format.text "let")
in (let _170_528 = (let _170_527 = (FStar_Format.text "_")
in (let _170_526 = (let _170_525 = (FStar_Format.text "=")
in (let _170_524 = (let _170_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_170_523)::[])
in (_170_525)::_170_524))
in (_170_527)::_170_526))
in (_170_529)::_170_528))
in (FStar_Format.reduce1 _170_530))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_75_712) -> begin
FStar_Format.empty
end
| _75_715 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _75_718 -> (match (_75_718) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _75_725 -> (match (_75_725) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _170_549 = (let _170_548 = (FStar_Format.text "module")
in (let _170_547 = (let _170_546 = (FStar_Format.text x)
in (let _170_545 = (let _170_544 = (FStar_Format.text ":")
in (let _170_543 = (let _170_542 = (FStar_Format.text "sig")
in (_170_542)::[])
in (_170_544)::_170_543))
in (_170_546)::_170_545))
in (_170_548)::_170_547))
in (FStar_Format.reduce1 _170_549))
in (

let tail = (let _170_551 = (let _170_550 = (FStar_Format.text "end")
in (_170_550)::[])
in (FStar_Format.reduce1 _170_551))
in (

let doc = (FStar_Option.map (fun _75_732 -> (match (_75_732) with
| (s, _75_731) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _170_561 = (let _170_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _170_559 = (let _170_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _170_557 = (let _170_556 = (FStar_Format.reduce sub)
in (let _170_555 = (let _170_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_170_554)::[])
in (_170_556)::_170_555))
in (_170_558)::_170_557))
in (_170_560)::_170_559))
in (FStar_Format.reduce _170_561))))))))
end))
and for1_mod = (fun istop _75_745 -> (match (_75_745) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _170_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _170_566 = (FStar_Format.text "module")
in (let _170_565 = (let _170_564 = (FStar_Format.text x)
in (_170_564)::[])
in (_170_566)::_170_565))
end else begin
if (not (istop)) then begin
(let _170_573 = (FStar_Format.text "module")
in (let _170_572 = (let _170_571 = (FStar_Format.text x)
in (let _170_570 = (let _170_569 = (FStar_Format.text "=")
in (let _170_568 = (let _170_567 = (FStar_Format.text "struct")
in (_170_567)::[])
in (_170_569)::_170_568))
in (_170_571)::_170_570))
in (_170_573)::_170_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _170_574))
in (

let tail = if (not (istop)) then begin
(let _170_576 = (let _170_575 = (FStar_Format.text "end")
in (_170_575)::[])
in (FStar_Format.reduce1 _170_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _75_752 -> (match (_75_752) with
| (_75_750, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _170_580 = (let _170_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _170_579 FStar_Format.hardline))
in (_170_580)::[])
end else begin
[]
end
in (let _170_592 = (let _170_591 = (let _170_590 = (let _170_589 = (let _170_588 = (FStar_Format.text "open Prims")
in (let _170_587 = (let _170_586 = (let _170_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _170_584 = (let _170_583 = (FStar_Format.reduce sub)
in (let _170_582 = (let _170_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_170_581)::[])
in (_170_583)::_170_582))
in (_170_585)::_170_584))
in (FStar_Format.hardline)::_170_586)
in (_170_588)::_170_587))
in (FStar_Format.hardline)::_170_589)
in (head)::_170_590)
in (FStar_List.append prefix _170_591))
in (FStar_All.pipe_left FStar_Format.reduce _170_592)))))))))
end))
in (

let docs = (FStar_List.map (fun _75_764 -> (match (_75_764) with
| (x, s, m) -> begin
(let _170_595 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _170_594 = (for1_mod true ((x), (s), (m)))
in ((_170_595), (_170_594))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _170_602 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _170_602 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _170_607 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _170_607 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





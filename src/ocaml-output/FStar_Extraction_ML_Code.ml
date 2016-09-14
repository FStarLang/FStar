
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
| Infix (_74_4) -> begin
_74_4
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
| ([], _74_9) -> begin
true
end
| ((x1)::t1, (x2)::t2) when (x1 = x2) -> begin
(in_ns ((t1), (t2)))
end
| (_74_19, _74_21) -> begin
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

let _74_32 = (FStar_Util.first_N cg_len ns)
in (match (_74_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _167_31 = (let _167_30 = (let _167_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_167_29)::[])
in (FStar_List.append pfx _167_30))
in Some (_167_31))
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
| _74_42 -> begin
(

let _74_45 = x
in (match (_74_45) with
| (ns, x) -> begin
(let _167_36 = (path_of_ns currentModule ns)
in ((_167_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _167_39 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.lowercase _167_39)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
(Prims.strcat "l__" s)
end else begin
s
end)


let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(

let _74_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_74_51) with
| (p, s) -> begin
(let _167_46 = (let _167_45 = (let _167_44 = (ptsym_of_symbol s)
in (_167_44)::[])
in (FStar_List.append p _167_45))
in (FStar_String.concat "." _167_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _74_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_74_56) with
| (p, s) -> begin
(

let s = if ((let _167_51 = (FStar_String.get s (Prims.parse_int "0"))
in (FStar_Char.uppercase _167_51)) <> (FStar_String.get s (Prims.parse_int "0"))) then begin
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


let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _74_61 -> (match (_74_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _74_67 -> (match (_74_67) with
| (y, _74_64, _74_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))


let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))


let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _74_71 -> (match (_74_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _74_75 -> (match (_74_75) with
| (y, _74_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))


let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))


let as_standard_type = (fun _74_79 -> (match (_74_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _74_83 -> (match (_74_83) with
| (y, _74_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))


let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))


let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _74_87 -> (match (_74_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _74_91 -> (match (_74_91) with
| (y, _74_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))


let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))


let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _74_95 inner doc -> (match (_74_95) with
| (outer, side) -> begin
(

let noparens = (fun _inner _outer side -> (

let _74_104 = _inner
in (match (_74_104) with
| (pi, fi) -> begin
(

let _74_107 = _outer
in (match (_74_107) with
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
| (_74_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_74_135, _74_137) -> begin
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


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _74_1 -> (match (_74_1) with
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
(let _167_101 = (let _167_100 = (escape_or escape_char_hex c)
in (Prims.strcat _167_100 "\'"))
in (Prims.strcat "\'" _167_101))
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
(let _167_103 = (let _167_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _167_102 "\""))
in (Prims.strcat "\"" _167_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _167_105 = (let _167_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _167_104 "\""))
in (Prims.strcat "\"" _167_105))
end
| _74_203 -> begin
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
in (let _167_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _167_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _167_120 = (let _167_119 = (let _167_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _167_118 doc))
in (FStar_Format.hbox _167_119))
in (FStar_Format.parens _167_120))
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
| _74_223 -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _167_123 = (let _167_122 = (let _167_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_121 args))
in (FStar_Format.hbox _167_122))
in (FStar_Format.parens _167_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _167_125 = (let _167_124 = (as_standard_type name)
in (FStar_Option.get _167_124))
in (Prims.snd _167_125))
end else begin
(ptsym currentModule name)
end
in (let _167_129 = (let _167_128 = (let _167_127 = (let _167_126 = (FStar_Format.text name)
in (_167_126)::[])
in (args)::_167_127)
in (FStar_Format.reduce1 _167_128))
in (FStar_Format.hbox _167_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _74_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _167_134 = (let _167_133 = (let _167_132 = (let _167_131 = (let _167_130 = (FStar_Format.text " -> ")
in (_167_130)::(d2)::[])
in (d1)::_167_131)
in (FStar_Format.reduce1 _167_132))
in (FStar_Format.hbox _167_133))
in (maybe_paren outer t_prio_fun _167_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _167_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _167_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _167_161 = (let _167_160 = (let _167_159 = (FStar_Format.text "Prims.checked_cast")
in (_167_159)::(doc)::[])
in (FStar_Format.reduce _167_160))
in (FStar_Format.parens _167_161))
end else begin
(let _167_166 = (let _167_165 = (let _167_164 = (FStar_Format.text "Obj.magic ")
in (let _167_163 = (let _167_162 = (FStar_Format.parens doc)
in (_167_162)::[])
in (_167_164)::_167_163))
in (FStar_Format.reduce _167_165))
in (FStar_Format.parens _167_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _167_170 = (let _167_169 = (let _167_168 = (FStar_Format.text ";")
in (_167_168)::(FStar_Format.hardline)::[])
in (d)::_167_169)
in (FStar_Format.reduce _167_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _167_171 = (string_of_mlconstant c)
in (FStar_Format.text _167_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _74_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _167_172 = (ptsym currentModule path)
in (FStar_Format.text _167_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _74_269 -> (match (_74_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _167_179 = (let _167_178 = (let _167_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _167_175))
in (let _167_177 = (let _167_176 = (FStar_Format.text "=")
in (_167_176)::(doc)::[])
in (_167_178)::_167_177))
in (FStar_Format.reduce1 _167_179)))
end))
in (let _167_182 = (let _167_181 = (FStar_Format.text "; ")
in (let _167_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _167_181 _167_180)))
in (FStar_Format.cbrackets _167_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _167_184 = (let _167_183 = (as_standard_constructor ctor)
in (FStar_Option.get _167_183))
in (Prims.snd _167_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _167_186 = (let _167_185 = (as_standard_constructor ctor)
in (FStar_Option.get _167_185))
in (Prims.snd _167_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _167_190 = (let _167_189 = (FStar_Format.parens x)
in (let _167_188 = (let _167_187 = (FStar_Format.text "::")
in (_167_187)::(xs)::[])
in (_167_189)::_167_188))
in (FStar_Format.reduce _167_190))
end
| (_74_288, _74_290) -> begin
(let _167_196 = (let _167_195 = (FStar_Format.text name)
in (let _167_194 = (let _167_193 = (let _167_192 = (let _167_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_191 args))
in (FStar_Format.parens _167_192))
in (_167_193)::[])
in (_167_195)::_167_194))
in (FStar_Format.reduce1 _167_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _167_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _167_198))) es)
in (

let docs = (let _167_200 = (let _167_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_199 docs))
in (FStar_Format.parens _167_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _167_203 = (let _167_202 = (let _167_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_167_201)::[])
in (FStar_Format.hardline)::_167_202)
in (FStar_Format.reduce _167_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _167_210 = (let _167_209 = (let _167_208 = (let _167_207 = (let _167_206 = (let _167_205 = (let _167_204 = (FStar_Format.text "in")
in (_167_204)::(body)::[])
in (FStar_Format.reduce1 _167_205))
in (_167_206)::[])
in (doc)::_167_207)
in (pre)::_167_208)
in (FStar_Format.combine FStar_Format.hardline _167_209))
in (FStar_Format.parens _167_210)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_74_331)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _74_329; FStar_Extraction_ML_Syntax.loc = _74_327})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _74_319))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _74_316; FStar_Extraction_ML_Syntax.loc = _74_314})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(

let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _74_346; FStar_Extraction_ML_Syntax.loc = _74_344}, branches); FStar_Extraction_ML_Syntax.mlty = _74_342; FStar_Extraction_ML_Syntax.loc = _74_340} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _74_365; FStar_Extraction_ML_Syntax.loc = _74_363}, (unitVal)::[]), (e1)::(e2)::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), (e1)::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _74_385; FStar_Extraction_ML_Syntax.loc = _74_383}, (unitVal)::[]), (e1)::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _74_397 -> begin
(

let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (

let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _167_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _167_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _167_216 = (let _167_215 = (let _167_214 = (FStar_Format.text ".")
in (let _167_213 = (let _167_212 = (FStar_Format.text (Prims.snd f))
in (_167_212)::[])
in (_167_214)::_167_213))
in (e)::_167_215)
in (FStar_Format.reduce _167_216))
end else begin
(let _167_222 = (let _167_221 = (let _167_220 = (FStar_Format.text ".")
in (let _167_219 = (let _167_218 = (let _167_217 = (ptsym currentModule f)
in (FStar_Format.text _167_217))
in (_167_218)::[])
in (_167_220)::_167_219))
in (e)::_167_221)
in (FStar_Format.reduce _167_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _167_238 = (let _167_237 = (FStar_Format.text "(")
in (let _167_236 = (let _167_235 = (FStar_Format.text x)
in (let _167_234 = (let _167_233 = (match (xt) with
| Some (xxt) -> begin
(let _167_230 = (let _167_229 = (FStar_Format.text " : ")
in (let _167_228 = (let _167_227 = (doc_of_mltype currentModule outer xxt)
in (_167_227)::[])
in (_167_229)::_167_228))
in (FStar_Format.reduce1 _167_230))
end
| _74_416 -> begin
(FStar_Format.text "")
end)
in (let _167_232 = (let _167_231 = (FStar_Format.text ")")
in (_167_231)::[])
in (_167_233)::_167_232))
in (_167_235)::_167_234))
in (_167_237)::_167_236))
in (FStar_Format.reduce1 _167_238))
end else begin
(FStar_Format.text x)
end)
in (

let ids = (FStar_List.map (fun _74_422 -> (match (_74_422) with
| ((x, _74_419), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (

let doc = (let _167_245 = (let _167_244 = (FStar_Format.text "fun")
in (let _167_243 = (let _167_242 = (FStar_Format.reduce1 ids)
in (let _167_241 = (let _167_240 = (FStar_Format.text "->")
in (_167_240)::(body)::[])
in (_167_242)::_167_241))
in (_167_244)::_167_243))
in (FStar_Format.reduce1 _167_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _167_258 = (let _167_257 = (let _167_252 = (let _167_251 = (FStar_Format.text "if")
in (let _167_250 = (let _167_249 = (let _167_248 = (FStar_Format.text "then")
in (let _167_247 = (let _167_246 = (FStar_Format.text "begin")
in (_167_246)::[])
in (_167_248)::_167_247))
in (cond)::_167_249)
in (_167_251)::_167_250))
in (FStar_Format.reduce1 _167_252))
in (let _167_256 = (let _167_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _167_254 = (let _167_253 = (FStar_Format.text "end")
in (_167_253)::[])
in (_167_255)::_167_254))
in (_167_257)::_167_256))
in (FStar_Format.combine FStar_Format.hardline _167_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _167_281 = (let _167_280 = (let _167_265 = (let _167_264 = (FStar_Format.text "if")
in (let _167_263 = (let _167_262 = (let _167_261 = (FStar_Format.text "then")
in (let _167_260 = (let _167_259 = (FStar_Format.text "begin")
in (_167_259)::[])
in (_167_261)::_167_260))
in (cond)::_167_262)
in (_167_264)::_167_263))
in (FStar_Format.reduce1 _167_265))
in (let _167_279 = (let _167_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _167_277 = (let _167_276 = (let _167_271 = (let _167_270 = (FStar_Format.text "end")
in (let _167_269 = (let _167_268 = (FStar_Format.text "else")
in (let _167_267 = (let _167_266 = (FStar_Format.text "begin")
in (_167_266)::[])
in (_167_268)::_167_267))
in (_167_270)::_167_269))
in (FStar_Format.reduce1 _167_271))
in (let _167_275 = (let _167_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _167_273 = (let _167_272 = (FStar_Format.text "end")
in (_167_272)::[])
in (_167_274)::_167_273))
in (_167_276)::_167_275))
in (_167_278)::_167_277))
in (_167_280)::_167_279))
in (FStar_Format.combine FStar_Format.hardline _167_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _167_288 = (let _167_287 = (let _167_286 = (FStar_Format.text "match")
in (let _167_285 = (let _167_284 = (FStar_Format.parens cond)
in (let _167_283 = (let _167_282 = (FStar_Format.text "with")
in (_167_282)::[])
in (_167_284)::_167_283))
in (_167_286)::_167_285))
in (FStar_Format.reduce1 _167_287))
in (_167_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _167_293 = (let _167_292 = (FStar_Format.text "raise")
in (let _167_291 = (let _167_290 = (let _167_289 = (ptctor currentModule exn)
in (FStar_Format.text _167_289))
in (_167_290)::[])
in (_167_292)::_167_291))
in (FStar_Format.reduce1 _167_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _167_302 = (let _167_301 = (FStar_Format.text "raise")
in (let _167_300 = (let _167_299 = (let _167_294 = (ptctor currentModule exn)
in (FStar_Format.text _167_294))
in (let _167_298 = (let _167_297 = (let _167_296 = (let _167_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_295 args))
in (FStar_Format.parens _167_296))
in (_167_297)::[])
in (_167_299)::_167_298))
in (_167_301)::_167_300))
in (FStar_Format.reduce1 _167_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _167_311 = (let _167_310 = (FStar_Format.text "try")
in (let _167_309 = (let _167_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _167_307 = (let _167_306 = (FStar_Format.text "with")
in (let _167_305 = (let _167_304 = (let _167_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _167_303))
in (_167_304)::[])
in (_167_306)::_167_305))
in (_167_308)::_167_307))
in (_167_310)::_167_309))
in (FStar_Format.combine FStar_Format.hardline _167_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _74_470 = (let _167_316 = (as_bin_op p)
in (FStar_Option.get _167_316))
in (match (_74_470) with
| (_74_467, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _167_319 = (let _167_318 = (let _167_317 = (FStar_Format.text txt)
in (_167_317)::(e2)::[])
in (e1)::_167_318)
in (FStar_Format.reduce1 _167_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _74_480 = (let _167_323 = (as_uni_op p)
in (FStar_Option.get _167_323))
in (match (_74_480) with
| (_74_478, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _167_327 = (let _167_326 = (FStar_Format.text txt)
in (let _167_325 = (let _167_324 = (FStar_Format.parens e1)
in (_167_324)::[])
in (_167_326)::_167_325))
in (FStar_Format.reduce1 _167_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _167_330 = (string_of_mlconstant c)
in (FStar_Format.text _167_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _74_497 -> (match (_74_497) with
| (name, p) -> begin
(let _167_339 = (let _167_338 = (let _167_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _167_333))
in (let _167_337 = (let _167_336 = (FStar_Format.text "=")
in (let _167_335 = (let _167_334 = (doc_of_pattern currentModule p)
in (_167_334)::[])
in (_167_336)::_167_335))
in (_167_338)::_167_337))
in (FStar_Format.reduce1 _167_339))
end))
in (let _167_342 = (let _167_341 = (FStar_Format.text "; ")
in (let _167_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _167_341 _167_340)))
in (FStar_Format.cbrackets _167_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _167_344 = (let _167_343 = (as_standard_constructor ctor)
in (FStar_Option.get _167_343))
in (Prims.snd _167_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _167_346 = (let _167_345 = (as_standard_constructor ctor)
in (FStar_Option.get _167_345))
in (Prims.snd _167_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _167_353 = (let _167_352 = (let _167_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _167_347))
in (let _167_351 = (let _167_350 = (FStar_Format.text "::")
in (let _167_349 = (let _167_348 = (doc_of_pattern currentModule xs)
in (_167_348)::[])
in (_167_350)::_167_349))
in (_167_352)::_167_351))
in (FStar_Format.reduce _167_353))
end
| (_74_514, (FStar_Extraction_ML_Syntax.MLP_Tuple (_74_516))::[]) -> begin
(let _167_358 = (let _167_357 = (FStar_Format.text name)
in (let _167_356 = (let _167_355 = (let _167_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _167_354))
in (_167_355)::[])
in (_167_357)::_167_356))
in (FStar_Format.reduce1 _167_358))
end
| _74_521 -> begin
(let _167_365 = (let _167_364 = (FStar_Format.text name)
in (let _167_363 = (let _167_362 = (let _167_361 = (let _167_360 = (FStar_Format.text ", ")
in (let _167_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _167_360 _167_359)))
in (FStar_Format.parens _167_361))
in (_167_362)::[])
in (_167_364)::_167_363))
in (FStar_Format.reduce1 _167_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _167_367 = (let _167_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_366 ps))
in (FStar_Format.parens _167_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _167_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _167_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _74_534 -> (match (_74_534) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _167_374 = (let _167_373 = (FStar_Format.text "|")
in (let _167_372 = (let _167_371 = (doc_of_pattern currentModule p)
in (_167_371)::[])
in (_167_373)::_167_372))
in (FStar_Format.reduce1 _167_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _167_380 = (let _167_379 = (FStar_Format.text "|")
in (let _167_378 = (let _167_377 = (doc_of_pattern currentModule p)
in (let _167_376 = (let _167_375 = (FStar_Format.text "when")
in (_167_375)::(c)::[])
in (_167_377)::_167_376))
in (_167_379)::_167_378))
in (FStar_Format.reduce1 _167_380)))
end)
in (let _167_391 = (let _167_390 = (let _167_385 = (let _167_384 = (let _167_383 = (FStar_Format.text "->")
in (let _167_382 = (let _167_381 = (FStar_Format.text "begin")
in (_167_381)::[])
in (_167_383)::_167_382))
in (case)::_167_384)
in (FStar_Format.reduce1 _167_385))
in (let _167_389 = (let _167_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _167_387 = (let _167_386 = (FStar_Format.text "end")
in (_167_386)::[])
in (_167_388)::_167_387))
in (_167_390)::_167_389))
in (FStar_Format.combine FStar_Format.hardline _167_391)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _74_544 -> (match (_74_544) with
| (rec_, top_level, lets) -> begin
(

let for1 = (fun _74_552 -> (match (_74_552) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _74_549; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let ids = []
in (

let ids = (FStar_List.map (fun _74_558 -> (match (_74_558) with
| (x, _74_557) -> begin
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
in (let _167_398 = (let _167_397 = (FStar_Format.text ":")
in (_167_397)::(ty)::[])
in (FStar_Format.reduce1 _167_398)))
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
in (let _167_400 = (let _167_399 = (FStar_Format.text ":")
in (_167_399)::(ty)::[])
in (FStar_Format.reduce1 _167_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _167_407 = (let _167_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _167_405 = (let _167_404 = (FStar_Format.reduce1 ids)
in (let _167_403 = (let _167_402 = (let _167_401 = (FStar_Format.text "=")
in (_167_401)::(e)::[])
in (ty_annot)::_167_402)
in (_167_404)::_167_403))
in (_167_406)::_167_405))
in (FStar_Format.reduce1 _167_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _167_411 = (let _167_410 = (FStar_Format.text "let")
in (let _167_409 = (let _167_408 = (FStar_Format.text "rec")
in (_167_408)::[])
in (_167_410)::_167_409))
in (FStar_Format.reduce1 _167_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _167_415 = (let _167_414 = if (i = (Prims.parse_int "0")) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_167_414)::(doc)::[])
in (FStar_Format.reduce1 _167_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _74_598 -> (match (_74_598) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _167_422 = (let _167_421 = (FStar_Format.text "#")
in (let _167_420 = (let _167_419 = (FStar_Format.num lineno)
in (let _167_418 = (let _167_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_167_417)::[])
in (_167_419)::_167_418))
in (_167_421)::_167_420))
in (FStar_Format.reduce1 _167_422)))
end
end))


let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (

let for1 = (fun _74_606 -> (match (_74_606) with
| (x, tparams, body) -> begin
(

let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _74_611 -> begin
(

let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _167_431 = (let _167_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _167_430 doc))
in (FStar_Format.parens _167_431)))
end)
in (

let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(

let forfield = (fun _74_624 -> (match (_74_624) with
| (name, ty) -> begin
(

let name = (FStar_Format.text name)
in (

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _167_438 = (let _167_437 = (let _167_436 = (FStar_Format.text ":")
in (_167_436)::(ty)::[])
in (name)::_167_437)
in (FStar_Format.reduce1 _167_438))))
end))
in (let _167_441 = (let _167_440 = (FStar_Format.text "; ")
in (let _167_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _167_440 _167_439)))
in (FStar_Format.cbrackets _167_441)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(

let forctor = (fun _74_632 -> (match (_74_632) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _74_635 -> begin
(

let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let tys = (let _167_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _167_444 tys))
in (let _167_448 = (let _167_447 = (FStar_Format.text name)
in (let _167_446 = (let _167_445 = (FStar_Format.text "of")
in (_167_445)::(tys)::[])
in (_167_447)::_167_446))
in (FStar_Format.reduce1 _167_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _167_451 = (let _167_450 = (FStar_Format.text "|")
in (_167_450)::(d)::[])
in (FStar_Format.reduce1 _167_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _167_455 = (let _167_454 = (let _167_453 = (let _167_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _167_452))
in (_167_453)::[])
in (tparams)::_167_454)
in (FStar_Format.reduce1 _167_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _167_460 = (let _167_459 = (let _167_458 = (let _167_457 = (let _167_456 = (FStar_Format.text "=")
in (_167_456)::[])
in (doc)::_167_457)
in (FStar_Format.reduce1 _167_458))
in (_167_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _167_460)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > (Prims.parse_int "0")) then begin
(let _167_465 = (let _167_464 = (FStar_Format.text "type")
in (let _167_463 = (let _167_462 = (let _167_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _167_461 doc))
in (_167_462)::[])
in (_167_464)::_167_463))
in (FStar_Format.reduce1 _167_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _167_485 = (let _167_484 = (let _167_477 = (let _167_476 = (FStar_Format.text "module")
in (let _167_475 = (let _167_474 = (FStar_Format.text x)
in (let _167_473 = (let _167_472 = (FStar_Format.text "=")
in (_167_472)::[])
in (_167_474)::_167_473))
in (_167_476)::_167_475))
in (FStar_Format.reduce1 _167_477))
in (let _167_483 = (let _167_482 = (doc_of_sig currentModule subsig)
in (let _167_481 = (let _167_480 = (let _167_479 = (let _167_478 = (FStar_Format.text "end")
in (_167_478)::[])
in (FStar_Format.reduce1 _167_479))
in (_167_480)::[])
in (_167_482)::_167_481))
in (_167_484)::_167_483))
in (FStar_Format.combine FStar_Format.hardline _167_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _167_489 = (let _167_488 = (FStar_Format.text "exception")
in (let _167_487 = (let _167_486 = (FStar_Format.text x)
in (_167_486)::[])
in (_167_488)::_167_487))
in (FStar_Format.reduce1 _167_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _167_491 = (let _167_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _167_490 args))
in (FStar_Format.parens _167_491))
in (let _167_497 = (let _167_496 = (FStar_Format.text "exception")
in (let _167_495 = (let _167_494 = (FStar_Format.text x)
in (let _167_493 = (let _167_492 = (FStar_Format.text "of")
in (_167_492)::(args)::[])
in (_167_494)::_167_493))
in (_167_496)::_167_495))
in (FStar_Format.reduce1 _167_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_74_666, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _167_503 = (let _167_502 = (FStar_Format.text "val")
in (let _167_501 = (let _167_500 = (FStar_Format.text x)
in (let _167_499 = (let _167_498 = (FStar_Format.text ": ")
in (_167_498)::(ty)::[])
in (_167_500)::_167_499))
in (_167_502)::_167_501))
in (FStar_Format.reduce1 _167_503)))
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
(let _167_514 = (let _167_513 = (FStar_Format.text "exception")
in (let _167_512 = (let _167_511 = (FStar_Format.text x)
in (_167_511)::[])
in (_167_513)::_167_512))
in (FStar_Format.reduce1 _167_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _167_516 = (let _167_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _167_515 args))
in (FStar_Format.parens _167_516))
in (let _167_522 = (let _167_521 = (FStar_Format.text "exception")
in (let _167_520 = (let _167_519 = (FStar_Format.text x)
in (let _167_518 = (let _167_517 = (FStar_Format.text "of")
in (_167_517)::(args)::[])
in (_167_519)::_167_518))
in (_167_521)::_167_520))
in (FStar_Format.reduce1 _167_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _167_530 = (let _167_529 = (FStar_Format.text "let")
in (let _167_528 = (let _167_527 = (FStar_Format.text "_")
in (let _167_526 = (let _167_525 = (FStar_Format.text "=")
in (let _167_524 = (let _167_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_167_523)::[])
in (_167_525)::_167_524))
in (_167_527)::_167_526))
in (_167_529)::_167_528))
in (FStar_Format.reduce1 _167_530))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))


let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (

let docs = (FStar_List.map (fun x -> (

let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_74_706) -> begin
FStar_Format.empty
end
| _74_709 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))


let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _74_712 -> (match (_74_712) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(

let rec for1_sig = (fun _74_719 -> (match (_74_719) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _167_549 = (let _167_548 = (FStar_Format.text "module")
in (let _167_547 = (let _167_546 = (FStar_Format.text x)
in (let _167_545 = (let _167_544 = (FStar_Format.text ":")
in (let _167_543 = (let _167_542 = (FStar_Format.text "sig")
in (_167_542)::[])
in (_167_544)::_167_543))
in (_167_546)::_167_545))
in (_167_548)::_167_547))
in (FStar_Format.reduce1 _167_549))
in (

let tail = (let _167_551 = (let _167_550 = (FStar_Format.text "end")
in (_167_550)::[])
in (FStar_Format.reduce1 _167_551))
in (

let doc = (FStar_Option.map (fun _74_726 -> (match (_74_726) with
| (s, _74_725) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _167_561 = (let _167_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _167_559 = (let _167_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _167_557 = (let _167_556 = (FStar_Format.reduce sub)
in (let _167_555 = (let _167_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_167_554)::[])
in (_167_556)::_167_555))
in (_167_558)::_167_557))
in (_167_560)::_167_559))
in (FStar_Format.reduce _167_561))))))))
end))
and for1_mod = (fun istop _74_739 -> (match (_74_739) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (

let head = (let _167_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _167_566 = (FStar_Format.text "module")
in (let _167_565 = (let _167_564 = (FStar_Format.text x)
in (_167_564)::[])
in (_167_566)::_167_565))
end else begin
if (not (istop)) then begin
(let _167_573 = (FStar_Format.text "module")
in (let _167_572 = (let _167_571 = (FStar_Format.text x)
in (let _167_570 = (let _167_569 = (FStar_Format.text "=")
in (let _167_568 = (let _167_567 = (FStar_Format.text "struct")
in (_167_567)::[])
in (_167_569)::_167_568))
in (_167_571)::_167_570))
in (_167_573)::_167_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _167_574))
in (

let tail = if (not (istop)) then begin
(let _167_576 = (let _167_575 = (FStar_Format.text "end")
in (_167_575)::[])
in (FStar_Format.reduce1 _167_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _74_746 -> (match (_74_746) with
| (_74_744, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _167_580 = (let _167_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _167_579 FStar_Format.hardline))
in (_167_580)::[])
end else begin
[]
end
in (let _167_592 = (let _167_591 = (let _167_590 = (let _167_589 = (let _167_588 = (FStar_Format.text "open Prims")
in (let _167_587 = (let _167_586 = (let _167_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _167_584 = (let _167_583 = (FStar_Format.reduce sub)
in (let _167_582 = (let _167_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_167_581)::[])
in (_167_583)::_167_582))
in (_167_585)::_167_584))
in (FStar_Format.hardline)::_167_586)
in (_167_588)::_167_587))
in (FStar_Format.hardline)::_167_589)
in (head)::_167_590)
in (FStar_List.append prefix _167_591))
in (FStar_All.pipe_left FStar_Format.reduce _167_592)))))))))
end))
in (

let docs = (FStar_List.map (fun _74_758 -> (match (_74_758) with
| (x, s, m) -> begin
(let _167_595 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _167_594 = (for1_mod true ((x), (s), (m)))
in ((_167_595), (_167_594))))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _167_602 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _167_602 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _167_607 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _167_607 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty (Prims.parse_int "0") doc)))





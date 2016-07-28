
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


let t_prio_fun : (Prims.int * fixity) = ((10), (Infix (Right)))


let t_prio_tpl : (Prims.int * fixity) = ((20), (Infix (NonAssoc)))


let t_prio_name : (Prims.int * fixity) = ((30), (Postfix))


let e_bin_prio_lambda : (Prims.int * fixity) = ((5), (Prefix))


let e_bin_prio_if : (Prims.int * fixity) = ((15), (Prefix))


let e_bin_prio_letin : (Prims.int * fixity) = ((19), (Prefix))


let e_bin_prio_or : (Prims.int * fixity) = ((20), (Infix (Left)))


let e_bin_prio_and : (Prims.int * fixity) = ((25), (Infix (Left)))


let e_bin_prio_eq : (Prims.int * fixity) = ((27), (Infix (NonAssoc)))


let e_bin_prio_order : (Prims.int * fixity) = ((29), (Infix (NonAssoc)))


let e_bin_prio_op1 : (Prims.int * fixity) = ((30), (Infix (Left)))


let e_bin_prio_op2 : (Prims.int * fixity) = ((40), (Infix (Left)))


let e_bin_prio_op3 : (Prims.int * fixity) = ((50), (Infix (Left)))


let e_bin_prio_op4 : (Prims.int * fixity) = ((60), (Infix (Left)))


let e_bin_prio_comb : (Prims.int * fixity) = ((70), (Infix (Left)))


let e_bin_prio_seq : (Prims.int * fixity) = ((100), (Infix (Left)))


let e_app_prio : (Prims.int * fixity) = ((10000), (Infix (Left)))


let min_op_prec : (Prims.int * fixity) = (((- (1))), (Infix (NonAssoc)))


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
(let _166_31 = (let _166_30 = (let _166_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_166_29)::[])
in (FStar_List.append pfx _166_30))
in Some (_166_31))
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
(let _166_36 = (path_of_ns currentModule ns)
in ((_166_36), (x)))
end))
end))


let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _166_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _166_39)) <> (FStar_String.get s 0)) then begin
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
(let _166_46 = (let _166_45 = (let _166_44 = (ptsym_of_symbol s)
in (_166_44)::[])
in (FStar_List.append p _166_45))
in (FStar_String.concat "." _166_46))
end))
end)


let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (

let _74_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_74_56) with
| (p, s) -> begin
(

let s = if ((let _166_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _166_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))


let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_ColonEquals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("%")))::[]


let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("-")))::((("op_Bang"), ("Support.ST.read")))::[]


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
(let _166_101 = (let _166_100 = (escape_or escape_char_hex c)
in (Prims.strcat _166_100 "\'"))
in (Prims.strcat "\'" _166_101))
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
if (FStar_Options.use_native_int ()) then begin
s
end else begin
(Prims.strcat "(Prims.parse_int \"" (Prims.strcat s "\")"))
end
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let _166_103 = (let _166_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat _166_102 "\""))
in (Prims.strcat "\"" _166_103))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _166_105 = (let _166_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat _166_104 "\""))
in (Prims.strcat "\"" _166_105))
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
in (let _166_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _166_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(

let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (

let doc = (let _166_120 = (let _166_119 = (let _166_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _166_118 doc))
in (FStar_Format.hbox _166_119))
in (FStar_Format.parens _166_120))
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
in (let _166_123 = (let _166_122 = (let _166_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_121 args))
in (FStar_Format.hbox _166_122))
in (FStar_Format.parens _166_123)))
end)
in (

let name = if (is_standard_type name) then begin
(let _166_125 = (let _166_124 = (as_standard_type name)
in (FStar_Option.get _166_124))
in (Prims.snd _166_125))
end else begin
(ptsym currentModule name)
end
in (let _166_129 = (let _166_128 = (let _166_127 = (let _166_126 = (FStar_Format.text name)
in (_166_126)::[])
in (args)::_166_127)
in (FStar_Format.reduce1 _166_128))
in (FStar_Format.hbox _166_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _74_229, t2) -> begin
(

let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (

let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _166_134 = (let _166_133 = (let _166_132 = (let _166_131 = (let _166_130 = (FStar_Format.text " -> ")
in (_166_130)::(d2)::[])
in (d1)::_166_131)
in (FStar_Format.reduce1 _166_132))
in (FStar_Format.hbox _166_133))
in (maybe_paren outer t_prio_fun _166_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _166_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _166_138)))


let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_161 = (let _166_160 = (let _166_159 = (FStar_Format.text "Prims.checked_cast")
in (_166_159)::(doc)::[])
in (FStar_Format.reduce _166_160))
in (FStar_Format.parens _166_161))
end else begin
(let _166_166 = (let _166_165 = (let _166_164 = (FStar_Format.text "Obj.magic ")
in (let _166_163 = (let _166_162 = (FStar_Format.parens doc)
in (_166_162)::[])
in (_166_164)::_166_163))
in (FStar_Format.reduce _166_165))
in (FStar_Format.parens _166_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(

let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (

let docs = (FStar_List.map (fun d -> (let _166_170 = (let _166_169 = (let _166_168 = (FStar_Format.text ";")
in (_166_168)::(FStar_Format.hardline)::[])
in (d)::_166_169)
in (FStar_Format.reduce _166_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _166_171 = (string_of_mlconstant c)
in (FStar_Format.text _166_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _74_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _166_172 = (ptsym currentModule path)
in (FStar_Format.text _166_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(

let for1 = (fun _74_269 -> (match (_74_269) with
| (name, e) -> begin
(

let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _166_179 = (let _166_178 = (let _166_175 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _166_175))
in (let _166_177 = (let _166_176 = (FStar_Format.text "=")
in (_166_176)::(doc)::[])
in (_166_178)::_166_177))
in (FStar_Format.reduce1 _166_179)))
end))
in (let _166_182 = (let _166_181 = (FStar_Format.text "; ")
in (let _166_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _166_181 _166_180)))
in (FStar_Format.cbrackets _166_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _166_184 = (let _166_183 = (as_standard_constructor ctor)
in (FStar_Option.get _166_183))
in (Prims.snd _166_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _166_186 = (let _166_185 = (as_standard_constructor ctor)
in (FStar_Option.get _166_185))
in (Prims.snd _166_186))
end else begin
(ptctor currentModule ctor)
end
in (

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (

let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(let _166_190 = (let _166_189 = (FStar_Format.parens x)
in (let _166_188 = (let _166_187 = (FStar_Format.text "::")
in (_166_187)::(xs)::[])
in (_166_189)::_166_188))
in (FStar_Format.reduce _166_190))
end
| (_74_288, _74_290) -> begin
(let _166_196 = (let _166_195 = (FStar_Format.text name)
in (let _166_194 = (let _166_193 = (let _166_192 = (let _166_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_191 args))
in (FStar_Format.parens _166_192))
in (_166_193)::[])
in (_166_195)::_166_194))
in (FStar_Format.reduce1 _166_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(

let docs = (FStar_List.map (fun x -> (let _166_198 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _166_198))) es)
in (

let docs = (let _166_200 = (let _166_199 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_199 docs))
in (FStar_Format.parens _166_200))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(

let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _166_203 = (let _166_202 = (let _166_201 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_166_201)::[])
in (FStar_Format.hardline)::_166_202)
in (FStar_Format.reduce _166_203))
end else begin
FStar_Format.empty
end
in (

let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (

let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _166_210 = (let _166_209 = (let _166_208 = (let _166_207 = (let _166_206 = (let _166_205 = (let _166_204 = (FStar_Format.text "in")
in (_166_204)::(body)::[])
in (FStar_Format.reduce1 _166_205))
in (_166_206)::[])
in (doc)::_166_207)
in (pre)::_166_208)
in (FStar_Format.combine FStar_Format.hardline _166_209))
in (FStar_Format.parens _166_210)))))
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
in (let _166_211 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _166_211))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(

let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (

let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_216 = (let _166_215 = (let _166_214 = (FStar_Format.text ".")
in (let _166_213 = (let _166_212 = (FStar_Format.text (Prims.snd f))
in (_166_212)::[])
in (_166_214)::_166_213))
in (e)::_166_215)
in (FStar_Format.reduce _166_216))
end else begin
(let _166_222 = (let _166_221 = (let _166_220 = (FStar_Format.text ".")
in (let _166_219 = (let _166_218 = (let _166_217 = (ptsym currentModule f)
in (FStar_Format.text _166_217))
in (_166_218)::[])
in (_166_220)::_166_219))
in (e)::_166_221)
in (FStar_Format.reduce _166_222))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(

let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_238 = (let _166_237 = (FStar_Format.text "(")
in (let _166_236 = (let _166_235 = (FStar_Format.text x)
in (let _166_234 = (let _166_233 = (match (xt) with
| Some (xxt) -> begin
(let _166_230 = (let _166_229 = (FStar_Format.text " : ")
in (let _166_228 = (let _166_227 = (doc_of_mltype currentModule outer xxt)
in (_166_227)::[])
in (_166_229)::_166_228))
in (FStar_Format.reduce1 _166_230))
end
| _74_416 -> begin
(FStar_Format.text "")
end)
in (let _166_232 = (let _166_231 = (FStar_Format.text ")")
in (_166_231)::[])
in (_166_233)::_166_232))
in (_166_235)::_166_234))
in (_166_237)::_166_236))
in (FStar_Format.reduce1 _166_238))
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

let doc = (let _166_245 = (let _166_244 = (FStar_Format.text "fun")
in (let _166_243 = (let _166_242 = (FStar_Format.reduce1 ids)
in (let _166_241 = (let _166_240 = (FStar_Format.text "->")
in (_166_240)::(body)::[])
in (_166_242)::_166_241))
in (_166_244)::_166_243))
in (FStar_Format.reduce1 _166_245))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _166_258 = (let _166_257 = (let _166_252 = (let _166_251 = (FStar_Format.text "if")
in (let _166_250 = (let _166_249 = (let _166_248 = (FStar_Format.text "then")
in (let _166_247 = (let _166_246 = (FStar_Format.text "begin")
in (_166_246)::[])
in (_166_248)::_166_247))
in (cond)::_166_249)
in (_166_251)::_166_250))
in (FStar_Format.reduce1 _166_252))
in (let _166_256 = (let _166_255 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _166_254 = (let _166_253 = (FStar_Format.text "end")
in (_166_253)::[])
in (_166_255)::_166_254))
in (_166_257)::_166_256))
in (FStar_Format.combine FStar_Format.hardline _166_258))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let doc = (let _166_281 = (let _166_280 = (let _166_265 = (let _166_264 = (FStar_Format.text "if")
in (let _166_263 = (let _166_262 = (let _166_261 = (FStar_Format.text "then")
in (let _166_260 = (let _166_259 = (FStar_Format.text "begin")
in (_166_259)::[])
in (_166_261)::_166_260))
in (cond)::_166_262)
in (_166_264)::_166_263))
in (FStar_Format.reduce1 _166_265))
in (let _166_279 = (let _166_278 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _166_277 = (let _166_276 = (let _166_271 = (let _166_270 = (FStar_Format.text "end")
in (let _166_269 = (let _166_268 = (FStar_Format.text "else")
in (let _166_267 = (let _166_266 = (FStar_Format.text "begin")
in (_166_266)::[])
in (_166_268)::_166_267))
in (_166_270)::_166_269))
in (FStar_Format.reduce1 _166_271))
in (let _166_275 = (let _166_274 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (let _166_273 = (let _166_272 = (FStar_Format.text "end")
in (_166_272)::[])
in (_166_274)::_166_273))
in (_166_276)::_166_275))
in (_166_278)::_166_277))
in (_166_280)::_166_279))
in (FStar_Format.combine FStar_Format.hardline _166_281))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(

let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (

let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (

let doc = (let _166_288 = (let _166_287 = (let _166_286 = (FStar_Format.text "match")
in (let _166_285 = (let _166_284 = (FStar_Format.parens cond)
in (let _166_283 = (let _166_282 = (FStar_Format.text "with")
in (_166_282)::[])
in (_166_284)::_166_283))
in (_166_286)::_166_285))
in (FStar_Format.reduce1 _166_287))
in (_166_288)::pats)
in (

let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _166_293 = (let _166_292 = (FStar_Format.text "raise")
in (let _166_291 = (let _166_290 = (let _166_289 = (ptctor currentModule exn)
in (FStar_Format.text _166_289))
in (_166_290)::[])
in (_166_292)::_166_291))
in (FStar_Format.reduce1 _166_293))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(

let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _166_302 = (let _166_301 = (FStar_Format.text "raise")
in (let _166_300 = (let _166_299 = (let _166_294 = (ptctor currentModule exn)
in (FStar_Format.text _166_294))
in (let _166_298 = (let _166_297 = (let _166_296 = (let _166_295 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_295 args))
in (FStar_Format.parens _166_296))
in (_166_297)::[])
in (_166_299)::_166_298))
in (_166_301)::_166_300))
in (FStar_Format.reduce1 _166_302)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _166_311 = (let _166_310 = (FStar_Format.text "try")
in (let _166_309 = (let _166_308 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _166_307 = (let _166_306 = (FStar_Format.text "with")
in (let _166_305 = (let _166_304 = (let _166_303 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _166_303))
in (_166_304)::[])
in (_166_306)::_166_305))
in (_166_308)::_166_307))
in (_166_310)::_166_309))
in (FStar_Format.combine FStar_Format.hardline _166_311))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (

let _74_470 = (let _166_316 = (as_bin_op p)
in (FStar_Option.get _166_316))
in (match (_74_470) with
| (_74_467, prio, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (

let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (

let doc = (let _166_319 = (let _166_318 = (let _166_317 = (FStar_Format.text txt)
in (_166_317)::(e2)::[])
in (e1)::_166_318)
in (FStar_Format.reduce1 _166_319))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (

let _74_480 = (let _166_323 = (as_uni_op p)
in (FStar_Option.get _166_323))
in (match (_74_480) with
| (_74_478, txt) -> begin
(

let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (

let doc = (let _166_327 = (let _166_326 = (FStar_Format.text txt)
in (let _166_325 = (let _166_324 = (FStar_Format.parens e1)
in (_166_324)::[])
in (_166_326)::_166_325))
in (FStar_Format.reduce1 _166_327))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _166_330 = (string_of_mlconstant c)
in (FStar_Format.text _166_330))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(

let for1 = (fun _74_497 -> (match (_74_497) with
| (name, p) -> begin
(let _166_339 = (let _166_338 = (let _166_333 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _166_333))
in (let _166_337 = (let _166_336 = (FStar_Format.text "=")
in (let _166_335 = (let _166_334 = (doc_of_pattern currentModule p)
in (_166_334)::[])
in (_166_336)::_166_335))
in (_166_338)::_166_337))
in (FStar_Format.reduce1 _166_339))
end))
in (let _166_342 = (let _166_341 = (FStar_Format.text "; ")
in (let _166_340 = (FStar_List.map for1 fields)
in (FStar_Format.combine _166_341 _166_340)))
in (FStar_Format.cbrackets _166_342)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _166_344 = (let _166_343 = (as_standard_constructor ctor)
in (FStar_Option.get _166_343))
in (Prims.snd _166_344))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(

let name = if (is_standard_constructor ctor) then begin
(let _166_346 = (let _166_345 = (as_standard_constructor ctor)
in (FStar_Option.get _166_345))
in (Prims.snd _166_346))
end else begin
(ptctor currentModule ctor)
end
in (

let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _166_353 = (let _166_352 = (let _166_347 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _166_347))
in (let _166_351 = (let _166_350 = (FStar_Format.text "::")
in (let _166_349 = (let _166_348 = (doc_of_pattern currentModule xs)
in (_166_348)::[])
in (_166_350)::_166_349))
in (_166_352)::_166_351))
in (FStar_Format.reduce _166_353))
end
| (_74_514, (FStar_Extraction_ML_Syntax.MLP_Tuple (_74_516))::[]) -> begin
(let _166_358 = (let _166_357 = (FStar_Format.text name)
in (let _166_356 = (let _166_355 = (let _166_354 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _166_354))
in (_166_355)::[])
in (_166_357)::_166_356))
in (FStar_Format.reduce1 _166_358))
end
| _74_521 -> begin
(let _166_365 = (let _166_364 = (FStar_Format.text name)
in (let _166_363 = (let _166_362 = (let _166_361 = (let _166_360 = (FStar_Format.text ", ")
in (let _166_359 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _166_360 _166_359)))
in (FStar_Format.parens _166_361))
in (_166_362)::[])
in (_166_364)::_166_363))
in (FStar_Format.reduce1 _166_365))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _166_367 = (let _166_366 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_366 ps))
in (FStar_Format.parens _166_367)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(

let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (

let ps = (FStar_List.map FStar_Format.parens ps)
in (let _166_368 = (FStar_Format.text " | ")
in (FStar_Format.combine _166_368 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _74_534 -> (match (_74_534) with
| (p, cond, e) -> begin
(

let case = (match (cond) with
| None -> begin
(let _166_374 = (let _166_373 = (FStar_Format.text "|")
in (let _166_372 = (let _166_371 = (doc_of_pattern currentModule p)
in (_166_371)::[])
in (_166_373)::_166_372))
in (FStar_Format.reduce1 _166_374))
end
| Some (c) -> begin
(

let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _166_380 = (let _166_379 = (FStar_Format.text "|")
in (let _166_378 = (let _166_377 = (doc_of_pattern currentModule p)
in (let _166_376 = (let _166_375 = (FStar_Format.text "when")
in (_166_375)::(c)::[])
in (_166_377)::_166_376))
in (_166_379)::_166_378))
in (FStar_Format.reduce1 _166_380)))
end)
in (let _166_391 = (let _166_390 = (let _166_385 = (let _166_384 = (let _166_383 = (FStar_Format.text "->")
in (let _166_382 = (let _166_381 = (FStar_Format.text "begin")
in (_166_381)::[])
in (_166_383)::_166_382))
in (case)::_166_384)
in (FStar_Format.reduce1 _166_385))
in (let _166_389 = (let _166_388 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _166_387 = (let _166_386 = (FStar_Format.text "end")
in (_166_386)::[])
in (_166_388)::_166_387))
in (_166_390)::_166_389))
in (FStar_Format.combine FStar_Format.hardline _166_391)))
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
in (let _166_398 = (let _166_397 = (FStar_Format.text ":")
in (_166_397)::(ty)::[])
in (FStar_Format.reduce1 _166_398)))
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
in (let _166_400 = (let _166_399 = (FStar_Format.text ":")
in (_166_399)::(ty)::[])
in (FStar_Format.reduce1 _166_400)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _166_407 = (let _166_406 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _166_405 = (let _166_404 = (FStar_Format.reduce1 ids)
in (let _166_403 = (let _166_402 = (let _166_401 = (FStar_Format.text "=")
in (_166_401)::(e)::[])
in (ty_annot)::_166_402)
in (_166_404)::_166_403))
in (_166_406)::_166_405))
in (FStar_Format.reduce1 _166_407))))))
end))
in (

let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(let _166_411 = (let _166_410 = (FStar_Format.text "let")
in (let _166_409 = (let _166_408 = (FStar_Format.text "rec")
in (_166_408)::[])
in (_166_410)::_166_409))
in (FStar_Format.reduce1 _166_411))
end else begin
(FStar_Format.text "let")
end
in (

let lets = (FStar_List.map for1 lets)
in (

let lets = (FStar_List.mapi (fun i doc -> (let _166_415 = (let _166_414 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_166_414)::(doc)::[])
in (FStar_Format.reduce1 _166_415))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _74_598 -> (match (_74_598) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(

let file = (FStar_Util.basename file)
in (let _166_422 = (let _166_421 = (FStar_Format.text "#")
in (let _166_420 = (let _166_419 = (FStar_Format.num lineno)
in (let _166_418 = (let _166_417 = (FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\"")))
in (_166_417)::[])
in (_166_419)::_166_418))
in (_166_421)::_166_420))
in (FStar_Format.reduce1 _166_422)))
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
in (let _166_431 = (let _166_430 = (FStar_Format.text ", ")
in (FStar_Format.combine _166_430 doc))
in (FStar_Format.parens _166_431)))
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
in (let _166_438 = (let _166_437 = (let _166_436 = (FStar_Format.text ":")
in (_166_436)::(ty)::[])
in (name)::_166_437)
in (FStar_Format.reduce1 _166_438))))
end))
in (let _166_441 = (let _166_440 = (FStar_Format.text "; ")
in (let _166_439 = (FStar_List.map forfield fields)
in (FStar_Format.combine _166_440 _166_439)))
in (FStar_Format.cbrackets _166_441)))
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

let tys = (let _166_444 = (FStar_Format.text " * ")
in (FStar_Format.combine _166_444 tys))
in (let _166_448 = (let _166_447 = (FStar_Format.text name)
in (let _166_446 = (let _166_445 = (FStar_Format.text "of")
in (_166_445)::(tys)::[])
in (_166_447)::_166_446))
in (FStar_Format.reduce1 _166_448))))
end)
end))
in (

let ctors = (FStar_List.map forctor ctors)
in (

let ctors = (FStar_List.map (fun d -> (let _166_451 = (let _166_450 = (FStar_Format.text "|")
in (_166_450)::(d)::[])
in (FStar_Format.reduce1 _166_451))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (

let doc = (let _166_455 = (let _166_454 = (let _166_453 = (let _166_452 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _166_452))
in (_166_453)::[])
in (tparams)::_166_454)
in (FStar_Format.reduce1 _166_455))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(

let body = (forbody body)
in (let _166_460 = (let _166_459 = (let _166_458 = (let _166_457 = (let _166_456 = (FStar_Format.text "=")
in (_166_456)::[])
in (doc)::_166_457)
in (FStar_Format.reduce1 _166_458))
in (_166_459)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _166_460)))
end))))
end))
in (

let doc = (FStar_List.map for1 decls)
in (

let doc = if ((FStar_List.length doc) > 0) then begin
(let _166_465 = (let _166_464 = (FStar_Format.text "type")
in (let _166_463 = (let _166_462 = (let _166_461 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _166_461 doc))
in (_166_462)::[])
in (_166_464)::_166_463))
in (FStar_Format.reduce1 _166_465))
end else begin
(FStar_Format.text "")
end
in doc))))


let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _166_485 = (let _166_484 = (let _166_477 = (let _166_476 = (FStar_Format.text "module")
in (let _166_475 = (let _166_474 = (FStar_Format.text x)
in (let _166_473 = (let _166_472 = (FStar_Format.text "=")
in (_166_472)::[])
in (_166_474)::_166_473))
in (_166_476)::_166_475))
in (FStar_Format.reduce1 _166_477))
in (let _166_483 = (let _166_482 = (doc_of_sig currentModule subsig)
in (let _166_481 = (let _166_480 = (let _166_479 = (let _166_478 = (FStar_Format.text "end")
in (_166_478)::[])
in (FStar_Format.reduce1 _166_479))
in (_166_480)::[])
in (_166_482)::_166_481))
in (_166_484)::_166_483))
in (FStar_Format.combine FStar_Format.hardline _166_485))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _166_489 = (let _166_488 = (FStar_Format.text "exception")
in (let _166_487 = (let _166_486 = (FStar_Format.text x)
in (_166_486)::[])
in (_166_488)::_166_487))
in (FStar_Format.reduce1 _166_489))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _166_491 = (let _166_490 = (FStar_Format.text " * ")
in (FStar_Format.combine _166_490 args))
in (FStar_Format.parens _166_491))
in (let _166_497 = (let _166_496 = (FStar_Format.text "exception")
in (let _166_495 = (let _166_494 = (FStar_Format.text x)
in (let _166_493 = (let _166_492 = (FStar_Format.text "of")
in (_166_492)::(args)::[])
in (_166_494)::_166_493))
in (_166_496)::_166_495))
in (FStar_Format.reduce1 _166_497))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_74_666, ty)) -> begin
(

let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (let _166_503 = (let _166_502 = (FStar_Format.text "val")
in (let _166_501 = (let _166_500 = (FStar_Format.text x)
in (let _166_499 = (let _166_498 = (FStar_Format.text ": ")
in (_166_498)::(ty)::[])
in (_166_500)::_166_499))
in (_166_502)::_166_501))
in (FStar_Format.reduce1 _166_503)))
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
(let _166_514 = (let _166_513 = (FStar_Format.text "exception")
in (let _166_512 = (let _166_511 = (FStar_Format.text x)
in (_166_511)::[])
in (_166_513)::_166_512))
in (FStar_Format.reduce1 _166_514))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(

let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (

let args = (let _166_516 = (let _166_515 = (FStar_Format.text " * ")
in (FStar_Format.combine _166_515 args))
in (FStar_Format.parens _166_516))
in (let _166_522 = (let _166_521 = (FStar_Format.text "exception")
in (let _166_520 = (let _166_519 = (FStar_Format.text x)
in (let _166_518 = (let _166_517 = (FStar_Format.text "of")
in (_166_517)::(args)::[])
in (_166_519)::_166_518))
in (_166_521)::_166_520))
in (FStar_Format.reduce1 _166_522))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _166_530 = (let _166_529 = (FStar_Format.text "let")
in (let _166_528 = (let _166_527 = (FStar_Format.text "_")
in (let _166_526 = (let _166_525 = (FStar_Format.text "=")
in (let _166_524 = (let _166_523 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_166_523)::[])
in (_166_525)::_166_524))
in (_166_527)::_166_526))
in (_166_529)::_166_528))
in (FStar_Format.reduce1 _166_530))
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

let head = (let _166_549 = (let _166_548 = (FStar_Format.text "module")
in (let _166_547 = (let _166_546 = (FStar_Format.text x)
in (let _166_545 = (let _166_544 = (FStar_Format.text ":")
in (let _166_543 = (let _166_542 = (FStar_Format.text "sig")
in (_166_542)::[])
in (_166_544)::_166_543))
in (_166_546)::_166_545))
in (_166_548)::_166_547))
in (FStar_Format.reduce1 _166_549))
in (

let tail = (let _166_551 = (let _166_550 = (FStar_Format.text "end")
in (_166_550)::[])
in (FStar_Format.reduce1 _166_551))
in (

let doc = (FStar_Option.map (fun _74_725 -> (match (_74_725) with
| (s, _74_724) -> begin
(doc_of_sig x s)
end)) sigmod)
in (

let sub = (FStar_List.map for1_sig sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _166_561 = (let _166_560 = (FStar_Format.cat head FStar_Format.hardline)
in (let _166_559 = (let _166_558 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _166_557 = (let _166_556 = (FStar_Format.reduce sub)
in (let _166_555 = (let _166_554 = (FStar_Format.cat tail FStar_Format.hardline)
in (_166_554)::[])
in (_166_556)::_166_555))
in (_166_558)::_166_557))
in (_166_560)::_166_559))
in (FStar_Format.reduce _166_561)))))))
end))
and for1_mod = (fun istop _74_738 -> (match (_74_738) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(

let head = (let _166_574 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_566 = (FStar_Format.text "module")
in (let _166_565 = (let _166_564 = (FStar_Format.text x)
in (_166_564)::[])
in (_166_566)::_166_565))
end else begin
if (not (istop)) then begin
(let _166_573 = (FStar_Format.text "module")
in (let _166_572 = (let _166_571 = (FStar_Format.text x)
in (let _166_570 = (let _166_569 = (FStar_Format.text "=")
in (let _166_568 = (let _166_567 = (FStar_Format.text "struct")
in (_166_567)::[])
in (_166_569)::_166_568))
in (_166_571)::_166_570))
in (_166_573)::_166_572))
end else begin
[]
end
end
in (FStar_Format.reduce1 _166_574))
in (

let tail = if (not (istop)) then begin
(let _166_576 = (let _166_575 = (FStar_Format.text "end")
in (_166_575)::[])
in (FStar_Format.reduce1 _166_576))
end else begin
(FStar_Format.reduce1 [])
end
in (

let doc = (FStar_Option.map (fun _74_744 -> (match (_74_744) with
| (_74_742, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (

let sub = (FStar_List.map (for1_mod false) sub)
in (

let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (

let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_580 = (let _166_579 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _166_579 FStar_Format.hardline))
in (_166_580)::[])
end else begin
[]
end
in (let _166_592 = (let _166_591 = (let _166_590 = (let _166_589 = (let _166_588 = (FStar_Format.text "open Prims")
in (let _166_587 = (let _166_586 = (let _166_585 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _166_584 = (let _166_583 = (FStar_Format.reduce sub)
in (let _166_582 = (let _166_581 = (FStar_Format.cat tail FStar_Format.hardline)
in (_166_581)::[])
in (_166_583)::_166_582))
in (_166_585)::_166_584))
in (FStar_Format.hardline)::_166_586)
in (_166_588)::_166_587))
in (FStar_Format.hardline)::_166_589)
in (head)::_166_590)
in (FStar_List.append prefix _166_591))
in (FStar_All.pipe_left FStar_Format.reduce _166_592))))))))
end))
in (

let docs = (FStar_List.map (fun _74_756 -> (match (_74_756) with
| (x, s, m) -> begin
(let _166_594 = (for1_mod true ((x), (s), (m)))
in ((x), (_166_594)))
end)) mllib)
in docs))
end))


let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))


let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (

let doc = (let _166_601 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _166_601 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty 0 doc)))


let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (

let doc = (let _166_606 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _166_606 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty 0 doc)))





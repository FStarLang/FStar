
open Prims
# 32 "FStar.Extraction.ML.Code.fst"
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 35 "FStar.Extraction.ML.Code.fst"
let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 35 "FStar.Extraction.ML.Code.fst"
type fixity =
| Prefix
| Postfix
| Infix of assoc

# 36 "FStar.Extraction.ML.Code.fst"
let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_74_4) -> begin
_74_4
end))

# 36 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 37 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 38 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = ((10), (Infix (Right)))

# 40 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = ((20), (Infix (NonAssoc)))

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = ((30), (Postfix))

# 42 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = ((5), (Prefix))

# 44 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = ((15), (Prefix))

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = ((19), (Prefix))

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = ((20), (Infix (Left)))

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = ((25), (Infix (Left)))

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = ((27), (Infix (NonAssoc)))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = ((29), (Infix (NonAssoc)))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = ((30), (Infix (Left)))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = ((40), (Infix (Left)))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = ((50), (Infix (Left)))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = ((60), (Infix (Left)))

# 54 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = ((70), (Infix (Left)))

# 55 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = ((100), (Infix (Left)))

# 56 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = ((10000), (Infix (Left)))

# 57 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = (((- (1))), (Infix (NonAssoc)))

# 59 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = ((FStar_Util.max_int), (Infix (NonAssoc)))

# 60 "FStar.Extraction.ML.Code.fst"
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

# 69 "FStar.Extraction.ML.Code.fst"
let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (
# 73 "FStar.Extraction.ML.Code.fst"
let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(
# 76 "FStar.Extraction.ML.Code.fst"
let cg_libs = (FStar_Options.codegen_libs ())
in (
# 77 "FStar.Extraction.ML.Code.fst"
let ns_len = (FStar_List.length ns)
in (
# 78 "FStar.Extraction.ML.Code.fst"
let found = (FStar_Util.find_map cg_libs (fun cg_path -> (
# 79 "FStar.Extraction.ML.Code.fst"
let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(
# 81 "FStar.Extraction.ML.Code.fst"
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

# 88 "FStar.Extraction.ML.Code.fst"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
(([]), ("Some"))
end
| "Prims.None" -> begin
(([]), ("None"))
end
| _74_42 -> begin
(
# 95 "FStar.Extraction.ML.Code.fst"
let _74_45 = x
in (match (_74_45) with
| (ns, x) -> begin
(let _166_36 = (path_of_ns currentModule ns)
in ((_166_36), (x)))
end))
end))

# 96 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _166_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _166_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 101 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 107 "FStar.Extraction.ML.Code.fst"
let _74_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_74_51) with
| (p, s) -> begin
(let _166_46 = (let _166_45 = (let _166_44 = (ptsym_of_symbol s)
in (_166_44)::[])
in (FStar_List.append p _166_45))
in (FStar_String.concat "." _166_46))
end))
end)

# 108 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 112 "FStar.Extraction.ML.Code.fst"
let _74_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_74_56) with
| (p, s) -> begin
(
# 113 "FStar.Extraction.ML.Code.fst"
let s = if ((let _166_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _166_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 114 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = ((("op_Addition"), (e_bin_prio_op1), ("+")))::((("op_Subtraction"), (e_bin_prio_op1), ("-")))::((("op_Multiply"), (e_bin_prio_op1), ("*")))::((("op_Division"), (e_bin_prio_op1), ("/")))::((("op_Equality"), (e_bin_prio_eq), ("=")))::((("op_ColonEquals"), (e_bin_prio_eq), (":=")))::((("op_disEquality"), (e_bin_prio_eq), ("<>")))::((("op_AmpAmp"), (e_bin_prio_and), ("&&")))::((("op_BarBar"), (e_bin_prio_or), ("||")))::((("op_LessThanOrEqual"), (e_bin_prio_order), ("<=")))::((("op_GreaterThanOrEqual"), (e_bin_prio_order), (">=")))::((("op_LessThan"), (e_bin_prio_order), ("<")))::((("op_GreaterThan"), (e_bin_prio_order), (">")))::((("op_Modulus"), (e_bin_prio_order), ("mod")))::[]

# 132 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = ((("op_Negation"), ("not")))::((("op_Minus"), ("-")))::((("op_Bang"), ("Support.ST.read")))::[]

# 139 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 142 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = ((("Some"), ("Some")))::((("None"), ("None")))::((("Nil"), ("[]")))::((("Cons"), ("::")))::[]

# 150 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 154 "FStar.Extraction.ML.Code.fst"
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

# 161 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 165 "FStar.Extraction.ML.Code.fst"
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

# 172 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 176 "FStar.Extraction.ML.Code.fst"
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

# 183 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 187 "FStar.Extraction.ML.Code.fst"
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

# 194 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 198 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _74_95 inner doc -> (match (_74_95) with
| (outer, side) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 203 "FStar.Extraction.ML.Code.fst"
let _74_104 = _inner
in (match (_74_104) with
| (pi, fi) -> begin
(
# 204 "FStar.Extraction.ML.Code.fst"
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

# 217 "FStar.Extraction.ML.Code.fst"
let escape_byte_hex : FStar_BaseTypes.byte  ->  Prims.string = (fun x -> (Prims.strcat "\\x" (FStar_Util.hex_string_of_byte x)))

# 221 "FStar.Extraction.ML.Code.fst"
let escape_char_hex : FStar_BaseTypes.char  ->  Prims.string = (fun x -> (escape_byte_hex (FStar_Util.byte_of_char x)))

# 224 "FStar.Extraction.ML.Code.fst"
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

# 239 "FStar.Extraction.ML.Code.fst"
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

# 272 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 279 "FStar.Extraction.ML.Code.fst"
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
# 286 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (
# 287 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_119 = (let _166_118 = (FStar_Format.combine (FStar_Format.text " * ") doc)
in (FStar_Format.hbox _166_118))
in (FStar_Format.parens _166_119))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 291 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| (arg)::[] -> begin
(doc_of_mltype currentModule ((t_prio_name), (Left)) arg)
end
| _74_223 -> begin
(
# 296 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (let _166_121 = (let _166_120 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.hbox _166_120))
in (FStar_Format.parens _166_121)))
end)
in (
# 301 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _166_123 = (let _166_122 = (as_standard_type name)
in (FStar_Option.get _166_122))
in (Prims.snd _166_123))
end else begin
(ptsym currentModule name)
end
in (let _166_124 = (FStar_Format.reduce1 ((args)::((FStar_Format.text name))::[]))
in (FStar_Format.hbox _166_124))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _74_229, t2) -> begin
(
# 311 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule ((t_prio_fun), (Left)) t1)
in (
# 312 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule ((t_prio_fun), (Right)) t2)
in (let _166_126 = (let _166_125 = (FStar_Format.reduce1 ((d1)::((FStar_Format.text " -> "))::(d2)::[]))
in (FStar_Format.hbox _166_125))
in (maybe_paren outer t_prio_fun _166_126))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _166_130 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _166_130)))

# 321 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 327 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_151 = (FStar_Format.reduce (((FStar_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FStar_Format.parens _166_151))
end else begin
(let _166_152 = (FStar_Format.reduce (((FStar_Format.text "Obj.magic "))::((FStar_Format.parens doc))::[]))
in (FStar_Format.parens _166_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 333 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) es)
in (
# 334 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (FStar_Format.reduce ((d)::((FStar_Format.text ";"))::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _166_154 = (string_of_mlconstant c)
in (FStar_Format.text _166_154))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _74_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _166_155 = (ptsym currentModule path)
in (FStar_Format.text _166_155))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 347 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _74_269 -> (match (_74_269) with
| (name, e) -> begin
(
# 348 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _166_160 = (let _166_159 = (let _166_158 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _166_158))
in (_166_159)::((FStar_Format.text "="))::(doc)::[])
in (FStar_Format.reduce1 _166_160)))
end))
in (let _166_162 = (let _166_161 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _166_161))
in (FStar_Format.cbrackets _166_162)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 354 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _166_164 = (let _166_163 = (as_standard_constructor ctor)
in (FStar_Option.get _166_163))
in (Prims.snd _166_164))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 362 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _166_166 = (let _166_165 = (as_standard_constructor ctor)
in (FStar_Option.get _166_165))
in (Prims.snd _166_166))
end else begin
(ptctor currentModule ctor)
end
in (
# 367 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (
# 368 "FStar.Extraction.ML.Code.fst"
let doc = (match (((name), (args))) with
| ("::", (x)::(xs)::[]) -> begin
(FStar_Format.reduce (((FStar_Format.parens x))::((FStar_Format.text "::"))::(xs)::[]))
end
| (_74_288, _74_290) -> begin
(let _166_170 = (let _166_169 = (let _166_168 = (let _166_167 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _166_167))
in (_166_168)::[])
in ((FStar_Format.text name))::_166_169)
in (FStar_Format.reduce1 _166_170))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 376 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (let _166_172 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) x)
in (FStar_Format.parens _166_172))) es)
in (
# 377 "FStar.Extraction.ML.Code.fst"
let docs = (let _166_173 = (FStar_Format.combine (FStar_Format.text ", ") docs)
in (FStar_Format.parens _166_173))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 381 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _166_176 = (let _166_175 = (let _166_174 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_166_174)::[])
in (FStar_Format.hardline)::_166_175)
in (FStar_Format.reduce _166_176))
end else begin
FStar_Format.empty
end
in (
# 386 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule ((rec_), (false), (lets)))
in (
# 387 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (let _166_181 = (let _166_180 = (let _166_179 = (let _166_178 = (let _166_177 = (FStar_Format.reduce1 (((FStar_Format.text "in"))::(body)::[]))
in (_166_177)::[])
in (doc)::_166_178)
in (pre)::_166_179)
in (FStar_Format.combine FStar_Format.hardline _166_180))
in (FStar_Format.parens _166_181)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match (((e.FStar_Extraction_ML_Syntax.expr), (args))) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((_74_331)::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _74_329; FStar_Extraction_ML_Syntax.loc = _74_327})::({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (((arg, _74_319))::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _74_316; FStar_Extraction_ML_Syntax.loc = _74_314})::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(
# 396 "FStar.Extraction.ML.Code.fst"
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
# 419 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule ((e_app_prio), (ILeft)) e)
in (
# 420 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule ((e_app_prio), (IRight))) args)
in (let _166_182 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _166_182))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 425 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (
# 426 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.reduce ((e)::((FStar_Format.text "."))::((FStar_Format.text (Prims.snd f)))::[]))
end else begin
(let _166_187 = (let _166_186 = (let _166_185 = (let _166_184 = (let _166_183 = (ptsym currentModule f)
in (FStar_Format.text _166_183))
in (_166_184)::[])
in ((FStar_Format.text "."))::_166_185)
in (e)::_166_186)
in (FStar_Format.reduce _166_187))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 433 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _166_198 = (let _166_197 = (let _166_196 = (let _166_195 = (match (xt) with
| Some (xxt) -> begin
(let _166_194 = (let _166_193 = (let _166_192 = (doc_of_mltype currentModule outer xxt)
in (_166_192)::[])
in ((FStar_Format.text " : "))::_166_193)
in (FStar_Format.reduce1 _166_194))
end
| _74_416 -> begin
(FStar_Format.text "")
end)
in (_166_195)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text x))::_166_196)
in ((FStar_Format.text "("))::_166_197)
in (FStar_Format.reduce1 _166_198))
end else begin
(FStar_Format.text x)
end)
in (
# 439 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _74_422 -> (match (_74_422) with
| ((x, _74_419), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 440 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) body)
in (
# 441 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_202 = (let _166_201 = (let _166_200 = (FStar_Format.reduce1 ids)
in (_166_200)::((FStar_Format.text "->"))::(body)::[])
in ((FStar_Format.text "fun"))::_166_201)
in (FStar_Format.reduce1 _166_202))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 445 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (
# 446 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_206 = (let _166_205 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _166_204 = (let _166_203 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (_166_203)::((FStar_Format.text "end"))::[])
in (_166_205)::_166_204))
in (FStar_Format.combine FStar_Format.hardline _166_206))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 456 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (
# 457 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_214 = (let _166_213 = (FStar_Format.reduce1 (((FStar_Format.text "if"))::(cond)::((FStar_Format.text "then"))::((FStar_Format.text "begin"))::[]))
in (let _166_212 = (let _166_211 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (let _166_210 = (let _166_209 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::((FStar_Format.text "else"))::((FStar_Format.text "begin"))::[]))
in (let _166_208 = (let _166_207 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e2)
in (_166_207)::((FStar_Format.text "end"))::[])
in (_166_209)::_166_208))
in (_166_211)::_166_210))
in (_166_213)::_166_212))
in (FStar_Format.combine FStar_Format.hardline _166_214))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 469 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) cond)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 471 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_215 = (FStar_Format.reduce1 (((FStar_Format.text "match"))::((FStar_Format.parens cond))::((FStar_Format.text "with"))::[]))
in (_166_215)::pats)
in (
# 472 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _166_219 = (let _166_218 = (let _166_217 = (let _166_216 = (ptctor currentModule exn)
in (FStar_Format.text _166_216))
in (_166_217)::[])
in ((FStar_Format.text "raise"))::_166_218)
in (FStar_Format.reduce1 _166_219))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 480 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule ((min_op_prec), (NonAssoc))) args)
in (let _166_226 = (let _166_225 = (let _166_224 = (let _166_220 = (ptctor currentModule exn)
in (FStar_Format.text _166_220))
in (let _166_223 = (let _166_222 = (let _166_221 = (FStar_Format.combine (FStar_Format.text ", ") args)
in (FStar_Format.parens _166_221))
in (_166_222)::[])
in (_166_224)::_166_223))
in ((FStar_Format.text "raise"))::_166_225)
in (FStar_Format.reduce1 _166_226)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _166_233 = (let _166_232 = (let _166_231 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (let _166_230 = (let _166_229 = (let _166_228 = (let _166_227 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _166_227))
in (_166_228)::[])
in ((FStar_Format.text "with"))::_166_229)
in (_166_231)::_166_230))
in ((FStar_Format.text "try"))::_166_232)
in (FStar_Format.combine FStar_Format.hardline _166_233))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 491 "FStar.Extraction.ML.Code.fst"
let _74_470 = (let _166_238 = (as_bin_op p)
in (FStar_Option.get _166_238))
in (match (_74_470) with
| (_74_467, prio, txt) -> begin
(
# 492 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule ((prio), (Left)) e1)
in (
# 493 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule ((prio), (Right)) e2)
in (
# 494 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.reduce1 ((e1)::((FStar_Format.text txt))::(e2)::[]))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 498 "FStar.Extraction.ML.Code.fst"
let _74_480 = (let _166_242 = (as_uni_op p)
in (FStar_Option.get _166_242))
in (match (_74_480) with
| (_74_478, txt) -> begin
(
# 499 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e1)
in (
# 500 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.reduce1 (((FStar_Format.text txt))::((FStar_Format.parens e1))::[]))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _166_245 = (string_of_mlconstant c)
in (FStar_Format.text _166_245))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 510 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _74_497 -> (match (_74_497) with
| (name, p) -> begin
(let _166_253 = (let _166_252 = (let _166_248 = (ptsym currentModule ((path), (name)))
in (FStar_Format.text _166_248))
in (let _166_251 = (let _166_250 = (let _166_249 = (doc_of_pattern currentModule p)
in (_166_249)::[])
in ((FStar_Format.text "="))::_166_250)
in (_166_252)::_166_251))
in (FStar_Format.reduce1 _166_253))
end))
in (let _166_255 = (let _166_254 = (FStar_List.map for1 fields)
in (FStar_Format.combine (FStar_Format.text "; ") _166_254))
in (FStar_Format.cbrackets _166_255)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 514 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _166_257 = (let _166_256 = (as_standard_constructor ctor)
in (FStar_Option.get _166_256))
in (Prims.snd _166_257))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 522 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _166_259 = (let _166_258 = (as_standard_constructor ctor)
in (FStar_Option.get _166_258))
in (Prims.snd _166_259))
end else begin
(ptctor currentModule ctor)
end
in (
# 527 "FStar.Extraction.ML.Code.fst"
let doc = (match (((name), (pats))) with
| ("::", (x)::(xs)::[]) -> begin
(let _166_265 = (let _166_264 = (let _166_260 = (doc_of_pattern currentModule x)
in (FStar_Format.parens _166_260))
in (let _166_263 = (let _166_262 = (let _166_261 = (doc_of_pattern currentModule xs)
in (_166_261)::[])
in ((FStar_Format.text "::"))::_166_262)
in (_166_264)::_166_263))
in (FStar_Format.reduce _166_265))
end
| (_74_514, (FStar_Extraction_ML_Syntax.MLP_Tuple (_74_516))::[]) -> begin
(let _166_269 = (let _166_268 = (let _166_267 = (let _166_266 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _166_266))
in (_166_267)::[])
in ((FStar_Format.text name))::_166_268)
in (FStar_Format.reduce1 _166_269))
end
| _74_521 -> begin
(let _166_274 = (let _166_273 = (let _166_272 = (let _166_271 = (let _166_270 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine (FStar_Format.text ", ") _166_270))
in (FStar_Format.parens _166_271))
in (_166_272)::[])
in ((FStar_Format.text name))::_166_273)
in (FStar_Format.reduce1 _166_274))
end)
in (maybe_paren ((min_op_prec), (NonAssoc)) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 536 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _166_275 = (FStar_Format.combine (FStar_Format.text ", ") ps)
in (FStar_Format.parens _166_275)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 540 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 541 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (FStar_Format.combine (FStar_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _74_534 -> (match (_74_534) with
| (p, cond, e) -> begin
(
# 546 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _166_280 = (let _166_279 = (let _166_278 = (doc_of_pattern currentModule p)
in (_166_278)::[])
in ((FStar_Format.text "|"))::_166_279)
in (FStar_Format.reduce1 _166_280))
end
| Some (c) -> begin
(
# 550 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) c)
in (let _166_283 = (let _166_282 = (let _166_281 = (doc_of_pattern currentModule p)
in (_166_281)::((FStar_Format.text "when"))::(c)::[])
in ((FStar_Format.text "|"))::_166_282)
in (FStar_Format.reduce1 _166_283)))
end)
in (let _166_287 = (let _166_286 = (FStar_Format.reduce1 ((case)::((FStar_Format.text "->"))::((FStar_Format.text "begin"))::[]))
in (let _166_285 = (let _166_284 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_166_284)::((FStar_Format.text "end"))::[])
in (_166_286)::_166_285))
in (FStar_Format.combine FStar_Format.hardline _166_287)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (FStar_Extraction_ML_Syntax.mlletflavor * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _74_544 -> (match (_74_544) with
| (rec_, top_level, lets) -> begin
(
# 561 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _74_552 -> (match (_74_552) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _74_549; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 562 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (
# 563 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 567 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _74_558 -> (match (_74_558) with
| (x, _74_557) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 568 "FStar.Extraction.ML.Code.fst"
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
# 576 "FStar.Extraction.ML.Code.fst"
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
# 587 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text ":"))::(ty)::[])))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _166_295 = (let _166_294 = (let _166_293 = (FStar_Format.reduce1 ids)
in (_166_293)::(ty_annot)::((FStar_Format.text "="))::(e)::[])
in ((FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_166_294)
in (FStar_Format.reduce1 _166_295))))))
end))
in (
# 593 "FStar.Extraction.ML.Code.fst"
let letdoc = if (rec_ = FStar_Extraction_ML_Syntax.Rec) then begin
(FStar_Format.reduce1 (((FStar_Format.text "let"))::((FStar_Format.text "rec"))::[]))
end else begin
(FStar_Format.text "let")
end
in (
# 595 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 596 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (FStar_Format.reduce1 ((if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end)::(doc)::[]))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _74_598 -> (match (_74_598) with
| (lineno, file) -> begin
if ((FStar_Options.no_location_info ()) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 607 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (FStar_Format.reduce1 (((FStar_Format.text "#"))::((FStar_Format.num lineno))::((FStar_Format.text (Prims.strcat "\"" (Prims.strcat file "\""))))::[])))
end
end))

# 608 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 612 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _74_606 -> (match (_74_606) with
| (x, tparams, body) -> begin
(
# 613 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| (x)::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _74_611 -> begin
(
# 618 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _166_306 = (FStar_Format.combine (FStar_Format.text ", ") doc)
in (FStar_Format.parens _166_306)))
end)
in (
# 621 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 627 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _74_624 -> (match (_74_624) with
| (name, ty) -> begin
(
# 628 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 629 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 ((name)::((FStar_Format.text ":"))::(ty)::[]))))
end))
in (let _166_312 = (let _166_311 = (FStar_List.map forfield fields)
in (FStar_Format.combine (FStar_Format.text "; ") _166_311))
in (FStar_Format.cbrackets _166_312)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 636 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _74_632 -> (match (_74_632) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _74_635 -> begin
(
# 640 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule ((t_prio_tpl), (Left))) tys)
in (
# 641 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_Format.combine (FStar_Format.text " * ") tys)
in (FStar_Format.reduce1 (((FStar_Format.text name))::((FStar_Format.text "of"))::(tys)::[]))))
end)
end))
in (
# 645 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 646 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (FStar_Format.reduce1 (((FStar_Format.text "|"))::(d)::[]))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 651 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_319 = (let _166_318 = (let _166_317 = (let _166_316 = (ptsym currentModule (([]), (x)))
in (FStar_Format.text _166_316))
in (_166_317)::[])
in (tparams)::_166_318)
in (FStar_Format.reduce1 _166_319))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 656 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _166_321 = (let _166_320 = (FStar_Format.reduce1 ((doc)::((FStar_Format.text "="))::[]))
in (_166_320)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _166_321)))
end))))
end))
in (
# 661 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 662 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _166_324 = (let _166_323 = (let _166_322 = (FStar_Format.combine (FStar_Format.text " \n and ") doc)
in (_166_322)::[])
in ((FStar_Format.text "type"))::_166_323)
in (FStar_Format.reduce1 _166_324))
end else begin
(FStar_Format.text "")
end
in doc))))

# 663 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _166_336 = (let _166_335 = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::[]))
in (let _166_334 = (let _166_333 = (doc_of_sig currentModule subsig)
in (let _166_332 = (let _166_331 = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (_166_331)::[])
in (_166_333)::_166_332))
in (_166_335)::_166_334))
in (FStar_Format.combine FStar_Format.hardline _166_336))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 678 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (
# 679 "FStar.Extraction.ML.Code.fst"
let args = (let _166_337 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _166_337))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_74_666, ty)) -> begin
(
# 683 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule ((min_op_prec), (NonAssoc)) ty)
in (FStar_Format.reduce1 (((FStar_Format.text "val"))::((FStar_Format.text x))::((FStar_Format.text ": "))::(ty)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 691 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 692 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 693 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 703 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule ((min_op_prec), (NonAssoc))) args)
in (
# 704 "FStar.Extraction.ML.Code.fst"
let args = (let _166_345 = (FStar_Format.combine (FStar_Format.text " * ") args)
in (FStar_Format.parens _166_345))
in (FStar_Format.reduce1 (((FStar_Format.text "exception"))::((FStar_Format.text x))::((FStar_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule ((rec_), (true), (lets)))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _166_350 = (let _166_349 = (let _166_348 = (let _166_347 = (let _166_346 = (doc_of_expr currentModule ((min_op_prec), (NonAssoc)) e)
in (_166_346)::[])
in ((FStar_Format.text "="))::_166_347)
in ((FStar_Format.text "_"))::_166_348)
in ((FStar_Format.text "let"))::_166_349)
in (FStar_Format.reduce1 _166_350))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 720 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 724 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 725 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_74_706) -> begin
FStar_Format.empty
end
| _74_709 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 727 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _74_712 -> (match (_74_712) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 731 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _74_719 -> (match (_74_719) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 732 "FStar.Extraction.ML.Code.fst"
let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (
# 733 "FStar.Extraction.ML.Code.fst"
let head = (FStar_Format.reduce1 (((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text ":"))::((FStar_Format.text "sig"))::[]))
in (
# 734 "FStar.Extraction.ML.Code.fst"
let tail = (FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
in (
# 735 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _74_726 -> (match (_74_726) with
| (s, _74_725) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 736 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 737 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _166_367 = (let _166_366 = (let _166_365 = (let _166_364 = (FStar_Format.reduce sub)
in (_166_364)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_166_365)
in ((FStar_Format.cat head FStar_Format.hardline))::_166_366)
in (FStar_Format.reduce _166_367))))))))
end))
and for1_mod = (fun istop _74_739 -> (match (_74_739) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 748 "FStar.Extraction.ML.Code.fst"
let x = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (
# 749 "FStar.Extraction.ML.Code.fst"
let head = (let _166_370 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::[]
end else begin
if (not (istop)) then begin
((FStar_Format.text "module"))::((FStar_Format.text x))::((FStar_Format.text "="))::((FStar_Format.text "struct"))::[]
end else begin
[]
end
end
in (FStar_Format.reduce1 _166_370))
in (
# 754 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(FStar_Format.reduce1 (((FStar_Format.text "end"))::[]))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 757 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _74_746 -> (match (_74_746) with
| (_74_744, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 758 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 759 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 760 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FStar_Format.cat (FStar_Format.text "#light \"off\"") FStar_Format.hardline))::[]
end else begin
[]
end
in (let _166_380 = (let _166_379 = (let _166_378 = (let _166_377 = (let _166_376 = (let _166_375 = (let _166_374 = (let _166_373 = (FStar_Format.reduce sub)
in (_166_373)::((FStar_Format.cat tail FStar_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end))::_166_374)
in (FStar_Format.hardline)::_166_375)
in ((FStar_Format.text "open Prims"))::_166_376)
in (FStar_Format.hardline)::_166_377)
in (head)::_166_378)
in (FStar_List.append prefix _166_379))
in (FStar_All.pipe_left FStar_Format.reduce _166_380)))))))))
end))
in (
# 776 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _74_758 -> (match (_74_758) with
| (x, s, m) -> begin
(let _166_383 = (FStar_Extraction_ML_Util.flatten_mlpath x)
in (let _166_382 = (for1_mod true ((x), (s), (m)))
in ((_166_383), (_166_382))))
end)) mllib)
in docs))
end))

# 778 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 782 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 785 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_390 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _166_390 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty 0 doc)))

# 786 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 789 "FStar.Extraction.ML.Code.fst"
let doc = (let _166_395 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _166_395 ((min_op_prec), (NonAssoc)) e))
in (FStar_Format.pretty 0 doc)))





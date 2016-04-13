
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
| Infix (_73_4) -> begin
_73_4
end))

# 36 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 37 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 38 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 40 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 42 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 44 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 54 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 55 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 56 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 57 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 59 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 60 "FStar.Extraction.ML.Code.fst"
let rec in_ns = (fun x -> (match (x) with
| ([], _73_9) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_73_19, _73_21) -> begin
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
let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
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
let _73_32 = (FStar_Util.first_N cg_len ns)
in (match (_73_32) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _162_31 = (let _162_30 = (let _162_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_162_29)::[])
in (FStar_List.append pfx _162_30))
in Some (_162_31))
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
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _73_42 -> begin
(
# 95 "FStar.Extraction.ML.Code.fst"
let _73_45 = x
in (match (_73_45) with
| (ns, x) -> begin
(let _162_36 = (path_of_ns currentModule ns)
in (_162_36, x))
end))
end))

# 96 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _162_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _162_39)) <> (FStar_String.get s 0)) then begin
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
let _73_51 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_51) with
| (p, s) -> begin
(let _162_46 = (let _162_45 = (let _162_44 = (ptsym_of_symbol s)
in (_162_44)::[])
in (FStar_List.append p _162_45))
in (FStar_String.concat "." _162_46))
end))
end)

# 108 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 112 "FStar.Extraction.ML.Code.fst"
let _73_56 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_56) with
| (p, s) -> begin
(
# 113 "FStar.Extraction.ML.Code.fst"
let s = if ((let _162_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _162_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 114 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 132 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 139 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 142 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 150 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 154 "FStar.Extraction.ML.Code.fst"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _73_61 -> (match (_73_61) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_67 -> (match (_73_67) with
| (y, _73_64, _73_66) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 161 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 165 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_71 -> (match (_73_71) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_75 -> (match (_73_75) with
| (y, _73_74) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 172 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 176 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _73_79 -> (match (_73_79) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_83 -> (match (_73_83) with
| (y, _73_82) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 183 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 187 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _73_87 -> (match (_73_87) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_91 -> (match (_73_91) with
| (y, _73_90) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 194 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 198 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _73_95 inner doc -> (match (_73_95) with
| (outer, side) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 203 "FStar.Extraction.ML.Code.fst"
let _73_104 = _inner
in (match (_73_104) with
| (pi, fi) -> begin
(
# 204 "FStar.Extraction.ML.Code.fst"
let _73_107 = _outer
in (match (_73_107) with
| (po, fo) -> begin
((pi > po) || (match ((fi, side)) with
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
| (_73_131, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_73_135, _73_137) -> begin
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
let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _73_1 -> (match (_73_1) with
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
(let _162_101 = (let _162_100 = (escape_or escape_char_hex c)
in (Prims.strcat "\'" _162_100))
in (Prims.strcat _162_101 "\'"))
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
if (FStar_ST.read FStar_Options.use_native_int) then begin
s
end else begin
(Prims.strcat (Prims.strcat "(Prims.parse_int \"" s) "\")")
end
end
| FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(FStar_Util.string_of_float d)
end
| FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let _162_103 = (let _162_102 = (FStar_Bytes.f_encode escape_byte_hex bytes)
in (Prims.strcat "\"" _162_102))
in (Prims.strcat _162_103 "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let _162_105 = (let _162_104 = (FStar_String.collect (escape_or FStar_Util.string_of_char) chars)
in (Prims.strcat "\"" _162_104))
in (Prims.strcat _162_105 "\""))
end
| _73_203 -> begin
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
in (let _162_117 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _162_117)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 286 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 287 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_120 = (let _162_119 = (let _162_118 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_118 doc))
in (FStar_Format.hbox _162_119))
in (FStar_Format.parens _162_120))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 291 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _73_223 -> begin
(
# 296 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _162_123 = (let _162_122 = (let _162_121 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_121 args))
in (FStar_Format.hbox _162_122))
in (FStar_Format.parens _162_123)))
end)
in (
# 301 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _162_125 = (let _162_124 = (as_standard_type name)
in (FStar_Option.get _162_124))
in (Prims.snd _162_125))
end else begin
(ptsym currentModule name)
end
in (let _162_129 = (let _162_128 = (let _162_127 = (let _162_126 = (FStar_Format.text name)
in (_162_126)::[])
in (args)::_162_127)
in (FStar_Format.reduce1 _162_128))
in (FStar_Format.hbox _162_129))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_229, t2) -> begin
(
# 311 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 312 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _162_134 = (let _162_133 = (let _162_132 = (let _162_131 = (let _162_130 = (FStar_Format.text " -> ")
in (_162_130)::(d2)::[])
in (d1)::_162_131)
in (FStar_Format.reduce1 _162_132))
in (FStar_Format.hbox _162_133))
in (maybe_paren outer t_prio_fun _162_134))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _162_138 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _162_138)))

# 321 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 327 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_161 = (let _162_160 = (let _162_159 = (FStar_Format.text "Prims.checked_cast")
in (_162_159)::(doc)::[])
in (FStar_Format.reduce _162_160))
in (FStar_Format.parens _162_161))
end else begin
(let _162_166 = (let _162_165 = (let _162_164 = (FStar_Format.text "Obj.magic ")
in (let _162_163 = (let _162_162 = (FStar_Format.parens doc)
in (_162_162)::[])
in (_162_164)::_162_163))
in (FStar_Format.reduce _162_165))
in (FStar_Format.parens _162_166))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 333 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 334 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _162_170 = (let _162_169 = (let _162_168 = (FStar_Format.text ";")
in (_162_168)::(FStar_Format.hardline)::[])
in (d)::_162_169)
in (FStar_Format.reduce _162_170))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _162_171 = (string_of_mlconstant c)
in (FStar_Format.text _162_171))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_257) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _162_172 = (ptsym currentModule path)
in (FStar_Format.text _162_172))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 347 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_269 -> (match (_73_269) with
| (name, e) -> begin
(
# 348 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_179 = (let _162_178 = (let _162_175 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_175))
in (let _162_177 = (let _162_176 = (FStar_Format.text "=")
in (_162_176)::(doc)::[])
in (_162_178)::_162_177))
in (FStar_Format.reduce1 _162_179)))
end))
in (let _162_182 = (let _162_181 = (FStar_Format.text "; ")
in (let _162_180 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_181 _162_180)))
in (FStar_Format.cbrackets _162_182)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 354 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_184 = (let _162_183 = (as_standard_constructor ctor)
in (FStar_Option.get _162_183))
in (Prims.snd _162_184))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 362 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_186 = (let _162_185 = (as_standard_constructor ctor)
in (FStar_Option.get _162_185))
in (Prims.snd _162_186))
end else begin
(ptctor currentModule ctor)
end
in (
# 367 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 368 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _162_190 = (let _162_189 = (FStar_Format.parens x)
in (let _162_188 = (let _162_187 = (FStar_Format.text "::")
in (_162_187)::(xs)::[])
in (_162_189)::_162_188))
in (FStar_Format.reduce _162_190))
end
| (_73_288, _73_290) -> begin
(let _162_196 = (let _162_195 = (FStar_Format.text name)
in (let _162_194 = (let _162_193 = (let _162_192 = (let _162_191 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_191 args))
in (FStar_Format.parens _162_192))
in (_162_193)::[])
in (_162_195)::_162_194))
in (FStar_Format.reduce1 _162_196))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 376 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 377 "FStar.Extraction.ML.Code.fst"
let docs = (let _162_198 = (let _162_197 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_197 docs))
in (FStar_Format.parens _162_198))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 381 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _162_201 = (let _162_200 = (let _162_199 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_162_199)::[])
in (FStar_Format.hardline)::_162_200)
in (FStar_Format.reduce _162_201))
end else begin
FStar_Format.empty
end
in (
# 386 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 387 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _162_208 = (let _162_207 = (let _162_206 = (let _162_205 = (let _162_204 = (let _162_203 = (let _162_202 = (FStar_Format.text "in")
in (_162_202)::(body)::[])
in (FStar_Format.reduce1 _162_203))
in (_162_204)::[])
in (doc)::_162_205)
in (pre)::_162_206)
in (FStar_Format.combine FStar_Format.hardline _162_207))
in (FStar_Format.parens _162_208)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (_73_330::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _73_328; FStar_Extraction_ML_Syntax.loc = _73_326}::{FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((arg, _73_318)::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _73_315; FStar_Extraction_ML_Syntax.loc = _73_313}::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(
# 396 "FStar.Extraction.ML.Code.fst"
let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _73_345; FStar_Extraction_ML_Syntax.loc = _73_343}, branches); FStar_Extraction_ML_Syntax.mlty = _73_341; FStar_Extraction_ML_Syntax.loc = _73_339} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
branches
end
| e -> begin
((FStar_Extraction_ML_Syntax.MLP_Wild, None, e))::[]
end)
in (doc_of_expr currentModule outer {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Try ((scrutinee, branches)); FStar_Extraction_ML_Syntax.mlty = possible_match.FStar_Extraction_ML_Syntax.mlty; FStar_Extraction_ML_Syntax.loc = possible_match.FStar_Extraction_ML_Syntax.loc}))
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_364; FStar_Extraction_ML_Syntax.loc = _73_362}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _73_384; FStar_Extraction_ML_Syntax.loc = _73_382}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _73_396 -> begin
(
# 419 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 420 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _162_209 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _162_209))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 425 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 426 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_214 = (let _162_213 = (let _162_212 = (FStar_Format.text ".")
in (let _162_211 = (let _162_210 = (FStar_Format.text (Prims.snd f))
in (_162_210)::[])
in (_162_212)::_162_211))
in (e)::_162_213)
in (FStar_Format.reduce _162_214))
end else begin
(let _162_220 = (let _162_219 = (let _162_218 = (FStar_Format.text ".")
in (let _162_217 = (let _162_216 = (let _162_215 = (ptsym currentModule f)
in (FStar_Format.text _162_215))
in (_162_216)::[])
in (_162_218)::_162_217))
in (e)::_162_219)
in (FStar_Format.reduce _162_220))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 433 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_236 = (let _162_235 = (FStar_Format.text "(")
in (let _162_234 = (let _162_233 = (FStar_Format.text x)
in (let _162_232 = (let _162_231 = (match (xt) with
| Some (xxt) -> begin
(let _162_228 = (let _162_227 = (FStar_Format.text " : ")
in (let _162_226 = (let _162_225 = (doc_of_mltype currentModule outer xxt)
in (_162_225)::[])
in (_162_227)::_162_226))
in (FStar_Format.reduce1 _162_228))
end
| _73_415 -> begin
(FStar_Format.text "")
end)
in (let _162_230 = (let _162_229 = (FStar_Format.text ")")
in (_162_229)::[])
in (_162_231)::_162_230))
in (_162_233)::_162_232))
in (_162_235)::_162_234))
in (FStar_Format.reduce1 _162_236))
end else begin
(FStar_Format.text x)
end)
in (
# 439 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _73_421 -> (match (_73_421) with
| ((x, _73_418), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 440 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 441 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_243 = (let _162_242 = (FStar_Format.text "fun")
in (let _162_241 = (let _162_240 = (FStar_Format.reduce1 ids)
in (let _162_239 = (let _162_238 = (FStar_Format.text "->")
in (_162_238)::(body)::[])
in (_162_240)::_162_239))
in (_162_242)::_162_241))
in (FStar_Format.reduce1 _162_243))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 445 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 446 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_256 = (let _162_255 = (let _162_250 = (let _162_249 = (FStar_Format.text "if")
in (let _162_248 = (let _162_247 = (let _162_246 = (FStar_Format.text "then")
in (let _162_245 = (let _162_244 = (FStar_Format.text "begin")
in (_162_244)::[])
in (_162_246)::_162_245))
in (cond)::_162_247)
in (_162_249)::_162_248))
in (FStar_Format.reduce1 _162_250))
in (let _162_254 = (let _162_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_252 = (let _162_251 = (FStar_Format.text "end")
in (_162_251)::[])
in (_162_253)::_162_252))
in (_162_255)::_162_254))
in (FStar_Format.combine FStar_Format.hardline _162_256))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 456 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 457 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_279 = (let _162_278 = (let _162_263 = (let _162_262 = (FStar_Format.text "if")
in (let _162_261 = (let _162_260 = (let _162_259 = (FStar_Format.text "then")
in (let _162_258 = (let _162_257 = (FStar_Format.text "begin")
in (_162_257)::[])
in (_162_259)::_162_258))
in (cond)::_162_260)
in (_162_262)::_162_261))
in (FStar_Format.reduce1 _162_263))
in (let _162_277 = (let _162_276 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _162_275 = (let _162_274 = (let _162_269 = (let _162_268 = (FStar_Format.text "end")
in (let _162_267 = (let _162_266 = (FStar_Format.text "else")
in (let _162_265 = (let _162_264 = (FStar_Format.text "begin")
in (_162_264)::[])
in (_162_266)::_162_265))
in (_162_268)::_162_267))
in (FStar_Format.reduce1 _162_269))
in (let _162_273 = (let _162_272 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _162_271 = (let _162_270 = (FStar_Format.text "end")
in (_162_270)::[])
in (_162_272)::_162_271))
in (_162_274)::_162_273))
in (_162_276)::_162_275))
in (_162_278)::_162_277))
in (FStar_Format.combine FStar_Format.hardline _162_279))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 469 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 471 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_286 = (let _162_285 = (let _162_284 = (FStar_Format.text "match")
in (let _162_283 = (let _162_282 = (FStar_Format.parens cond)
in (let _162_281 = (let _162_280 = (FStar_Format.text "with")
in (_162_280)::[])
in (_162_282)::_162_281))
in (_162_284)::_162_283))
in (FStar_Format.reduce1 _162_285))
in (_162_286)::pats)
in (
# 472 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _162_291 = (let _162_290 = (FStar_Format.text "raise")
in (let _162_289 = (let _162_288 = (let _162_287 = (ptctor currentModule exn)
in (FStar_Format.text _162_287))
in (_162_288)::[])
in (_162_290)::_162_289))
in (FStar_Format.reduce1 _162_291))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 480 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _162_300 = (let _162_299 = (FStar_Format.text "raise")
in (let _162_298 = (let _162_297 = (let _162_292 = (ptctor currentModule exn)
in (FStar_Format.text _162_292))
in (let _162_296 = (let _162_295 = (let _162_294 = (let _162_293 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_293 args))
in (FStar_Format.parens _162_294))
in (_162_295)::[])
in (_162_297)::_162_296))
in (_162_299)::_162_298))
in (FStar_Format.reduce1 _162_300)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _162_309 = (let _162_308 = (FStar_Format.text "try")
in (let _162_307 = (let _162_306 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_305 = (let _162_304 = (FStar_Format.text "with")
in (let _162_303 = (let _162_302 = (let _162_301 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _162_301))
in (_162_302)::[])
in (_162_304)::_162_303))
in (_162_306)::_162_305))
in (_162_308)::_162_307))
in (FStar_Format.combine FStar_Format.hardline _162_309))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 491 "FStar.Extraction.ML.Code.fst"
let _73_469 = (let _162_314 = (as_bin_op p)
in (FStar_Option.get _162_314))
in (match (_73_469) with
| (_73_466, prio, txt) -> begin
(
# 492 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 493 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 494 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_317 = (let _162_316 = (let _162_315 = (FStar_Format.text txt)
in (_162_315)::(e2)::[])
in (e1)::_162_316)
in (FStar_Format.reduce1 _162_317))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 498 "FStar.Extraction.ML.Code.fst"
let _73_479 = (let _162_321 = (as_uni_op p)
in (FStar_Option.get _162_321))
in (match (_73_479) with
| (_73_477, txt) -> begin
(
# 499 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 500 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_325 = (let _162_324 = (FStar_Format.text txt)
in (let _162_323 = (let _162_322 = (FStar_Format.parens e1)
in (_162_322)::[])
in (_162_324)::_162_323))
in (FStar_Format.reduce1 _162_325))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _162_328 = (string_of_mlconstant c)
in (FStar_Format.text _162_328))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 510 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_496 -> (match (_73_496) with
| (name, p) -> begin
(let _162_337 = (let _162_336 = (let _162_331 = (ptsym currentModule (path, name))
in (FStar_Format.text _162_331))
in (let _162_335 = (let _162_334 = (FStar_Format.text "=")
in (let _162_333 = (let _162_332 = (doc_of_pattern currentModule p)
in (_162_332)::[])
in (_162_334)::_162_333))
in (_162_336)::_162_335))
in (FStar_Format.reduce1 _162_337))
end))
in (let _162_340 = (let _162_339 = (FStar_Format.text "; ")
in (let _162_338 = (FStar_List.map for1 fields)
in (FStar_Format.combine _162_339 _162_338)))
in (FStar_Format.cbrackets _162_340)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 514 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_342 = (let _162_341 = (as_standard_constructor ctor)
in (FStar_Option.get _162_341))
in (Prims.snd _162_342))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 522 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _162_344 = (let _162_343 = (as_standard_constructor ctor)
in (FStar_Option.get _162_343))
in (Prims.snd _162_344))
end else begin
(ptctor currentModule ctor)
end
in (
# 527 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _162_350 = (let _162_349 = (doc_of_pattern currentModule x)
in (let _162_348 = (let _162_347 = (FStar_Format.text "::")
in (let _162_346 = (let _162_345 = (doc_of_pattern currentModule xs)
in (_162_345)::[])
in (_162_347)::_162_346))
in (_162_349)::_162_348))
in (FStar_Format.reduce _162_350))
end
| (_73_513, FStar_Extraction_ML_Syntax.MLP_Tuple (_73_515)::[]) -> begin
(let _162_355 = (let _162_354 = (FStar_Format.text name)
in (let _162_353 = (let _162_352 = (let _162_351 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _162_351))
in (_162_352)::[])
in (_162_354)::_162_353))
in (FStar_Format.reduce1 _162_355))
end
| _73_520 -> begin
(let _162_362 = (let _162_361 = (FStar_Format.text name)
in (let _162_360 = (let _162_359 = (let _162_358 = (let _162_357 = (FStar_Format.text ", ")
in (let _162_356 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _162_357 _162_356)))
in (FStar_Format.parens _162_358))
in (_162_359)::[])
in (_162_361)::_162_360))
in (FStar_Format.reduce1 _162_362))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 536 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _162_364 = (let _162_363 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_363 ps))
in (FStar_Format.parens _162_364)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 540 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 541 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _162_365 = (FStar_Format.text " | ")
in (FStar_Format.combine _162_365 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _73_533 -> (match (_73_533) with
| (p, cond, e) -> begin
(
# 546 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _162_371 = (let _162_370 = (FStar_Format.text "|")
in (let _162_369 = (let _162_368 = (doc_of_pattern currentModule p)
in (_162_368)::[])
in (_162_370)::_162_369))
in (FStar_Format.reduce1 _162_371))
end
| Some (c) -> begin
(
# 550 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _162_377 = (let _162_376 = (FStar_Format.text "|")
in (let _162_375 = (let _162_374 = (doc_of_pattern currentModule p)
in (let _162_373 = (let _162_372 = (FStar_Format.text "when")
in (_162_372)::(c)::[])
in (_162_374)::_162_373))
in (_162_376)::_162_375))
in (FStar_Format.reduce1 _162_377)))
end)
in (let _162_388 = (let _162_387 = (let _162_382 = (let _162_381 = (let _162_380 = (FStar_Format.text "->")
in (let _162_379 = (let _162_378 = (FStar_Format.text "begin")
in (_162_378)::[])
in (_162_380)::_162_379))
in (case)::_162_381)
in (FStar_Format.reduce1 _162_382))
in (let _162_386 = (let _162_385 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _162_384 = (let _162_383 = (FStar_Format.text "end")
in (_162_383)::[])
in (_162_385)::_162_384))
in (_162_387)::_162_386))
in (FStar_Format.combine FStar_Format.hardline _162_388)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _73_543 -> (match (_73_543) with
| (rec_, top_level, lets) -> begin
(
# 561 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_551 -> (match (_73_551) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_548; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 562 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 563 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 567 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _73_557 -> (match (_73_557) with
| (x, _73_556) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 568 "FStar.Extraction.ML.Code.fst"
let ty_annot = if (not (pt)) then begin
(FStar_Format.text "")
end else begin
if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (Some (_::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 576 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_395 = (let _162_394 = (FStar_Format.text ":")
in (_162_394)::(ty)::[])
in (FStar_Format.reduce1 _162_395)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 587 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_397 = (let _162_396 = (FStar_Format.text ":")
in (_162_396)::(ty)::[])
in (FStar_Format.reduce1 _162_397)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _162_404 = (let _162_403 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _162_402 = (let _162_401 = (FStar_Format.reduce1 ids)
in (let _162_400 = (let _162_399 = (let _162_398 = (FStar_Format.text "=")
in (_162_398)::(e)::[])
in (ty_annot)::_162_399)
in (_162_401)::_162_400))
in (_162_403)::_162_402))
in (FStar_Format.reduce1 _162_404))))))
end))
in (
# 593 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _162_408 = (let _162_407 = (FStar_Format.text "let")
in (let _162_406 = (let _162_405 = (FStar_Format.text "rec")
in (_162_405)::[])
in (_162_407)::_162_406))
in (FStar_Format.reduce1 _162_408))
end else begin
(FStar_Format.text "let")
end
in (
# 595 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 596 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _162_412 = (let _162_411 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_162_411)::(doc)::[])
in (FStar_Format.reduce1 _162_412))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _73_597 -> (match (_73_597) with
| (lineno, file) -> begin
if ((FStar_ST.read FStar_Options.no_location_info) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 607 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _162_419 = (let _162_418 = (FStar_Format.text "#")
in (let _162_417 = (let _162_416 = (FStar_Format.num lineno)
in (let _162_415 = (let _162_414 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_162_414)::[])
in (_162_416)::_162_415))
in (_162_418)::_162_417))
in (FStar_Format.reduce1 _162_419)))
end
end))

# 608 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 612 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _73_605 -> (match (_73_605) with
| (x, tparams, body) -> begin
(
# 613 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _73_610 -> begin
(
# 618 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _162_428 = (let _162_427 = (FStar_Format.text ", ")
in (FStar_Format.combine _162_427 doc))
in (FStar_Format.parens _162_428)))
end)
in (
# 621 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 627 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _73_623 -> (match (_73_623) with
| (name, ty) -> begin
(
# 628 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 629 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_435 = (let _162_434 = (let _162_433 = (FStar_Format.text ":")
in (_162_433)::(ty)::[])
in (name)::_162_434)
in (FStar_Format.reduce1 _162_435))))
end))
in (let _162_438 = (let _162_437 = (FStar_Format.text "; ")
in (let _162_436 = (FStar_List.map forfield fields)
in (FStar_Format.combine _162_437 _162_436)))
in (FStar_Format.cbrackets _162_438)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 636 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _73_631 -> (match (_73_631) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _73_634 -> begin
(
# 640 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 641 "FStar.Extraction.ML.Code.fst"
let tys = (let _162_441 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_441 tys))
in (let _162_445 = (let _162_444 = (FStar_Format.text name)
in (let _162_443 = (let _162_442 = (FStar_Format.text "of")
in (_162_442)::(tys)::[])
in (_162_444)::_162_443))
in (FStar_Format.reduce1 _162_445))))
end)
end))
in (
# 645 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 646 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _162_448 = (let _162_447 = (FStar_Format.text "|")
in (_162_447)::(d)::[])
in (FStar_Format.reduce1 _162_448))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 651 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_452 = (let _162_451 = (let _162_450 = (let _162_449 = (ptsym currentModule ([], x))
in (FStar_Format.text _162_449))
in (_162_450)::[])
in (tparams)::_162_451)
in (FStar_Format.reduce1 _162_452))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 656 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _162_457 = (let _162_456 = (let _162_455 = (let _162_454 = (let _162_453 = (FStar_Format.text "=")
in (_162_453)::[])
in (doc)::_162_454)
in (FStar_Format.reduce1 _162_455))
in (_162_456)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _162_457)))
end))))
end))
in (
# 661 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 662 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _162_462 = (let _162_461 = (FStar_Format.text "type")
in (let _162_460 = (let _162_459 = (let _162_458 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _162_458 doc))
in (_162_459)::[])
in (_162_461)::_162_460))
in (FStar_Format.reduce1 _162_462))
end else begin
(FStar_Format.text "")
end
in doc))))

# 663 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _162_482 = (let _162_481 = (let _162_474 = (let _162_473 = (FStar_Format.text "module")
in (let _162_472 = (let _162_471 = (FStar_Format.text x)
in (let _162_470 = (let _162_469 = (FStar_Format.text "=")
in (_162_469)::[])
in (_162_471)::_162_470))
in (_162_473)::_162_472))
in (FStar_Format.reduce1 _162_474))
in (let _162_480 = (let _162_479 = (doc_of_sig currentModule subsig)
in (let _162_478 = (let _162_477 = (let _162_476 = (let _162_475 = (FStar_Format.text "end")
in (_162_475)::[])
in (FStar_Format.reduce1 _162_476))
in (_162_477)::[])
in (_162_479)::_162_478))
in (_162_481)::_162_480))
in (FStar_Format.combine FStar_Format.hardline _162_482))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _162_486 = (let _162_485 = (FStar_Format.text "exception")
in (let _162_484 = (let _162_483 = (FStar_Format.text x)
in (_162_483)::[])
in (_162_485)::_162_484))
in (FStar_Format.reduce1 _162_486))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 678 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 679 "FStar.Extraction.ML.Code.fst"
let args = (let _162_488 = (let _162_487 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_487 args))
in (FStar_Format.parens _162_488))
in (let _162_494 = (let _162_493 = (FStar_Format.text "exception")
in (let _162_492 = (let _162_491 = (FStar_Format.text x)
in (let _162_490 = (let _162_489 = (FStar_Format.text "of")
in (_162_489)::(args)::[])
in (_162_491)::_162_490))
in (_162_493)::_162_492))
in (FStar_Format.reduce1 _162_494))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_665, ty)) -> begin
(
# 683 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _162_500 = (let _162_499 = (FStar_Format.text "val")
in (let _162_498 = (let _162_497 = (FStar_Format.text x)
in (let _162_496 = (let _162_495 = (FStar_Format.text ": ")
in (_162_495)::(ty)::[])
in (_162_497)::_162_496))
in (_162_499)::_162_498))
in (FStar_Format.reduce1 _162_500)))
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
(let _162_511 = (let _162_510 = (FStar_Format.text "exception")
in (let _162_509 = (let _162_508 = (FStar_Format.text x)
in (_162_508)::[])
in (_162_510)::_162_509))
in (FStar_Format.reduce1 _162_511))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 703 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 704 "FStar.Extraction.ML.Code.fst"
let args = (let _162_513 = (let _162_512 = (FStar_Format.text " * ")
in (FStar_Format.combine _162_512 args))
in (FStar_Format.parens _162_513))
in (let _162_519 = (let _162_518 = (FStar_Format.text "exception")
in (let _162_517 = (let _162_516 = (FStar_Format.text x)
in (let _162_515 = (let _162_514 = (FStar_Format.text "of")
in (_162_514)::(args)::[])
in (_162_516)::_162_515))
in (_162_518)::_162_517))
in (FStar_Format.reduce1 _162_519))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _162_527 = (let _162_526 = (FStar_Format.text "let")
in (let _162_525 = (let _162_524 = (FStar_Format.text "_")
in (let _162_523 = (let _162_522 = (FStar_Format.text "=")
in (let _162_521 = (let _162_520 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_162_520)::[])
in (_162_522)::_162_521))
in (_162_524)::_162_523))
in (_162_526)::_162_525))
in (FStar_Format.reduce1 _162_527))
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
| FStar_Extraction_ML_Syntax.MLM_Loc (_73_705) -> begin
FStar_Format.empty
end
| _73_708 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 727 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _73_711 -> (match (_73_711) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 731 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _73_718 -> (match (_73_718) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 732 "FStar.Extraction.ML.Code.fst"
let head = (let _162_546 = (let _162_545 = (FStar_Format.text "module")
in (let _162_544 = (let _162_543 = (FStar_Format.text x)
in (let _162_542 = (let _162_541 = (FStar_Format.text ":")
in (let _162_540 = (let _162_539 = (FStar_Format.text "sig")
in (_162_539)::[])
in (_162_541)::_162_540))
in (_162_543)::_162_542))
in (_162_545)::_162_544))
in (FStar_Format.reduce1 _162_546))
in (
# 733 "FStar.Extraction.ML.Code.fst"
let tail = (let _162_548 = (let _162_547 = (FStar_Format.text "end")
in (_162_547)::[])
in (FStar_Format.reduce1 _162_548))
in (
# 734 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _73_724 -> (match (_73_724) with
| (s, _73_723) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 735 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 736 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _162_558 = (let _162_557 = (FStar_Format.cat head FStar_Format.hardline)
in (let _162_556 = (let _162_555 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_554 = (let _162_553 = (FStar_Format.reduce sub)
in (let _162_552 = (let _162_551 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_551)::[])
in (_162_553)::_162_552))
in (_162_555)::_162_554))
in (_162_557)::_162_556))
in (FStar_Format.reduce _162_558)))))))
end))
and for1_mod = (fun istop _73_737 -> (match (_73_737) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 747 "FStar.Extraction.ML.Code.fst"
let head = (let _162_571 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_563 = (FStar_Format.text "module")
in (let _162_562 = (let _162_561 = (FStar_Format.text x)
in (_162_561)::[])
in (_162_563)::_162_562))
end else begin
if (not (istop)) then begin
(let _162_570 = (FStar_Format.text "module")
in (let _162_569 = (let _162_568 = (FStar_Format.text x)
in (let _162_567 = (let _162_566 = (FStar_Format.text "=")
in (let _162_565 = (let _162_564 = (FStar_Format.text "struct")
in (_162_564)::[])
in (_162_566)::_162_565))
in (_162_568)::_162_567))
in (_162_570)::_162_569))
end else begin
[]
end
end
in (FStar_Format.reduce1 _162_571))
in (
# 752 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _162_573 = (let _162_572 = (FStar_Format.text "end")
in (_162_572)::[])
in (FStar_Format.reduce1 _162_573))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 755 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _73_743 -> (match (_73_743) with
| (_73_741, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 756 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 757 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 758 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _162_577 = (let _162_576 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _162_576 FStar_Format.hardline))
in (_162_577)::[])
end else begin
[]
end
in (let _162_589 = (let _162_588 = (let _162_587 = (let _162_586 = (let _162_585 = (FStar_Format.text "open Prims")
in (let _162_584 = (let _162_583 = (let _162_582 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _162_581 = (let _162_580 = (FStar_Format.reduce sub)
in (let _162_579 = (let _162_578 = (FStar_Format.cat tail FStar_Format.hardline)
in (_162_578)::[])
in (_162_580)::_162_579))
in (_162_582)::_162_581))
in (FStar_Format.hardline)::_162_583)
in (_162_585)::_162_584))
in (FStar_Format.hardline)::_162_586)
in (head)::_162_587)
in (FStar_List.append prefix _162_588))
in (FStar_All.pipe_left FStar_Format.reduce _162_589))))))))
end))
in (
# 774 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _73_755 -> (match (_73_755) with
| (x, s, m) -> begin
(let _162_591 = (for1_mod true (x, s, m))
in (x, _162_591))
end)) mllib)
in docs))
end))

# 775 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 779 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 782 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_598 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _162_598 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 783 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 786 "FStar.Extraction.ML.Code.fst"
let doc = (let _162_603 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _162_603 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





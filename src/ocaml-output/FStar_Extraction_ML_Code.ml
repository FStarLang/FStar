
open Prims
# 33 "FStar.Extraction.ML.Code.fst"
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 36 "FStar.Extraction.ML.Code.fst"
let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 36 "FStar.Extraction.ML.Code.fst"
type fixity =
| Prefix
| Postfix
| Infix of assoc

# 37 "FStar.Extraction.ML.Code.fst"
let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.Extraction.ML.Code.fst"
let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.Extraction.ML.Code.fst"
let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.Extraction.ML.Code.fst"
let ___Infix____0 : fixity  ->  assoc = (fun projectee -> (match (projectee) with
| Infix (_60_3) -> begin
_60_3
end))

# 37 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 38 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 39 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 42 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 43 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 54 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 55 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 56 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 57 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 58 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 60 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 61 "FStar.Extraction.ML.Code.fst"
let rec in_ns = (fun x -> (match (x) with
| ([], _60_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_60_18, _60_20) -> begin
false
end))

# 70 "FStar.Extraction.ML.Code.fst"
let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (
# 74 "FStar.Extraction.ML.Code.fst"
let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(
# 77 "FStar.Extraction.ML.Code.fst"
let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (
# 78 "FStar.Extraction.ML.Code.fst"
let ns_len = (FStar_List.length ns)
in (
# 79 "FStar.Extraction.ML.Code.fst"
let found = (FStar_Util.find_map cg_libs (fun cg_path -> (
# 80 "FStar.Extraction.ML.Code.fst"
let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(
# 82 "FStar.Extraction.ML.Code.fst"
let _60_31 = (FStar_Util.first_N cg_len ns)
in (match (_60_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _141_31 = (let _141_30 = (let _141_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_141_29)::[])
in (FStar_List.append pfx _141_30))
in Some (_141_31))
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

# 89 "FStar.Extraction.ML.Code.fst"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _60_41 -> begin
(
# 96 "FStar.Extraction.ML.Code.fst"
let _60_44 = x
in (match (_60_44) with
| (ns, x) -> begin
(let _141_36 = (path_of_ns currentModule ns)
in (_141_36, x))
end))
end))

# 97 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _141_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _141_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 102 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 108 "FStar.Extraction.ML.Code.fst"
let _60_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_50) with
| (p, s) -> begin
(let _141_46 = (let _141_45 = (let _141_44 = (ptsym_of_symbol s)
in (_141_44)::[])
in (FStar_List.append p _141_45))
in (FStar_String.concat "." _141_46))
end))
end)

# 109 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 113 "FStar.Extraction.ML.Code.fst"
let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(
# 114 "FStar.Extraction.ML.Code.fst"
let s = if ((let _141_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _141_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 115 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 133 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 140 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 143 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 151 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 155 "FStar.Extraction.ML.Code.fst"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _60_60 -> (match (_60_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_66 -> (match (_60_66) with
| (y, _60_63, _60_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 162 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 166 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _60_70 -> (match (_60_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_74 -> (match (_60_74) with
| (y, _60_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 173 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 177 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _60_78 -> (match (_60_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_82 -> (match (_60_82) with
| (y, _60_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 184 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 188 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _60_86 -> (match (_60_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _60_90 -> (match (_60_90) with
| (y, _60_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 195 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 199 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _60_94 inner doc -> (match (_60_94) with
| (outer, side) -> begin
(
# 203 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 204 "FStar.Extraction.ML.Code.fst"
let _60_103 = _inner
in (match (_60_103) with
| (pi, fi) -> begin
(
# 205 "FStar.Extraction.ML.Code.fst"
let _60_106 = _outer
in (match (_60_106) with
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
| (_60_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_60_134, _60_136) -> begin
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

# 218 "FStar.Extraction.ML.Code.fst"
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 222 "FStar.Extraction.ML.Code.fst"
let encode_char : Prims.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(
# 227 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.string_of_char c)
in (
# 228 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.unicode_of_string bytes)
in (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
end else begin
(match (c) with
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
| _60_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 243 "FStar.Extraction.ML.Code.fst"
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
(let _141_92 = (let _141_91 = (encode_char c)
in (Prims.strcat "\'" _141_91))
in (Prims.strcat _141_92 "\'"))
end
| FStar_Extraction_ML_Syntax.MLC_Byte (c) -> begin
(Prims.strcat (Prims.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| FStar_Extraction_ML_Syntax.MLC_Int32 (i) -> begin
(FStar_Util.string_of_int32 i)
end
| FStar_Extraction_ML_Syntax.MLC_Int64 (i) -> begin
(Prims.strcat (FStar_Util.string_of_int64 i) "L")
end
| FStar_Extraction_ML_Syntax.MLC_Int (s) -> begin
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
(
# 261 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(
# 265 "FStar.Extraction.ML.Code.fst"
let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

# 266 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 273 "FStar.Extraction.ML.Code.fst"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _141_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _141_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 280 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 281 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_107 = (let _141_106 = (let _141_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _141_105 doc))
in (FStar_Format.hbox _141_106))
in (FStar_Format.parens _141_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 285 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _60_198 -> begin
(
# 290 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _141_110 = (let _141_109 = (let _141_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_108 args))
in (FStar_Format.hbox _141_109))
in (FStar_Format.parens _141_110)))
end)
in (
# 295 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _141_112 = (let _141_111 = (as_standard_type name)
in (FStar_Option.get _141_111))
in (Prims.snd _141_112))
end else begin
(ptsym currentModule name)
end
in (let _141_116 = (let _141_115 = (let _141_114 = (let _141_113 = (FStar_Format.text name)
in (_141_113)::[])
in (args)::_141_114)
in (FStar_Format.reduce1 _141_115))
in (FStar_Format.hbox _141_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_204, t2) -> begin
(
# 305 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 306 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _141_121 = (let _141_120 = (let _141_119 = (let _141_118 = (let _141_117 = (FStar_Format.text " -> ")
in (_141_117)::(d2)::[])
in (d1)::_141_118)
in (FStar_Format.reduce1 _141_119))
in (FStar_Format.hbox _141_120))
in (maybe_paren outer t_prio_fun _141_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

# 315 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 321 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _141_147 = (let _141_146 = (let _141_145 = (FStar_Format.text "Prims.checked_cast")
in (_141_145)::(doc)::[])
in (FStar_Format.reduce _141_146))
in (FStar_Format.parens _141_147))
end else begin
(let _141_152 = (let _141_151 = (let _141_150 = (FStar_Format.text "Obj.magic ")
in (let _141_149 = (let _141_148 = (FStar_Format.parens doc)
in (_141_148)::[])
in (_141_150)::_141_149))
in (FStar_Format.reduce _141_151))
in (FStar_Format.parens _141_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 327 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 328 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _141_156 = (let _141_155 = (let _141_154 = (FStar_Format.text ";")
in (_141_154)::(FStar_Format.hardline)::[])
in (d)::_141_155)
in (FStar_Format.reduce _141_156))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _141_157 = (string_of_mlconstant c)
in (FStar_Format.text _141_157))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _141_158 = (ptsym currentModule path)
in (FStar_Format.text _141_158))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 341 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_244 -> (match (_60_244) with
| (name, e) -> begin
(
# 342 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _141_165 = (let _141_164 = (let _141_161 = (ptsym currentModule (path, name))
in (FStar_Format.text _141_161))
in (let _141_163 = (let _141_162 = (FStar_Format.text "=")
in (_141_162)::(doc)::[])
in (_141_164)::_141_163))
in (FStar_Format.reduce1 _141_165)))
end))
in (let _141_168 = (let _141_167 = (FStar_Format.text "; ")
in (let _141_166 = (FStar_List.map for1 fields)
in (FStar_Format.combine _141_167 _141_166)))
in (FStar_Format.cbrackets _141_168)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 348 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _141_170 = (let _141_169 = (as_standard_constructor ctor)
in (FStar_Option.get _141_169))
in (Prims.snd _141_170))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 356 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _141_172 = (let _141_171 = (as_standard_constructor ctor)
in (FStar_Option.get _141_171))
in (Prims.snd _141_172))
end else begin
(ptctor currentModule ctor)
end
in (
# 361 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 362 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _141_176 = (let _141_175 = (FStar_Format.parens x)
in (let _141_174 = (let _141_173 = (FStar_Format.text "::")
in (_141_173)::(xs)::[])
in (_141_175)::_141_174))
in (FStar_Format.reduce _141_176))
end
| (_60_263, _60_265) -> begin
(let _141_182 = (let _141_181 = (FStar_Format.text name)
in (let _141_180 = (let _141_179 = (let _141_178 = (let _141_177 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_177 args))
in (FStar_Format.parens _141_178))
in (_141_179)::[])
in (_141_181)::_141_180))
in (FStar_Format.reduce1 _141_182))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 370 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 371 "FStar.Extraction.ML.Code.fst"
let docs = (let _141_184 = (let _141_183 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_183 docs))
in (FStar_Format.parens _141_184))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 375 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _141_187 = (let _141_186 = (let _141_185 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_141_185)::[])
in (FStar_Format.hardline)::_141_186)
in (FStar_Format.reduce _141_187))
end else begin
FStar_Format.empty
end
in (
# 380 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 381 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _141_194 = (let _141_193 = (let _141_192 = (let _141_191 = (let _141_190 = (let _141_189 = (let _141_188 = (FStar_Format.text "in")
in (_141_188)::(body)::[])
in (FStar_Format.reduce1 _141_189))
in (_141_190)::[])
in (doc)::_141_191)
in (pre)::_141_192)
in (FStar_Format.combine FStar_Format.hardline _141_193))
in (FStar_Format.parens _141_194)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _60_294; FStar_Extraction_ML_Syntax.loc = _60_292}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _60_314; FStar_Extraction_ML_Syntax.loc = _60_312}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _60_326 -> begin
(
# 396 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 397 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _141_195 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _141_195))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 402 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 403 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _141_200 = (let _141_199 = (let _141_198 = (FStar_Format.text ".")
in (let _141_197 = (let _141_196 = (FStar_Format.text (Prims.snd f))
in (_141_196)::[])
in (_141_198)::_141_197))
in (e)::_141_199)
in (FStar_Format.reduce _141_200))
end else begin
(let _141_206 = (let _141_205 = (let _141_204 = (FStar_Format.text ".")
in (let _141_203 = (let _141_202 = (let _141_201 = (ptsym currentModule f)
in (FStar_Format.text _141_201))
in (_141_202)::[])
in (_141_204)::_141_203))
in (e)::_141_205)
in (FStar_Format.reduce _141_206))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 410 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _141_222 = (let _141_221 = (FStar_Format.text "(")
in (let _141_220 = (let _141_219 = (FStar_Format.text x)
in (let _141_218 = (let _141_217 = (match (xt) with
| Some (xxt) -> begin
(let _141_214 = (let _141_213 = (FStar_Format.text " : ")
in (let _141_212 = (let _141_211 = (doc_of_mltype currentModule outer xxt)
in (_141_211)::[])
in (_141_213)::_141_212))
in (FStar_Format.reduce1 _141_214))
end
| _60_345 -> begin
(FStar_Format.text "")
end)
in (let _141_216 = (let _141_215 = (FStar_Format.text ")")
in (_141_215)::[])
in (_141_217)::_141_216))
in (_141_219)::_141_218))
in (_141_221)::_141_220))
in (FStar_Format.reduce1 _141_222))
end else begin
(FStar_Format.text x)
end)
in (
# 416 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _60_351 -> (match (_60_351) with
| ((x, _60_348), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 417 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 418 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_229 = (let _141_228 = (FStar_Format.text "fun")
in (let _141_227 = (let _141_226 = (FStar_Format.reduce1 ids)
in (let _141_225 = (let _141_224 = (FStar_Format.text "->")
in (_141_224)::(body)::[])
in (_141_226)::_141_225))
in (_141_228)::_141_227))
in (FStar_Format.reduce1 _141_229))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 422 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 423 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_242 = (let _141_241 = (let _141_236 = (let _141_235 = (FStar_Format.text "if")
in (let _141_234 = (let _141_233 = (let _141_232 = (FStar_Format.text "then")
in (let _141_231 = (let _141_230 = (FStar_Format.text "begin")
in (_141_230)::[])
in (_141_232)::_141_231))
in (cond)::_141_233)
in (_141_235)::_141_234))
in (FStar_Format.reduce1 _141_236))
in (let _141_240 = (let _141_239 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _141_238 = (let _141_237 = (FStar_Format.text "end")
in (_141_237)::[])
in (_141_239)::_141_238))
in (_141_241)::_141_240))
in (FStar_Format.combine FStar_Format.hardline _141_242))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 433 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 434 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_265 = (let _141_264 = (let _141_249 = (let _141_248 = (FStar_Format.text "if")
in (let _141_247 = (let _141_246 = (let _141_245 = (FStar_Format.text "then")
in (let _141_244 = (let _141_243 = (FStar_Format.text "begin")
in (_141_243)::[])
in (_141_245)::_141_244))
in (cond)::_141_246)
in (_141_248)::_141_247))
in (FStar_Format.reduce1 _141_249))
in (let _141_263 = (let _141_262 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _141_261 = (let _141_260 = (let _141_255 = (let _141_254 = (FStar_Format.text "end")
in (let _141_253 = (let _141_252 = (FStar_Format.text "else")
in (let _141_251 = (let _141_250 = (FStar_Format.text "begin")
in (_141_250)::[])
in (_141_252)::_141_251))
in (_141_254)::_141_253))
in (FStar_Format.reduce1 _141_255))
in (let _141_259 = (let _141_258 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _141_257 = (let _141_256 = (FStar_Format.text "end")
in (_141_256)::[])
in (_141_258)::_141_257))
in (_141_260)::_141_259))
in (_141_262)::_141_261))
in (_141_264)::_141_263))
in (FStar_Format.combine FStar_Format.hardline _141_265))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 446 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 447 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 448 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_272 = (let _141_271 = (let _141_270 = (FStar_Format.text "match")
in (let _141_269 = (let _141_268 = (FStar_Format.parens cond)
in (let _141_267 = (let _141_266 = (FStar_Format.text "with")
in (_141_266)::[])
in (_141_268)::_141_267))
in (_141_270)::_141_269))
in (FStar_Format.reduce1 _141_271))
in (_141_272)::pats)
in (
# 449 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _141_277 = (let _141_276 = (FStar_Format.text "raise")
in (let _141_275 = (let _141_274 = (let _141_273 = (ptctor currentModule exn)
in (FStar_Format.text _141_273))
in (_141_274)::[])
in (_141_276)::_141_275))
in (FStar_Format.reduce1 _141_277))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 457 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _141_286 = (let _141_285 = (FStar_Format.text "raise")
in (let _141_284 = (let _141_283 = (let _141_278 = (ptctor currentModule exn)
in (FStar_Format.text _141_278))
in (let _141_282 = (let _141_281 = (let _141_280 = (let _141_279 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_279 args))
in (FStar_Format.parens _141_280))
in (_141_281)::[])
in (_141_283)::_141_282))
in (_141_285)::_141_284))
in (FStar_Format.reduce1 _141_286)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _141_303 = (let _141_302 = (let _141_290 = (let _141_289 = (FStar_Format.text "try")
in (let _141_288 = (let _141_287 = (FStar_Format.text "begin")
in (_141_287)::[])
in (_141_289)::_141_288))
in (FStar_Format.reduce1 _141_290))
in (let _141_301 = (let _141_300 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _141_299 = (let _141_298 = (let _141_294 = (let _141_293 = (FStar_Format.text "end")
in (let _141_292 = (let _141_291 = (FStar_Format.text "with")
in (_141_291)::[])
in (_141_293)::_141_292))
in (FStar_Format.reduce1 _141_294))
in (let _141_297 = (let _141_296 = (let _141_295 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _141_295))
in (_141_296)::[])
in (_141_298)::_141_297))
in (_141_300)::_141_299))
in (_141_302)::_141_301))
in (FStar_Format.combine FStar_Format.hardline _141_303))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 468 "FStar.Extraction.ML.Code.fst"
let _60_399 = (let _141_308 = (as_bin_op p)
in (FStar_Option.get _141_308))
in (match (_60_399) with
| (_60_396, prio, txt) -> begin
(
# 469 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 471 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_311 = (let _141_310 = (let _141_309 = (FStar_Format.text txt)
in (_141_309)::(e2)::[])
in (e1)::_141_310)
in (FStar_Format.reduce1 _141_311))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 475 "FStar.Extraction.ML.Code.fst"
let _60_409 = (let _141_315 = (as_uni_op p)
in (FStar_Option.get _141_315))
in (match (_60_409) with
| (_60_407, txt) -> begin
(
# 476 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 477 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_319 = (let _141_318 = (FStar_Format.text txt)
in (let _141_317 = (let _141_316 = (FStar_Format.parens e1)
in (_141_316)::[])
in (_141_318)::_141_317))
in (FStar_Format.reduce1 _141_319))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _141_322 = (string_of_mlconstant c)
in (FStar_Format.text _141_322))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 487 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_426 -> (match (_60_426) with
| (name, p) -> begin
(let _141_331 = (let _141_330 = (let _141_325 = (ptsym currentModule (path, name))
in (FStar_Format.text _141_325))
in (let _141_329 = (let _141_328 = (FStar_Format.text "=")
in (let _141_327 = (let _141_326 = (doc_of_pattern currentModule p)
in (_141_326)::[])
in (_141_328)::_141_327))
in (_141_330)::_141_329))
in (FStar_Format.reduce1 _141_331))
end))
in (let _141_334 = (let _141_333 = (FStar_Format.text "; ")
in (let _141_332 = (FStar_List.map for1 fields)
in (FStar_Format.combine _141_333 _141_332)))
in (FStar_Format.cbrackets _141_334)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 491 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _141_336 = (let _141_335 = (as_standard_constructor ctor)
in (FStar_Option.get _141_335))
in (Prims.snd _141_336))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 499 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _141_338 = (let _141_337 = (as_standard_constructor ctor)
in (FStar_Option.get _141_337))
in (Prims.snd _141_338))
end else begin
(ptctor currentModule ctor)
end
in (
# 504 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _141_344 = (let _141_343 = (doc_of_pattern currentModule x)
in (let _141_342 = (let _141_341 = (FStar_Format.text "::")
in (let _141_340 = (let _141_339 = (doc_of_pattern currentModule xs)
in (_141_339)::[])
in (_141_341)::_141_340))
in (_141_343)::_141_342))
in (FStar_Format.reduce _141_344))
end
| (_60_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_445)::[]) -> begin
(let _141_349 = (let _141_348 = (FStar_Format.text name)
in (let _141_347 = (let _141_346 = (let _141_345 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _141_345))
in (_141_346)::[])
in (_141_348)::_141_347))
in (FStar_Format.reduce1 _141_349))
end
| _60_450 -> begin
(let _141_356 = (let _141_355 = (FStar_Format.text name)
in (let _141_354 = (let _141_353 = (let _141_352 = (let _141_351 = (FStar_Format.text ", ")
in (let _141_350 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _141_351 _141_350)))
in (FStar_Format.parens _141_352))
in (_141_353)::[])
in (_141_355)::_141_354))
in (FStar_Format.reduce1 _141_356))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 513 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _141_358 = (let _141_357 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_357 ps))
in (FStar_Format.parens _141_358)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 517 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 518 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _141_359 = (FStar_Format.text " | ")
in (FStar_Format.combine _141_359 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _60_463 -> (match (_60_463) with
| (p, cond, e) -> begin
(
# 523 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _141_365 = (let _141_364 = (FStar_Format.text "|")
in (let _141_363 = (let _141_362 = (doc_of_pattern currentModule p)
in (_141_362)::[])
in (_141_364)::_141_363))
in (FStar_Format.reduce1 _141_365))
end
| Some (c) -> begin
(
# 527 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _141_371 = (let _141_370 = (FStar_Format.text "|")
in (let _141_369 = (let _141_368 = (doc_of_pattern currentModule p)
in (let _141_367 = (let _141_366 = (FStar_Format.text "when")
in (_141_366)::(c)::[])
in (_141_368)::_141_367))
in (_141_370)::_141_369))
in (FStar_Format.reduce1 _141_371)))
end)
in (let _141_382 = (let _141_381 = (let _141_376 = (let _141_375 = (let _141_374 = (FStar_Format.text "->")
in (let _141_373 = (let _141_372 = (FStar_Format.text "begin")
in (_141_372)::[])
in (_141_374)::_141_373))
in (case)::_141_375)
in (FStar_Format.reduce1 _141_376))
in (let _141_380 = (let _141_379 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _141_378 = (let _141_377 = (FStar_Format.text "end")
in (_141_377)::[])
in (_141_379)::_141_378))
in (_141_381)::_141_380))
in (FStar_Format.combine FStar_Format.hardline _141_382)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _60_473 -> (match (_60_473) with
| (rec_, top_level, lets) -> begin
(
# 538 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_480 -> (match (_60_480) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _60_477; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(
# 539 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 540 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 544 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _60_486 -> (match (_60_486) with
| (x, _60_485) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 545 "FStar.Extraction.ML.Code.fst"
let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (Some (_::_, _)) | (None) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 551 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _141_389 = (let _141_388 = (FStar_Format.text ":")
in (_141_388)::(ty)::[])
in (FStar_Format.reduce1 _141_389)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 562 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _141_391 = (let _141_390 = (FStar_Format.text ":")
in (_141_390)::(ty)::[])
in (FStar_Format.reduce1 _141_391)))
end)
end else begin
(FStar_Format.text "")
end
end
in (let _141_398 = (let _141_397 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _141_396 = (let _141_395 = (FStar_Format.reduce1 ids)
in (let _141_394 = (let _141_393 = (let _141_392 = (FStar_Format.text "=")
in (_141_392)::(e)::[])
in (ty_annot)::_141_393)
in (_141_395)::_141_394))
in (_141_397)::_141_396))
in (FStar_Format.reduce1 _141_398))))))
end))
in (
# 568 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _141_402 = (let _141_401 = (FStar_Format.text "let")
in (let _141_400 = (let _141_399 = (FStar_Format.text "rec")
in (_141_399)::[])
in (_141_401)::_141_400))
in (FStar_Format.reduce1 _141_402))
end else begin
(FStar_Format.text "let")
end
in (
# 570 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 571 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _141_406 = (let _141_405 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_141_405)::(doc)::[])
in (FStar_Format.reduce1 _141_406))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _60_526 -> (match (_60_526) with
| (lineno, file) -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FStar_Format.empty
end else begin
(
# 582 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _141_413 = (let _141_412 = (FStar_Format.text "#")
in (let _141_411 = (let _141_410 = (FStar_Format.num lineno)
in (let _141_409 = (let _141_408 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_141_408)::[])
in (_141_410)::_141_409))
in (_141_412)::_141_411))
in (FStar_Format.reduce1 _141_413)))
end
end))

# 583 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 587 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_534 -> (match (_60_534) with
| (x, tparams, body) -> begin
(
# 588 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_539 -> begin
(
# 593 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _141_422 = (let _141_421 = (FStar_Format.text ", ")
in (FStar_Format.combine _141_421 doc))
in (FStar_Format.parens _141_422)))
end)
in (
# 596 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 602 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _60_552 -> (match (_60_552) with
| (name, ty) -> begin
(
# 603 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 604 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _141_429 = (let _141_428 = (let _141_427 = (FStar_Format.text ":")
in (_141_427)::(ty)::[])
in (name)::_141_428)
in (FStar_Format.reduce1 _141_429))))
end))
in (let _141_432 = (let _141_431 = (FStar_Format.text "; ")
in (let _141_430 = (FStar_List.map forfield fields)
in (FStar_Format.combine _141_431 _141_430)))
in (FStar_Format.cbrackets _141_432)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 611 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _60_560 -> (match (_60_560) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _60_563 -> begin
(
# 615 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 616 "FStar.Extraction.ML.Code.fst"
let tys = (let _141_435 = (FStar_Format.text " * ")
in (FStar_Format.combine _141_435 tys))
in (let _141_439 = (let _141_438 = (FStar_Format.text name)
in (let _141_437 = (let _141_436 = (FStar_Format.text "of")
in (_141_436)::(tys)::[])
in (_141_438)::_141_437))
in (FStar_Format.reduce1 _141_439))))
end)
end))
in (
# 620 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 621 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _141_442 = (let _141_441 = (FStar_Format.text "|")
in (_141_441)::(d)::[])
in (FStar_Format.reduce1 _141_442))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 626 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_446 = (let _141_445 = (let _141_444 = (let _141_443 = (ptsym currentModule ([], x))
in (FStar_Format.text _141_443))
in (_141_444)::[])
in (tparams)::_141_445)
in (FStar_Format.reduce1 _141_446))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 631 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _141_451 = (let _141_450 = (let _141_449 = (let _141_448 = (let _141_447 = (FStar_Format.text "=")
in (_141_447)::[])
in (doc)::_141_448)
in (FStar_Format.reduce1 _141_449))
in (_141_450)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _141_451)))
end))))
end))
in (
# 636 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 637 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _141_456 = (let _141_455 = (FStar_Format.text "type")
in (let _141_454 = (let _141_453 = (let _141_452 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _141_452 doc))
in (_141_453)::[])
in (_141_455)::_141_454))
in (FStar_Format.reduce1 _141_456))
end else begin
(FStar_Format.text "")
end
in doc))))

# 638 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _141_476 = (let _141_475 = (let _141_468 = (let _141_467 = (FStar_Format.text "module")
in (let _141_466 = (let _141_465 = (FStar_Format.text x)
in (let _141_464 = (let _141_463 = (FStar_Format.text "=")
in (_141_463)::[])
in (_141_465)::_141_464))
in (_141_467)::_141_466))
in (FStar_Format.reduce1 _141_468))
in (let _141_474 = (let _141_473 = (doc_of_sig currentModule subsig)
in (let _141_472 = (let _141_471 = (let _141_470 = (let _141_469 = (FStar_Format.text "end")
in (_141_469)::[])
in (FStar_Format.reduce1 _141_470))
in (_141_471)::[])
in (_141_473)::_141_472))
in (_141_475)::_141_474))
in (FStar_Format.combine FStar_Format.hardline _141_476))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _141_480 = (let _141_479 = (FStar_Format.text "exception")
in (let _141_478 = (let _141_477 = (FStar_Format.text x)
in (_141_477)::[])
in (_141_479)::_141_478))
in (FStar_Format.reduce1 _141_480))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 653 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 654 "FStar.Extraction.ML.Code.fst"
let args = (let _141_482 = (let _141_481 = (FStar_Format.text " * ")
in (FStar_Format.combine _141_481 args))
in (FStar_Format.parens _141_482))
in (let _141_488 = (let _141_487 = (FStar_Format.text "exception")
in (let _141_486 = (let _141_485 = (FStar_Format.text x)
in (let _141_484 = (let _141_483 = (FStar_Format.text "of")
in (_141_483)::(args)::[])
in (_141_485)::_141_484))
in (_141_487)::_141_486))
in (FStar_Format.reduce1 _141_488))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_594, ty)) -> begin
(
# 658 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _141_494 = (let _141_493 = (FStar_Format.text "val")
in (let _141_492 = (let _141_491 = (FStar_Format.text x)
in (let _141_490 = (let _141_489 = (FStar_Format.text ": ")
in (_141_489)::(ty)::[])
in (_141_491)::_141_490))
in (_141_493)::_141_492))
in (FStar_Format.reduce1 _141_494)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 666 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 667 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 668 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _141_505 = (let _141_504 = (FStar_Format.text "exception")
in (let _141_503 = (let _141_502 = (FStar_Format.text x)
in (_141_502)::[])
in (_141_504)::_141_503))
in (FStar_Format.reduce1 _141_505))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 678 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 679 "FStar.Extraction.ML.Code.fst"
let args = (let _141_507 = (let _141_506 = (FStar_Format.text " * ")
in (FStar_Format.combine _141_506 args))
in (FStar_Format.parens _141_507))
in (let _141_513 = (let _141_512 = (FStar_Format.text "exception")
in (let _141_511 = (let _141_510 = (FStar_Format.text x)
in (let _141_509 = (let _141_508 = (FStar_Format.text "of")
in (_141_508)::(args)::[])
in (_141_510)::_141_509))
in (_141_512)::_141_511))
in (FStar_Format.reduce1 _141_513))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _141_521 = (let _141_520 = (FStar_Format.text "let")
in (let _141_519 = (let _141_518 = (FStar_Format.text "_")
in (let _141_517 = (let _141_516 = (FStar_Format.text "=")
in (let _141_515 = (let _141_514 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_141_514)::[])
in (_141_516)::_141_515))
in (_141_518)::_141_517))
in (_141_520)::_141_519))
in (FStar_Format.reduce1 _141_521))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 695 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 699 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 700 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_60_634) -> begin
FStar_Format.empty
end
| _60_637 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 702 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _60_640 -> (match (_60_640) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 706 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _60_647 -> (match (_60_647) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 707 "FStar.Extraction.ML.Code.fst"
let head = (let _141_540 = (let _141_539 = (FStar_Format.text "module")
in (let _141_538 = (let _141_537 = (FStar_Format.text x)
in (let _141_536 = (let _141_535 = (FStar_Format.text ":")
in (let _141_534 = (let _141_533 = (FStar_Format.text "sig")
in (_141_533)::[])
in (_141_535)::_141_534))
in (_141_537)::_141_536))
in (_141_539)::_141_538))
in (FStar_Format.reduce1 _141_540))
in (
# 708 "FStar.Extraction.ML.Code.fst"
let tail = (let _141_542 = (let _141_541 = (FStar_Format.text "end")
in (_141_541)::[])
in (FStar_Format.reduce1 _141_542))
in (
# 709 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _60_653 -> (match (_60_653) with
| (s, _60_652) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 710 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 711 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _141_552 = (let _141_551 = (FStar_Format.cat head FStar_Format.hardline)
in (let _141_550 = (let _141_549 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _141_548 = (let _141_547 = (FStar_Format.reduce sub)
in (let _141_546 = (let _141_545 = (FStar_Format.cat tail FStar_Format.hardline)
in (_141_545)::[])
in (_141_547)::_141_546))
in (_141_549)::_141_548))
in (_141_551)::_141_550))
in (FStar_Format.reduce _141_552)))))))
end))
and for1_mod = (fun istop _60_666 -> (match (_60_666) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 722 "FStar.Extraction.ML.Code.fst"
let head = (let _141_565 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _141_557 = (FStar_Format.text "module")
in (let _141_556 = (let _141_555 = (FStar_Format.text x)
in (_141_555)::[])
in (_141_557)::_141_556))
end else begin
if (not (istop)) then begin
(let _141_564 = (FStar_Format.text "module")
in (let _141_563 = (let _141_562 = (FStar_Format.text x)
in (let _141_561 = (let _141_560 = (FStar_Format.text "=")
in (let _141_559 = (let _141_558 = (FStar_Format.text "struct")
in (_141_558)::[])
in (_141_560)::_141_559))
in (_141_562)::_141_561))
in (_141_564)::_141_563))
end else begin
[]
end
end
in (FStar_Format.reduce1 _141_565))
in (
# 727 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _141_567 = (let _141_566 = (FStar_Format.text "end")
in (_141_566)::[])
in (FStar_Format.reduce1 _141_567))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 730 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _60_672 -> (match (_60_672) with
| (_60_670, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 731 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 732 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 733 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _141_571 = (let _141_570 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _141_570 FStar_Format.hardline))
in (_141_571)::[])
end else begin
[]
end
in (let _141_583 = (let _141_582 = (let _141_581 = (let _141_580 = (let _141_579 = (FStar_Format.text "open Prims")
in (let _141_578 = (let _141_577 = (let _141_576 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _141_575 = (let _141_574 = (FStar_Format.reduce sub)
in (let _141_573 = (let _141_572 = (FStar_Format.cat tail FStar_Format.hardline)
in (_141_572)::[])
in (_141_574)::_141_573))
in (_141_576)::_141_575))
in (FStar_Format.hardline)::_141_577)
in (_141_579)::_141_578))
in (FStar_Format.hardline)::_141_580)
in (head)::_141_581)
in (FStar_List.append prefix _141_582))
in (FStar_All.pipe_left FStar_Format.reduce _141_583))))))))
end))
in (
# 749 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _60_684 -> (match (_60_684) with
| (x, s, m) -> begin
(let _141_585 = (for1_mod true (x, s, m))
in (x, _141_585))
end)) mllib)
in docs))
end))

# 750 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 756 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (
# 758 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_592 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _141_592 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 759 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (
# 762 "FStar.Extraction.ML.Code.fst"
let doc = (let _141_597 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _141_597 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





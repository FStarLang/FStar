
open Prims
# 36 "FStar.Extraction.ML.Code.fst"
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

# 37 "FStar.Extraction.ML.Code.fst"
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

# 38 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 39 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 42 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 43 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 54 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 55 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 56 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 57 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 58 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 60 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 61 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 67 "FStar.Extraction.ML.Code.fst"
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

# 73 "FStar.Extraction.ML.Code.fst"
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
(let _142_31 = (let _142_30 = (let _142_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_142_29)::[])
in (FStar_List.append pfx _142_30))
in Some (_142_31))
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

# 91 "FStar.Extraction.ML.Code.fst"
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
(let _142_36 = (path_of_ns currentModule ns)
in (_142_36, x))
end))
end))

# 99 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _142_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _142_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 104 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 108 "FStar.Extraction.ML.Code.fst"
let _60_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_50) with
| (p, s) -> begin
(let _142_46 = (let _142_45 = (let _142_44 = (ptsym_of_symbol s)
in (_142_44)::[])
in (FStar_List.append p _142_45))
in (FStar_String.concat "." _142_46))
end))
end)

# 112 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 113 "FStar.Extraction.ML.Code.fst"
let _60_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_55) with
| (p, s) -> begin
(
# 114 "FStar.Extraction.ML.Code.fst"
let s = if ((let _142_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _142_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 118 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 136 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 143 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 146 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 154 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 158 "FStar.Extraction.ML.Code.fst"
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

# 165 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 169 "FStar.Extraction.ML.Code.fst"
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

# 176 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 180 "FStar.Extraction.ML.Code.fst"
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

# 187 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 191 "FStar.Extraction.ML.Code.fst"
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

# 198 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 202 "FStar.Extraction.ML.Code.fst"
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

# 221 "FStar.Extraction.ML.Code.fst"
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 225 "FStar.Extraction.ML.Code.fst"
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

# 246 "FStar.Extraction.ML.Code.fst"
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
(let _142_92 = (let _142_91 = (encode_char c)
in (Prims.strcat "\'" _142_91))
in (Prims.strcat _142_92 "\'"))
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

# 270 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 273 "FStar.Extraction.ML.Code.fst"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _142_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _142_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 280 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 281 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_107 = (let _142_106 = (let _142_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_105 doc))
in (FStar_Format.hbox _142_106))
in (FStar_Format.parens _142_107))
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
in (let _142_110 = (let _142_109 = (let _142_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_108 args))
in (FStar_Format.hbox _142_109))
in (FStar_Format.parens _142_110)))
end)
in (
# 295 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _142_112 = (let _142_111 = (as_standard_type name)
in (FStar_Option.get _142_111))
in (Prims.snd _142_112))
end else begin
(ptsym currentModule name)
end
in (let _142_116 = (let _142_115 = (let _142_114 = (let _142_113 = (FStar_Format.text name)
in (_142_113)::[])
in (args)::_142_114)
in (FStar_Format.reduce1 _142_115))
in (FStar_Format.hbox _142_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_204, t2) -> begin
(
# 305 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 306 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _142_121 = (let _142_120 = (let _142_119 = (let _142_118 = (let _142_117 = (FStar_Format.text " -> ")
in (_142_117)::(d2)::[])
in (d1)::_142_118)
in (FStar_Format.reduce1 _142_119))
in (FStar_Format.hbox _142_120))
in (maybe_paren outer t_prio_fun _142_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

# 318 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 321 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_147 = (let _142_146 = (let _142_145 = (FStar_Format.text "Prims.checked_cast")
in (_142_145)::(doc)::[])
in (FStar_Format.reduce _142_146))
in (FStar_Format.parens _142_147))
end else begin
(let _142_152 = (let _142_151 = (let _142_150 = (FStar_Format.text "Obj.magic ")
in (let _142_149 = (let _142_148 = (FStar_Format.parens doc)
in (_142_148)::[])
in (_142_150)::_142_149))
in (FStar_Format.reduce _142_151))
in (FStar_Format.parens _142_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 327 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 328 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _142_156 = (let _142_155 = (let _142_154 = (FStar_Format.text ";")
in (_142_154)::(FStar_Format.hardline)::[])
in (d)::_142_155)
in (FStar_Format.reduce _142_156))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _142_157 = (string_of_mlconstant c)
in (FStar_Format.text _142_157))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _142_158 = (ptsym currentModule path)
in (FStar_Format.text _142_158))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 341 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_244 -> (match (_60_244) with
| (name, e) -> begin
(
# 342 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_165 = (let _142_164 = (let _142_161 = (ptsym currentModule (path, name))
in (FStar_Format.text _142_161))
in (let _142_163 = (let _142_162 = (FStar_Format.text "=")
in (_142_162)::(doc)::[])
in (_142_164)::_142_163))
in (FStar_Format.reduce1 _142_165)))
end))
in (let _142_168 = (let _142_167 = (FStar_Format.text "; ")
in (let _142_166 = (FStar_List.map for1 fields)
in (FStar_Format.combine _142_167 _142_166)))
in (FStar_Format.cbrackets _142_168)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 348 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_170 = (let _142_169 = (as_standard_constructor ctor)
in (FStar_Option.get _142_169))
in (Prims.snd _142_170))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 356 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_172 = (let _142_171 = (as_standard_constructor ctor)
in (FStar_Option.get _142_171))
in (Prims.snd _142_172))
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
(let _142_176 = (let _142_175 = (FStar_Format.parens x)
in (let _142_174 = (let _142_173 = (FStar_Format.text "::")
in (_142_173)::(xs)::[])
in (_142_175)::_142_174))
in (FStar_Format.reduce _142_176))
end
| (_60_263, _60_265) -> begin
(let _142_182 = (let _142_181 = (FStar_Format.text name)
in (let _142_180 = (let _142_179 = (let _142_178 = (let _142_177 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_177 args))
in (FStar_Format.parens _142_178))
in (_142_179)::[])
in (_142_181)::_142_180))
in (FStar_Format.reduce1 _142_182))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 370 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 371 "FStar.Extraction.ML.Code.fst"
let docs = (let _142_184 = (let _142_183 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_183 docs))
in (FStar_Format.parens _142_184))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 375 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _142_187 = (let _142_186 = (let _142_185 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_142_185)::[])
in (FStar_Format.hardline)::_142_186)
in (FStar_Format.reduce _142_187))
end else begin
FStar_Format.empty
end
in (
# 380 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 381 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _142_194 = (let _142_193 = (let _142_192 = (let _142_191 = (let _142_190 = (let _142_189 = (let _142_188 = (FStar_Format.text "in")
in (_142_188)::(body)::[])
in (FStar_Format.reduce1 _142_189))
in (_142_190)::[])
in (doc)::_142_191)
in (pre)::_142_192)
in (FStar_Format.combine FStar_Format.hardline _142_193))
in (FStar_Format.parens _142_194)))))
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
in (let _142_195 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _142_195))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 402 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 403 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_200 = (let _142_199 = (let _142_198 = (FStar_Format.text ".")
in (let _142_197 = (let _142_196 = (FStar_Format.text (Prims.snd f))
in (_142_196)::[])
in (_142_198)::_142_197))
in (e)::_142_199)
in (FStar_Format.reduce _142_200))
end else begin
(let _142_206 = (let _142_205 = (let _142_204 = (FStar_Format.text ".")
in (let _142_203 = (let _142_202 = (let _142_201 = (ptsym currentModule f)
in (FStar_Format.text _142_201))
in (_142_202)::[])
in (_142_204)::_142_203))
in (e)::_142_205)
in (FStar_Format.reduce _142_206))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 410 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_222 = (let _142_221 = (FStar_Format.text "(")
in (let _142_220 = (let _142_219 = (FStar_Format.text x)
in (let _142_218 = (let _142_217 = (match (xt) with
| Some (xxt) -> begin
(let _142_214 = (let _142_213 = (FStar_Format.text " : ")
in (let _142_212 = (let _142_211 = (doc_of_mltype currentModule outer xxt)
in (_142_211)::[])
in (_142_213)::_142_212))
in (FStar_Format.reduce1 _142_214))
end
| _60_345 -> begin
(FStar_Format.text "")
end)
in (let _142_216 = (let _142_215 = (FStar_Format.text ")")
in (_142_215)::[])
in (_142_217)::_142_216))
in (_142_219)::_142_218))
in (_142_221)::_142_220))
in (FStar_Format.reduce1 _142_222))
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
let doc = (let _142_229 = (let _142_228 = (FStar_Format.text "fun")
in (let _142_227 = (let _142_226 = (FStar_Format.reduce1 ids)
in (let _142_225 = (let _142_224 = (FStar_Format.text "->")
in (_142_224)::(body)::[])
in (_142_226)::_142_225))
in (_142_228)::_142_227))
in (FStar_Format.reduce1 _142_229))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 422 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 423 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_242 = (let _142_241 = (let _142_236 = (let _142_235 = (FStar_Format.text "if")
in (let _142_234 = (let _142_233 = (let _142_232 = (FStar_Format.text "then")
in (let _142_231 = (let _142_230 = (FStar_Format.text "begin")
in (_142_230)::[])
in (_142_232)::_142_231))
in (cond)::_142_233)
in (_142_235)::_142_234))
in (FStar_Format.reduce1 _142_236))
in (let _142_240 = (let _142_239 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _142_238 = (let _142_237 = (FStar_Format.text "end")
in (_142_237)::[])
in (_142_239)::_142_238))
in (_142_241)::_142_240))
in (FStar_Format.combine FStar_Format.hardline _142_242))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 433 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 434 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_265 = (let _142_264 = (let _142_249 = (let _142_248 = (FStar_Format.text "if")
in (let _142_247 = (let _142_246 = (let _142_245 = (FStar_Format.text "then")
in (let _142_244 = (let _142_243 = (FStar_Format.text "begin")
in (_142_243)::[])
in (_142_245)::_142_244))
in (cond)::_142_246)
in (_142_248)::_142_247))
in (FStar_Format.reduce1 _142_249))
in (let _142_263 = (let _142_262 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _142_261 = (let _142_260 = (let _142_255 = (let _142_254 = (FStar_Format.text "end")
in (let _142_253 = (let _142_252 = (FStar_Format.text "else")
in (let _142_251 = (let _142_250 = (FStar_Format.text "begin")
in (_142_250)::[])
in (_142_252)::_142_251))
in (_142_254)::_142_253))
in (FStar_Format.reduce1 _142_255))
in (let _142_259 = (let _142_258 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _142_257 = (let _142_256 = (FStar_Format.text "end")
in (_142_256)::[])
in (_142_258)::_142_257))
in (_142_260)::_142_259))
in (_142_262)::_142_261))
in (_142_264)::_142_263))
in (FStar_Format.combine FStar_Format.hardline _142_265))
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
let doc = (let _142_272 = (let _142_271 = (let _142_270 = (FStar_Format.text "match")
in (let _142_269 = (let _142_268 = (FStar_Format.parens cond)
in (let _142_267 = (let _142_266 = (FStar_Format.text "with")
in (_142_266)::[])
in (_142_268)::_142_267))
in (_142_270)::_142_269))
in (FStar_Format.reduce1 _142_271))
in (_142_272)::pats)
in (
# 449 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _142_277 = (let _142_276 = (FStar_Format.text "raise")
in (let _142_275 = (let _142_274 = (let _142_273 = (ptctor currentModule exn)
in (FStar_Format.text _142_273))
in (_142_274)::[])
in (_142_276)::_142_275))
in (FStar_Format.reduce1 _142_277))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 457 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _142_286 = (let _142_285 = (FStar_Format.text "raise")
in (let _142_284 = (let _142_283 = (let _142_278 = (ptctor currentModule exn)
in (FStar_Format.text _142_278))
in (let _142_282 = (let _142_281 = (let _142_280 = (let _142_279 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_279 args))
in (FStar_Format.parens _142_280))
in (_142_281)::[])
in (_142_283)::_142_282))
in (_142_285)::_142_284))
in (FStar_Format.reduce1 _142_286)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _142_303 = (let _142_302 = (let _142_290 = (let _142_289 = (FStar_Format.text "try")
in (let _142_288 = (let _142_287 = (FStar_Format.text "begin")
in (_142_287)::[])
in (_142_289)::_142_288))
in (FStar_Format.reduce1 _142_290))
in (let _142_301 = (let _142_300 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_299 = (let _142_298 = (let _142_294 = (let _142_293 = (FStar_Format.text "end")
in (let _142_292 = (let _142_291 = (FStar_Format.text "with")
in (_142_291)::[])
in (_142_293)::_142_292))
in (FStar_Format.reduce1 _142_294))
in (let _142_297 = (let _142_296 = (let _142_295 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _142_295))
in (_142_296)::[])
in (_142_298)::_142_297))
in (_142_300)::_142_299))
in (_142_302)::_142_301))
in (FStar_Format.combine FStar_Format.hardline _142_303))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 468 "FStar.Extraction.ML.Code.fst"
let _60_399 = (let _142_308 = (as_bin_op p)
in (FStar_Option.get _142_308))
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
let doc = (let _142_311 = (let _142_310 = (let _142_309 = (FStar_Format.text txt)
in (_142_309)::(e2)::[])
in (e1)::_142_310)
in (FStar_Format.reduce1 _142_311))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 475 "FStar.Extraction.ML.Code.fst"
let _60_409 = (let _142_315 = (as_uni_op p)
in (FStar_Option.get _142_315))
in (match (_60_409) with
| (_60_407, txt) -> begin
(
# 476 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 477 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_319 = (let _142_318 = (FStar_Format.text txt)
in (let _142_317 = (let _142_316 = (FStar_Format.parens e1)
in (_142_316)::[])
in (_142_318)::_142_317))
in (FStar_Format.reduce1 _142_319))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _142_322 = (string_of_mlconstant c)
in (FStar_Format.text _142_322))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 487 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _60_426 -> (match (_60_426) with
| (name, p) -> begin
(let _142_331 = (let _142_330 = (let _142_325 = (ptsym currentModule (path, name))
in (FStar_Format.text _142_325))
in (let _142_329 = (let _142_328 = (FStar_Format.text "=")
in (let _142_327 = (let _142_326 = (doc_of_pattern currentModule p)
in (_142_326)::[])
in (_142_328)::_142_327))
in (_142_330)::_142_329))
in (FStar_Format.reduce1 _142_331))
end))
in (let _142_334 = (let _142_333 = (FStar_Format.text "; ")
in (let _142_332 = (FStar_List.map for1 fields)
in (FStar_Format.combine _142_333 _142_332)))
in (FStar_Format.cbrackets _142_334)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 491 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_336 = (let _142_335 = (as_standard_constructor ctor)
in (FStar_Option.get _142_335))
in (Prims.snd _142_336))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 499 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_338 = (let _142_337 = (as_standard_constructor ctor)
in (FStar_Option.get _142_337))
in (Prims.snd _142_338))
end else begin
(ptctor currentModule ctor)
end
in (
# 504 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _142_344 = (let _142_343 = (doc_of_pattern currentModule x)
in (let _142_342 = (let _142_341 = (FStar_Format.text "::")
in (let _142_340 = (let _142_339 = (doc_of_pattern currentModule xs)
in (_142_339)::[])
in (_142_341)::_142_340))
in (_142_343)::_142_342))
in (FStar_Format.reduce _142_344))
end
| (_60_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_445)::[]) -> begin
(let _142_349 = (let _142_348 = (FStar_Format.text name)
in (let _142_347 = (let _142_346 = (let _142_345 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _142_345))
in (_142_346)::[])
in (_142_348)::_142_347))
in (FStar_Format.reduce1 _142_349))
end
| _60_450 -> begin
(let _142_356 = (let _142_355 = (FStar_Format.text name)
in (let _142_354 = (let _142_353 = (let _142_352 = (let _142_351 = (FStar_Format.text ", ")
in (let _142_350 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _142_351 _142_350)))
in (FStar_Format.parens _142_352))
in (_142_353)::[])
in (_142_355)::_142_354))
in (FStar_Format.reduce1 _142_356))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 513 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _142_358 = (let _142_357 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_357 ps))
in (FStar_Format.parens _142_358)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 517 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 518 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _142_359 = (FStar_Format.text " | ")
in (FStar_Format.combine _142_359 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _60_463 -> (match (_60_463) with
| (p, cond, e) -> begin
(
# 523 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _142_365 = (let _142_364 = (FStar_Format.text "|")
in (let _142_363 = (let _142_362 = (doc_of_pattern currentModule p)
in (_142_362)::[])
in (_142_364)::_142_363))
in (FStar_Format.reduce1 _142_365))
end
| Some (c) -> begin
(
# 527 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _142_371 = (let _142_370 = (FStar_Format.text "|")
in (let _142_369 = (let _142_368 = (doc_of_pattern currentModule p)
in (let _142_367 = (let _142_366 = (FStar_Format.text "when")
in (_142_366)::(c)::[])
in (_142_368)::_142_367))
in (_142_370)::_142_369))
in (FStar_Format.reduce1 _142_371)))
end)
in (let _142_382 = (let _142_381 = (let _142_376 = (let _142_375 = (let _142_374 = (FStar_Format.text "->")
in (let _142_373 = (let _142_372 = (FStar_Format.text "begin")
in (_142_372)::[])
in (_142_374)::_142_373))
in (case)::_142_375)
in (FStar_Format.reduce1 _142_376))
in (let _142_380 = (let _142_379 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_378 = (let _142_377 = (FStar_Format.text "end")
in (_142_377)::[])
in (_142_379)::_142_378))
in (_142_381)::_142_380))
in (FStar_Format.combine FStar_Format.hardline _142_382)))
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
in (let _142_389 = (let _142_388 = (FStar_Format.text ":")
in (_142_388)::(ty)::[])
in (FStar_Format.reduce1 _142_389)))
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
in (let _142_391 = (let _142_390 = (FStar_Format.text ":")
in (_142_390)::(ty)::[])
in (FStar_Format.reduce1 _142_391)))
end)
end else begin
(FStar_Format.text "")
end
end
in (let _142_398 = (let _142_397 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _142_396 = (let _142_395 = (FStar_Format.reduce1 ids)
in (let _142_394 = (let _142_393 = (let _142_392 = (FStar_Format.text "=")
in (_142_392)::(e)::[])
in (ty_annot)::_142_393)
in (_142_395)::_142_394))
in (_142_397)::_142_396))
in (FStar_Format.reduce1 _142_398))))))
end))
in (
# 568 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _142_402 = (let _142_401 = (FStar_Format.text "let")
in (let _142_400 = (let _142_399 = (FStar_Format.text "rec")
in (_142_399)::[])
in (_142_401)::_142_400))
in (FStar_Format.reduce1 _142_402))
end else begin
(FStar_Format.text "let")
end
in (
# 570 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 571 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _142_406 = (let _142_405 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_142_405)::(doc)::[])
in (FStar_Format.reduce1 _142_406))) lets)
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
in (let _142_413 = (let _142_412 = (FStar_Format.text "#")
in (let _142_411 = (let _142_410 = (FStar_Format.num lineno)
in (let _142_409 = (let _142_408 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_142_408)::[])
in (_142_410)::_142_409))
in (_142_412)::_142_411))
in (FStar_Format.reduce1 _142_413)))
end
end))

# 586 "FStar.Extraction.ML.Code.fst"
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
in (let _142_422 = (let _142_421 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_421 doc))
in (FStar_Format.parens _142_422)))
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
in (let _142_429 = (let _142_428 = (let _142_427 = (FStar_Format.text ":")
in (_142_427)::(ty)::[])
in (name)::_142_428)
in (FStar_Format.reduce1 _142_429))))
end))
in (let _142_432 = (let _142_431 = (FStar_Format.text "; ")
in (let _142_430 = (FStar_List.map forfield fields)
in (FStar_Format.combine _142_431 _142_430)))
in (FStar_Format.cbrackets _142_432)))
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
let tys = (let _142_435 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_435 tys))
in (let _142_439 = (let _142_438 = (FStar_Format.text name)
in (let _142_437 = (let _142_436 = (FStar_Format.text "of")
in (_142_436)::(tys)::[])
in (_142_438)::_142_437))
in (FStar_Format.reduce1 _142_439))))
end)
end))
in (
# 620 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 621 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _142_442 = (let _142_441 = (FStar_Format.text "|")
in (_142_441)::(d)::[])
in (FStar_Format.reduce1 _142_442))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 626 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_446 = (let _142_445 = (let _142_444 = (let _142_443 = (ptsym currentModule ([], x))
in (FStar_Format.text _142_443))
in (_142_444)::[])
in (tparams)::_142_445)
in (FStar_Format.reduce1 _142_446))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 631 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _142_451 = (let _142_450 = (let _142_449 = (let _142_448 = (let _142_447 = (FStar_Format.text "=")
in (_142_447)::[])
in (doc)::_142_448)
in (FStar_Format.reduce1 _142_449))
in (_142_450)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _142_451)))
end))))
end))
in (
# 636 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 637 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _142_456 = (let _142_455 = (FStar_Format.text "type")
in (let _142_454 = (let _142_453 = (let _142_452 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _142_452 doc))
in (_142_453)::[])
in (_142_455)::_142_454))
in (FStar_Format.reduce1 _142_456))
end else begin
(FStar_Format.text "")
end
in doc))))

# 641 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _142_476 = (let _142_475 = (let _142_468 = (let _142_467 = (FStar_Format.text "module")
in (let _142_466 = (let _142_465 = (FStar_Format.text x)
in (let _142_464 = (let _142_463 = (FStar_Format.text "=")
in (_142_463)::[])
in (_142_465)::_142_464))
in (_142_467)::_142_466))
in (FStar_Format.reduce1 _142_468))
in (let _142_474 = (let _142_473 = (doc_of_sig currentModule subsig)
in (let _142_472 = (let _142_471 = (let _142_470 = (let _142_469 = (FStar_Format.text "end")
in (_142_469)::[])
in (FStar_Format.reduce1 _142_470))
in (_142_471)::[])
in (_142_473)::_142_472))
in (_142_475)::_142_474))
in (FStar_Format.combine FStar_Format.hardline _142_476))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _142_480 = (let _142_479 = (FStar_Format.text "exception")
in (let _142_478 = (let _142_477 = (FStar_Format.text x)
in (_142_477)::[])
in (_142_479)::_142_478))
in (FStar_Format.reduce1 _142_480))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 653 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 654 "FStar.Extraction.ML.Code.fst"
let args = (let _142_482 = (let _142_481 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_481 args))
in (FStar_Format.parens _142_482))
in (let _142_488 = (let _142_487 = (FStar_Format.text "exception")
in (let _142_486 = (let _142_485 = (FStar_Format.text x)
in (let _142_484 = (let _142_483 = (FStar_Format.text "of")
in (_142_483)::(args)::[])
in (_142_485)::_142_484))
in (_142_487)::_142_486))
in (FStar_Format.reduce1 _142_488))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_594, ty)) -> begin
(
# 658 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _142_494 = (let _142_493 = (FStar_Format.text "val")
in (let _142_492 = (let _142_491 = (FStar_Format.text x)
in (let _142_490 = (let _142_489 = (FStar_Format.text ": ")
in (_142_489)::(ty)::[])
in (_142_491)::_142_490))
in (_142_493)::_142_492))
in (FStar_Format.reduce1 _142_494)))
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

# 672 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _142_505 = (let _142_504 = (FStar_Format.text "exception")
in (let _142_503 = (let _142_502 = (FStar_Format.text x)
in (_142_502)::[])
in (_142_504)::_142_503))
in (FStar_Format.reduce1 _142_505))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 678 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 679 "FStar.Extraction.ML.Code.fst"
let args = (let _142_507 = (let _142_506 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_506 args))
in (FStar_Format.parens _142_507))
in (let _142_513 = (let _142_512 = (FStar_Format.text "exception")
in (let _142_511 = (let _142_510 = (FStar_Format.text x)
in (let _142_509 = (let _142_508 = (FStar_Format.text "of")
in (_142_508)::(args)::[])
in (_142_510)::_142_509))
in (_142_512)::_142_511))
in (FStar_Format.reduce1 _142_513))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _142_521 = (let _142_520 = (FStar_Format.text "let")
in (let _142_519 = (let _142_518 = (FStar_Format.text "_")
in (let _142_517 = (let _142_516 = (FStar_Format.text "=")
in (let _142_515 = (let _142_514 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_142_514)::[])
in (_142_516)::_142_515))
in (_142_518)::_142_517))
in (_142_520)::_142_519))
in (FStar_Format.reduce1 _142_521))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 698 "FStar.Extraction.ML.Code.fst"
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

# 705 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _60_640 -> (match (_60_640) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 706 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _60_647 -> (match (_60_647) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 707 "FStar.Extraction.ML.Code.fst"
let head = (let _142_540 = (let _142_539 = (FStar_Format.text "module")
in (let _142_538 = (let _142_537 = (FStar_Format.text x)
in (let _142_536 = (let _142_535 = (FStar_Format.text ":")
in (let _142_534 = (let _142_533 = (FStar_Format.text "sig")
in (_142_533)::[])
in (_142_535)::_142_534))
in (_142_537)::_142_536))
in (_142_539)::_142_538))
in (FStar_Format.reduce1 _142_540))
in (
# 708 "FStar.Extraction.ML.Code.fst"
let tail = (let _142_542 = (let _142_541 = (FStar_Format.text "end")
in (_142_541)::[])
in (FStar_Format.reduce1 _142_542))
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
in (let _142_552 = (let _142_551 = (FStar_Format.cat head FStar_Format.hardline)
in (let _142_550 = (let _142_549 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _142_548 = (let _142_547 = (FStar_Format.reduce sub)
in (let _142_546 = (let _142_545 = (FStar_Format.cat tail FStar_Format.hardline)
in (_142_545)::[])
in (_142_547)::_142_546))
in (_142_549)::_142_548))
in (_142_551)::_142_550))
in (FStar_Format.reduce _142_552)))))))
end))
and for1_mod = (fun istop _60_666 -> (match (_60_666) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 722 "FStar.Extraction.ML.Code.fst"
let head = (let _142_565 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_557 = (FStar_Format.text "module")
in (let _142_556 = (let _142_555 = (FStar_Format.text x)
in (_142_555)::[])
in (_142_557)::_142_556))
end else begin
if (not (istop)) then begin
(let _142_564 = (FStar_Format.text "module")
in (let _142_563 = (let _142_562 = (FStar_Format.text x)
in (let _142_561 = (let _142_560 = (FStar_Format.text "=")
in (let _142_559 = (let _142_558 = (FStar_Format.text "struct")
in (_142_558)::[])
in (_142_560)::_142_559))
in (_142_562)::_142_561))
in (_142_564)::_142_563))
end else begin
[]
end
end
in (FStar_Format.reduce1 _142_565))
in (
# 727 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _142_567 = (let _142_566 = (FStar_Format.text "end")
in (_142_566)::[])
in (FStar_Format.reduce1 _142_567))
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
(let _142_571 = (let _142_570 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _142_570 FStar_Format.hardline))
in (_142_571)::[])
end else begin
[]
end
in (let _142_583 = (let _142_582 = (let _142_581 = (let _142_580 = (let _142_579 = (FStar_Format.text "open Prims")
in (let _142_578 = (let _142_577 = (let _142_576 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _142_575 = (let _142_574 = (FStar_Format.reduce sub)
in (let _142_573 = (let _142_572 = (FStar_Format.cat tail FStar_Format.hardline)
in (_142_572)::[])
in (_142_574)::_142_573))
in (_142_576)::_142_575))
in (FStar_Format.hardline)::_142_577)
in (_142_579)::_142_578))
in (FStar_Format.hardline)::_142_580)
in (head)::_142_581)
in (FStar_List.append prefix _142_582))
in (FStar_All.pipe_left FStar_Format.reduce _142_583))))))))
end))
in (
# 749 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _60_684 -> (match (_60_684) with
| (x, s, m) -> begin
(let _142_585 = (for1_mod true (x, s, m))
in (x, _142_585))
end)) mllib)
in docs))
end))

# 753 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 757 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (
# 758 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_592 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _142_592 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 761 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (
# 762 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_597 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _142_597 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





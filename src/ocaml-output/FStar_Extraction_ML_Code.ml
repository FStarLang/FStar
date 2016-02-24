
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
| Infix (_61_3) -> begin
_61_3
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
| ([], _61_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_61_18, _61_20) -> begin
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
let _61_31 = (FStar_Util.first_N cg_len ns)
in (match (_61_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _140_31 = (let _140_30 = (let _140_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_140_29)::[])
in (FStar_List.append pfx _140_30))
in Some (_140_31))
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
| _61_41 -> begin
(
# 96 "FStar.Extraction.ML.Code.fst"
let _61_44 = x
in (match (_61_44) with
| (ns, x) -> begin
(let _140_36 = (path_of_ns currentModule ns)
in (_140_36, x))
end))
end))

# 99 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _140_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _140_39)) <> (FStar_String.get s 0)) then begin
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
let _61_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_50) with
| (p, s) -> begin
(let _140_46 = (let _140_45 = (let _140_44 = (ptsym_of_symbol s)
in (_140_44)::[])
in (FStar_List.append p _140_45))
in (FStar_String.concat "." _140_46))
end))
end)

# 112 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 113 "FStar.Extraction.ML.Code.fst"
let _61_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_55) with
| (p, s) -> begin
(
# 114 "FStar.Extraction.ML.Code.fst"
let s = if ((let _140_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _140_51)) <> (FStar_String.get s 0)) then begin
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
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _61_60 -> (match (_61_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _61_66 -> (match (_61_66) with
| (y, _61_63, _61_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 165 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 169 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _61_70 -> (match (_61_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _61_74 -> (match (_61_74) with
| (y, _61_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 176 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 180 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _61_78 -> (match (_61_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _61_82 -> (match (_61_82) with
| (y, _61_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 187 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 191 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _61_86 -> (match (_61_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _61_90 -> (match (_61_90) with
| (y, _61_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 198 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 202 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _61_94 inner doc -> (match (_61_94) with
| (outer, side) -> begin
(
# 203 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 204 "FStar.Extraction.ML.Code.fst"
let _61_103 = _inner
in (match (_61_103) with
| (pi, fi) -> begin
(
# 205 "FStar.Extraction.ML.Code.fst"
let _61_106 = _outer
in (match (_61_106) with
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
| (_61_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_61_134, _61_136) -> begin
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
| _61_154 -> begin
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
(let _140_92 = (let _140_91 = (encode_char c)
in (Prims.strcat "\'" _140_91))
in (Prims.strcat _140_92 "\'"))
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
in (let _140_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _140_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 280 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 281 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_107 = (let _140_106 = (let _140_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _140_105 doc))
in (FStar_Format.hbox _140_106))
in (FStar_Format.parens _140_107))
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
| _61_198 -> begin
(
# 290 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _140_110 = (let _140_109 = (let _140_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_108 args))
in (FStar_Format.hbox _140_109))
in (FStar_Format.parens _140_110)))
end)
in (
# 295 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _140_112 = (let _140_111 = (as_standard_type name)
in (FStar_Option.get _140_111))
in (Prims.snd _140_112))
end else begin
(ptsym currentModule name)
end
in (let _140_116 = (let _140_115 = (let _140_114 = (let _140_113 = (FStar_Format.text name)
in (_140_113)::[])
in (args)::_140_114)
in (FStar_Format.reduce1 _140_115))
in (FStar_Format.hbox _140_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _61_204, t2) -> begin
(
# 305 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 306 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _140_121 = (let _140_120 = (let _140_119 = (let _140_118 = (let _140_117 = (FStar_Format.text " -> ")
in (_140_117)::(d2)::[])
in (d1)::_140_118)
in (FStar_Format.reduce1 _140_119))
in (FStar_Format.hbox _140_120))
in (maybe_paren outer t_prio_fun _140_121))))
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
(let _140_147 = (let _140_146 = (let _140_145 = (FStar_Format.text "Prims.checked_cast")
in (_140_145)::(doc)::[])
in (FStar_Format.reduce _140_146))
in (FStar_Format.parens _140_147))
end else begin
(let _140_152 = (let _140_151 = (let _140_150 = (FStar_Format.text "Obj.magic ")
in (let _140_149 = (let _140_148 = (FStar_Format.parens doc)
in (_140_148)::[])
in (_140_150)::_140_149))
in (FStar_Format.reduce _140_151))
in (FStar_Format.parens _140_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 327 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 328 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _140_156 = (let _140_155 = (let _140_154 = (FStar_Format.text ";")
in (_140_154)::(FStar_Format.hardline)::[])
in (d)::_140_155)
in (FStar_Format.reduce _140_156))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _140_157 = (string_of_mlconstant c)
in (FStar_Format.text _140_157))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _61_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _140_158 = (ptsym currentModule path)
in (FStar_Format.text _140_158))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 341 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _61_244 -> (match (_61_244) with
| (name, e) -> begin
(
# 342 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _140_165 = (let _140_164 = (let _140_161 = (ptsym currentModule (path, name))
in (FStar_Format.text _140_161))
in (let _140_163 = (let _140_162 = (FStar_Format.text "=")
in (_140_162)::(doc)::[])
in (_140_164)::_140_163))
in (FStar_Format.reduce1 _140_165)))
end))
in (let _140_168 = (let _140_167 = (FStar_Format.text "; ")
in (let _140_166 = (FStar_List.map for1 fields)
in (FStar_Format.combine _140_167 _140_166)))
in (FStar_Format.cbrackets _140_168)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 348 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _140_170 = (let _140_169 = (as_standard_constructor ctor)
in (FStar_Option.get _140_169))
in (Prims.snd _140_170))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 356 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _140_172 = (let _140_171 = (as_standard_constructor ctor)
in (FStar_Option.get _140_171))
in (Prims.snd _140_172))
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
(let _140_176 = (let _140_175 = (FStar_Format.parens x)
in (let _140_174 = (let _140_173 = (FStar_Format.text "::")
in (_140_173)::(xs)::[])
in (_140_175)::_140_174))
in (FStar_Format.reduce _140_176))
end
| (_61_263, _61_265) -> begin
(let _140_182 = (let _140_181 = (FStar_Format.text name)
in (let _140_180 = (let _140_179 = (let _140_178 = (let _140_177 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_177 args))
in (FStar_Format.parens _140_178))
in (_140_179)::[])
in (_140_181)::_140_180))
in (FStar_Format.reduce1 _140_182))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 370 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 371 "FStar.Extraction.ML.Code.fst"
let docs = (let _140_184 = (let _140_183 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_183 docs))
in (FStar_Format.parens _140_184))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 375 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _140_187 = (let _140_186 = (let _140_185 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_140_185)::[])
in (FStar_Format.hardline)::_140_186)
in (FStar_Format.reduce _140_187))
end else begin
FStar_Format.empty
end
in (
# 380 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 381 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _140_194 = (let _140_193 = (let _140_192 = (let _140_191 = (let _140_190 = (let _140_189 = (let _140_188 = (FStar_Format.text "in")
in (_140_188)::(body)::[])
in (FStar_Format.reduce1 _140_189))
in (_140_190)::[])
in (doc)::_140_191)
in (pre)::_140_192)
in (FStar_Format.combine FStar_Format.hardline _140_193))
in (FStar_Format.parens _140_194)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _61_294; FStar_Extraction_ML_Syntax.loc = _61_292}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _61_314; FStar_Extraction_ML_Syntax.loc = _61_312}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _61_326 -> begin
(
# 396 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 397 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _140_195 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _140_195))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 402 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 403 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _140_200 = (let _140_199 = (let _140_198 = (FStar_Format.text ".")
in (let _140_197 = (let _140_196 = (FStar_Format.text (Prims.snd f))
in (_140_196)::[])
in (_140_198)::_140_197))
in (e)::_140_199)
in (FStar_Format.reduce _140_200))
end else begin
(let _140_206 = (let _140_205 = (let _140_204 = (FStar_Format.text ".")
in (let _140_203 = (let _140_202 = (let _140_201 = (ptsym currentModule f)
in (FStar_Format.text _140_201))
in (_140_202)::[])
in (_140_204)::_140_203))
in (e)::_140_205)
in (FStar_Format.reduce _140_206))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 410 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _140_222 = (let _140_221 = (FStar_Format.text "(")
in (let _140_220 = (let _140_219 = (FStar_Format.text x)
in (let _140_218 = (let _140_217 = (match (xt) with
| Some (xxt) -> begin
(let _140_214 = (let _140_213 = (FStar_Format.text " : ")
in (let _140_212 = (let _140_211 = (doc_of_mltype currentModule outer xxt)
in (_140_211)::[])
in (_140_213)::_140_212))
in (FStar_Format.reduce1 _140_214))
end
| _61_345 -> begin
(FStar_Format.text "")
end)
in (let _140_216 = (let _140_215 = (FStar_Format.text ")")
in (_140_215)::[])
in (_140_217)::_140_216))
in (_140_219)::_140_218))
in (_140_221)::_140_220))
in (FStar_Format.reduce1 _140_222))
end else begin
(FStar_Format.text x)
end)
in (
# 416 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _61_351 -> (match (_61_351) with
| ((x, _61_348), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 417 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 418 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_229 = (let _140_228 = (FStar_Format.text "fun")
in (let _140_227 = (let _140_226 = (FStar_Format.reduce1 ids)
in (let _140_225 = (let _140_224 = (FStar_Format.text "->")
in (_140_224)::(body)::[])
in (_140_226)::_140_225))
in (_140_228)::_140_227))
in (FStar_Format.reduce1 _140_229))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 422 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 423 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_242 = (let _140_241 = (let _140_236 = (let _140_235 = (FStar_Format.text "if")
in (let _140_234 = (let _140_233 = (let _140_232 = (FStar_Format.text "then")
in (let _140_231 = (let _140_230 = (FStar_Format.text "begin")
in (_140_230)::[])
in (_140_232)::_140_231))
in (cond)::_140_233)
in (_140_235)::_140_234))
in (FStar_Format.reduce1 _140_236))
in (let _140_240 = (let _140_239 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _140_238 = (let _140_237 = (FStar_Format.text "end")
in (_140_237)::[])
in (_140_239)::_140_238))
in (_140_241)::_140_240))
in (FStar_Format.combine FStar_Format.hardline _140_242))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 433 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 434 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_265 = (let _140_264 = (let _140_249 = (let _140_248 = (FStar_Format.text "if")
in (let _140_247 = (let _140_246 = (let _140_245 = (FStar_Format.text "then")
in (let _140_244 = (let _140_243 = (FStar_Format.text "begin")
in (_140_243)::[])
in (_140_245)::_140_244))
in (cond)::_140_246)
in (_140_248)::_140_247))
in (FStar_Format.reduce1 _140_249))
in (let _140_263 = (let _140_262 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _140_261 = (let _140_260 = (let _140_255 = (let _140_254 = (FStar_Format.text "end")
in (let _140_253 = (let _140_252 = (FStar_Format.text "else")
in (let _140_251 = (let _140_250 = (FStar_Format.text "begin")
in (_140_250)::[])
in (_140_252)::_140_251))
in (_140_254)::_140_253))
in (FStar_Format.reduce1 _140_255))
in (let _140_259 = (let _140_258 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _140_257 = (let _140_256 = (FStar_Format.text "end")
in (_140_256)::[])
in (_140_258)::_140_257))
in (_140_260)::_140_259))
in (_140_262)::_140_261))
in (_140_264)::_140_263))
in (FStar_Format.combine FStar_Format.hardline _140_265))
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
let doc = (let _140_272 = (let _140_271 = (let _140_270 = (FStar_Format.text "match")
in (let _140_269 = (let _140_268 = (FStar_Format.parens cond)
in (let _140_267 = (let _140_266 = (FStar_Format.text "with")
in (_140_266)::[])
in (_140_268)::_140_267))
in (_140_270)::_140_269))
in (FStar_Format.reduce1 _140_271))
in (_140_272)::pats)
in (
# 449 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _140_277 = (let _140_276 = (FStar_Format.text "raise")
in (let _140_275 = (let _140_274 = (let _140_273 = (ptctor currentModule exn)
in (FStar_Format.text _140_273))
in (_140_274)::[])
in (_140_276)::_140_275))
in (FStar_Format.reduce1 _140_277))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 457 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _140_286 = (let _140_285 = (FStar_Format.text "raise")
in (let _140_284 = (let _140_283 = (let _140_278 = (ptctor currentModule exn)
in (FStar_Format.text _140_278))
in (let _140_282 = (let _140_281 = (let _140_280 = (let _140_279 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_279 args))
in (FStar_Format.parens _140_280))
in (_140_281)::[])
in (_140_283)::_140_282))
in (_140_285)::_140_284))
in (FStar_Format.reduce1 _140_286)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _140_303 = (let _140_302 = (let _140_290 = (let _140_289 = (FStar_Format.text "try")
in (let _140_288 = (let _140_287 = (FStar_Format.text "begin")
in (_140_287)::[])
in (_140_289)::_140_288))
in (FStar_Format.reduce1 _140_290))
in (let _140_301 = (let _140_300 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _140_299 = (let _140_298 = (let _140_294 = (let _140_293 = (FStar_Format.text "end")
in (let _140_292 = (let _140_291 = (FStar_Format.text "with")
in (_140_291)::[])
in (_140_293)::_140_292))
in (FStar_Format.reduce1 _140_294))
in (let _140_297 = (let _140_296 = (let _140_295 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _140_295))
in (_140_296)::[])
in (_140_298)::_140_297))
in (_140_300)::_140_299))
in (_140_302)::_140_301))
in (FStar_Format.combine FStar_Format.hardline _140_303))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 468 "FStar.Extraction.ML.Code.fst"
let _61_399 = (let _140_308 = (as_bin_op p)
in (FStar_Option.get _140_308))
in (match (_61_399) with
| (_61_396, prio, txt) -> begin
(
# 469 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 471 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_311 = (let _140_310 = (let _140_309 = (FStar_Format.text txt)
in (_140_309)::(e2)::[])
in (e1)::_140_310)
in (FStar_Format.reduce1 _140_311))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 475 "FStar.Extraction.ML.Code.fst"
let _61_409 = (let _140_315 = (as_uni_op p)
in (FStar_Option.get _140_315))
in (match (_61_409) with
| (_61_407, txt) -> begin
(
# 476 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 477 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_319 = (let _140_318 = (FStar_Format.text txt)
in (let _140_317 = (let _140_316 = (FStar_Format.parens e1)
in (_140_316)::[])
in (_140_318)::_140_317))
in (FStar_Format.reduce1 _140_319))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _140_322 = (string_of_mlconstant c)
in (FStar_Format.text _140_322))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 487 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _61_426 -> (match (_61_426) with
| (name, p) -> begin
(let _140_331 = (let _140_330 = (let _140_325 = (ptsym currentModule (path, name))
in (FStar_Format.text _140_325))
in (let _140_329 = (let _140_328 = (FStar_Format.text "=")
in (let _140_327 = (let _140_326 = (doc_of_pattern currentModule p)
in (_140_326)::[])
in (_140_328)::_140_327))
in (_140_330)::_140_329))
in (FStar_Format.reduce1 _140_331))
end))
in (let _140_334 = (let _140_333 = (FStar_Format.text "; ")
in (let _140_332 = (FStar_List.map for1 fields)
in (FStar_Format.combine _140_333 _140_332)))
in (FStar_Format.cbrackets _140_334)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 491 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _140_336 = (let _140_335 = (as_standard_constructor ctor)
in (FStar_Option.get _140_335))
in (Prims.snd _140_336))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 499 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _140_338 = (let _140_337 = (as_standard_constructor ctor)
in (FStar_Option.get _140_337))
in (Prims.snd _140_338))
end else begin
(ptctor currentModule ctor)
end
in (
# 504 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _140_344 = (let _140_343 = (doc_of_pattern currentModule x)
in (let _140_342 = (let _140_341 = (FStar_Format.text "::")
in (let _140_340 = (let _140_339 = (doc_of_pattern currentModule xs)
in (_140_339)::[])
in (_140_341)::_140_340))
in (_140_343)::_140_342))
in (FStar_Format.reduce _140_344))
end
| (_61_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_61_445)::[]) -> begin
(let _140_349 = (let _140_348 = (FStar_Format.text name)
in (let _140_347 = (let _140_346 = (let _140_345 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _140_345))
in (_140_346)::[])
in (_140_348)::_140_347))
in (FStar_Format.reduce1 _140_349))
end
| _61_450 -> begin
(let _140_356 = (let _140_355 = (FStar_Format.text name)
in (let _140_354 = (let _140_353 = (let _140_352 = (let _140_351 = (FStar_Format.text ", ")
in (let _140_350 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _140_351 _140_350)))
in (FStar_Format.parens _140_352))
in (_140_353)::[])
in (_140_355)::_140_354))
in (FStar_Format.reduce1 _140_356))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 513 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _140_358 = (let _140_357 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_357 ps))
in (FStar_Format.parens _140_358)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 517 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 518 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _140_359 = (FStar_Format.text " | ")
in (FStar_Format.combine _140_359 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _61_463 -> (match (_61_463) with
| (p, cond, e) -> begin
(
# 523 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _140_365 = (let _140_364 = (FStar_Format.text "|")
in (let _140_363 = (let _140_362 = (doc_of_pattern currentModule p)
in (_140_362)::[])
in (_140_364)::_140_363))
in (FStar_Format.reduce1 _140_365))
end
| Some (c) -> begin
(
# 527 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _140_371 = (let _140_370 = (FStar_Format.text "|")
in (let _140_369 = (let _140_368 = (doc_of_pattern currentModule p)
in (let _140_367 = (let _140_366 = (FStar_Format.text "when")
in (_140_366)::(c)::[])
in (_140_368)::_140_367))
in (_140_370)::_140_369))
in (FStar_Format.reduce1 _140_371)))
end)
in (let _140_382 = (let _140_381 = (let _140_376 = (let _140_375 = (let _140_374 = (FStar_Format.text "->")
in (let _140_373 = (let _140_372 = (FStar_Format.text "begin")
in (_140_372)::[])
in (_140_374)::_140_373))
in (case)::_140_375)
in (FStar_Format.reduce1 _140_376))
in (let _140_380 = (let _140_379 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _140_378 = (let _140_377 = (FStar_Format.text "end")
in (_140_377)::[])
in (_140_379)::_140_378))
in (_140_381)::_140_380))
in (FStar_Format.combine FStar_Format.hardline _140_382)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _61_473 -> (match (_61_473) with
| (rec_, top_level, lets) -> begin
(
# 538 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _61_480 -> (match (_61_480) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _61_477; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(
# 539 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 540 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 544 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _61_486 -> (match (_61_486) with
| (x, _61_485) -> begin
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
in (let _140_389 = (let _140_388 = (FStar_Format.text ":")
in (_140_388)::(ty)::[])
in (FStar_Format.reduce1 _140_389)))
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
in (let _140_391 = (let _140_390 = (FStar_Format.text ":")
in (_140_390)::(ty)::[])
in (FStar_Format.reduce1 _140_391)))
end)
end else begin
(FStar_Format.text "")
end
end
in (let _140_398 = (let _140_397 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _140_396 = (let _140_395 = (FStar_Format.reduce1 ids)
in (let _140_394 = (let _140_393 = (let _140_392 = (FStar_Format.text "=")
in (_140_392)::(e)::[])
in (ty_annot)::_140_393)
in (_140_395)::_140_394))
in (_140_397)::_140_396))
in (FStar_Format.reduce1 _140_398))))))
end))
in (
# 568 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _140_402 = (let _140_401 = (FStar_Format.text "let")
in (let _140_400 = (let _140_399 = (FStar_Format.text "rec")
in (_140_399)::[])
in (_140_401)::_140_400))
in (FStar_Format.reduce1 _140_402))
end else begin
(FStar_Format.text "let")
end
in (
# 570 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 571 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _140_406 = (let _140_405 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_140_405)::(doc)::[])
in (FStar_Format.reduce1 _140_406))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _61_526 -> (match (_61_526) with
| (lineno, file) -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FStar_Format.empty
end else begin
(
# 582 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _140_413 = (let _140_412 = (FStar_Format.text "#")
in (let _140_411 = (let _140_410 = (FStar_Format.num lineno)
in (let _140_409 = (let _140_408 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_140_408)::[])
in (_140_410)::_140_409))
in (_140_412)::_140_411))
in (FStar_Format.reduce1 _140_413)))
end
end))

# 586 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 587 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _61_534 -> (match (_61_534) with
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
| _61_539 -> begin
(
# 593 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _140_422 = (let _140_421 = (FStar_Format.text ", ")
in (FStar_Format.combine _140_421 doc))
in (FStar_Format.parens _140_422)))
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
let forfield = (fun _61_552 -> (match (_61_552) with
| (name, ty) -> begin
(
# 603 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 604 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _140_429 = (let _140_428 = (let _140_427 = (FStar_Format.text ":")
in (_140_427)::(ty)::[])
in (name)::_140_428)
in (FStar_Format.reduce1 _140_429))))
end))
in (let _140_432 = (let _140_431 = (FStar_Format.text "; ")
in (let _140_430 = (FStar_List.map forfield fields)
in (FStar_Format.combine _140_431 _140_430)))
in (FStar_Format.cbrackets _140_432)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 611 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _61_560 -> (match (_61_560) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _61_563 -> begin
(
# 615 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 616 "FStar.Extraction.ML.Code.fst"
let tys = (let _140_435 = (FStar_Format.text " * ")
in (FStar_Format.combine _140_435 tys))
in (let _140_439 = (let _140_438 = (FStar_Format.text name)
in (let _140_437 = (let _140_436 = (FStar_Format.text "of")
in (_140_436)::(tys)::[])
in (_140_438)::_140_437))
in (FStar_Format.reduce1 _140_439))))
end)
end))
in (
# 620 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 621 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _140_442 = (let _140_441 = (FStar_Format.text "|")
in (_140_441)::(d)::[])
in (FStar_Format.reduce1 _140_442))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 626 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_446 = (let _140_445 = (let _140_444 = (let _140_443 = (ptsym currentModule ([], x))
in (FStar_Format.text _140_443))
in (_140_444)::[])
in (tparams)::_140_445)
in (FStar_Format.reduce1 _140_446))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 631 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _140_451 = (let _140_450 = (let _140_449 = (let _140_448 = (let _140_447 = (FStar_Format.text "=")
in (_140_447)::[])
in (doc)::_140_448)
in (FStar_Format.reduce1 _140_449))
in (_140_450)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _140_451)))
end))))
end))
in (
# 636 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 637 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _140_456 = (let _140_455 = (FStar_Format.text "type")
in (let _140_454 = (let _140_453 = (let _140_452 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _140_452 doc))
in (_140_453)::[])
in (_140_455)::_140_454))
in (FStar_Format.reduce1 _140_456))
end else begin
(FStar_Format.text "")
end
in doc))))

# 641 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _140_476 = (let _140_475 = (let _140_468 = (let _140_467 = (FStar_Format.text "module")
in (let _140_466 = (let _140_465 = (FStar_Format.text x)
in (let _140_464 = (let _140_463 = (FStar_Format.text "=")
in (_140_463)::[])
in (_140_465)::_140_464))
in (_140_467)::_140_466))
in (FStar_Format.reduce1 _140_468))
in (let _140_474 = (let _140_473 = (doc_of_sig currentModule subsig)
in (let _140_472 = (let _140_471 = (let _140_470 = (let _140_469 = (FStar_Format.text "end")
in (_140_469)::[])
in (FStar_Format.reduce1 _140_470))
in (_140_471)::[])
in (_140_473)::_140_472))
in (_140_475)::_140_474))
in (FStar_Format.combine FStar_Format.hardline _140_476))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _140_480 = (let _140_479 = (FStar_Format.text "exception")
in (let _140_478 = (let _140_477 = (FStar_Format.text x)
in (_140_477)::[])
in (_140_479)::_140_478))
in (FStar_Format.reduce1 _140_480))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 653 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 654 "FStar.Extraction.ML.Code.fst"
let args = (let _140_482 = (let _140_481 = (FStar_Format.text " * ")
in (FStar_Format.combine _140_481 args))
in (FStar_Format.parens _140_482))
in (let _140_488 = (let _140_487 = (FStar_Format.text "exception")
in (let _140_486 = (let _140_485 = (FStar_Format.text x)
in (let _140_484 = (let _140_483 = (FStar_Format.text "of")
in (_140_483)::(args)::[])
in (_140_485)::_140_484))
in (_140_487)::_140_486))
in (FStar_Format.reduce1 _140_488))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_61_594, ty)) -> begin
(
# 658 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _140_494 = (let _140_493 = (FStar_Format.text "val")
in (let _140_492 = (let _140_491 = (FStar_Format.text x)
in (let _140_490 = (let _140_489 = (FStar_Format.text ": ")
in (_140_489)::(ty)::[])
in (_140_491)::_140_490))
in (_140_493)::_140_492))
in (FStar_Format.reduce1 _140_494)))
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
(let _140_505 = (let _140_504 = (FStar_Format.text "exception")
in (let _140_503 = (let _140_502 = (FStar_Format.text x)
in (_140_502)::[])
in (_140_504)::_140_503))
in (FStar_Format.reduce1 _140_505))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 678 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 679 "FStar.Extraction.ML.Code.fst"
let args = (let _140_507 = (let _140_506 = (FStar_Format.text " * ")
in (FStar_Format.combine _140_506 args))
in (FStar_Format.parens _140_507))
in (let _140_513 = (let _140_512 = (FStar_Format.text "exception")
in (let _140_511 = (let _140_510 = (FStar_Format.text x)
in (let _140_509 = (let _140_508 = (FStar_Format.text "of")
in (_140_508)::(args)::[])
in (_140_510)::_140_509))
in (_140_512)::_140_511))
in (FStar_Format.reduce1 _140_513))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _140_521 = (let _140_520 = (FStar_Format.text "let")
in (let _140_519 = (let _140_518 = (FStar_Format.text "_")
in (let _140_517 = (let _140_516 = (FStar_Format.text "=")
in (let _140_515 = (let _140_514 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_140_514)::[])
in (_140_516)::_140_515))
in (_140_518)::_140_517))
in (_140_520)::_140_519))
in (FStar_Format.reduce1 _140_521))
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
| FStar_Extraction_ML_Syntax.MLM_Loc (_61_634) -> begin
FStar_Format.empty
end
| _61_637 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 705 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _61_640 -> (match (_61_640) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 706 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _61_647 -> (match (_61_647) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 707 "FStar.Extraction.ML.Code.fst"
let head = (let _140_540 = (let _140_539 = (FStar_Format.text "module")
in (let _140_538 = (let _140_537 = (FStar_Format.text x)
in (let _140_536 = (let _140_535 = (FStar_Format.text ":")
in (let _140_534 = (let _140_533 = (FStar_Format.text "sig")
in (_140_533)::[])
in (_140_535)::_140_534))
in (_140_537)::_140_536))
in (_140_539)::_140_538))
in (FStar_Format.reduce1 _140_540))
in (
# 708 "FStar.Extraction.ML.Code.fst"
let tail = (let _140_542 = (let _140_541 = (FStar_Format.text "end")
in (_140_541)::[])
in (FStar_Format.reduce1 _140_542))
in (
# 709 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _61_653 -> (match (_61_653) with
| (s, _61_652) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 710 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 711 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _140_552 = (let _140_551 = (FStar_Format.cat head FStar_Format.hardline)
in (let _140_550 = (let _140_549 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _140_548 = (let _140_547 = (FStar_Format.reduce sub)
in (let _140_546 = (let _140_545 = (FStar_Format.cat tail FStar_Format.hardline)
in (_140_545)::[])
in (_140_547)::_140_546))
in (_140_549)::_140_548))
in (_140_551)::_140_550))
in (FStar_Format.reduce _140_552)))))))
end))
and for1_mod = (fun istop _61_666 -> (match (_61_666) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 722 "FStar.Extraction.ML.Code.fst"
let head = (let _140_565 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _140_557 = (FStar_Format.text "module")
in (let _140_556 = (let _140_555 = (FStar_Format.text x)
in (_140_555)::[])
in (_140_557)::_140_556))
end else begin
if (not (istop)) then begin
(let _140_564 = (FStar_Format.text "module")
in (let _140_563 = (let _140_562 = (FStar_Format.text x)
in (let _140_561 = (let _140_560 = (FStar_Format.text "=")
in (let _140_559 = (let _140_558 = (FStar_Format.text "struct")
in (_140_558)::[])
in (_140_560)::_140_559))
in (_140_562)::_140_561))
in (_140_564)::_140_563))
end else begin
[]
end
end
in (FStar_Format.reduce1 _140_565))
in (
# 727 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _140_567 = (let _140_566 = (FStar_Format.text "end")
in (_140_566)::[])
in (FStar_Format.reduce1 _140_567))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 730 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _61_672 -> (match (_61_672) with
| (_61_670, m) -> begin
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
(let _140_571 = (let _140_570 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _140_570 FStar_Format.hardline))
in (_140_571)::[])
end else begin
[]
end
in (let _140_583 = (let _140_582 = (let _140_581 = (let _140_580 = (let _140_579 = (FStar_Format.text "open Prims")
in (let _140_578 = (let _140_577 = (let _140_576 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _140_575 = (let _140_574 = (FStar_Format.reduce sub)
in (let _140_573 = (let _140_572 = (FStar_Format.cat tail FStar_Format.hardline)
in (_140_572)::[])
in (_140_574)::_140_573))
in (_140_576)::_140_575))
in (FStar_Format.hardline)::_140_577)
in (_140_579)::_140_578))
in (FStar_Format.hardline)::_140_580)
in (head)::_140_581)
in (FStar_List.append prefix _140_582))
in (FStar_All.pipe_left FStar_Format.reduce _140_583))))))))
end))
in (
# 749 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _61_684 -> (match (_61_684) with
| (x, s, m) -> begin
(let _140_585 = (for1_mod true (x, s, m))
in (x, _140_585))
end)) mllib)
in docs))
end))

# 753 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 757 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (
# 758 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_592 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _140_592 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 761 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (
# 762 "FStar.Extraction.ML.Code.fst"
let doc = (let _140_597 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _140_597 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





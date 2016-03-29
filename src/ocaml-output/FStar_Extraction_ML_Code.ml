
open Prims
# 30 "FStar.Extraction.ML.Code.fst"
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 33 "FStar.Extraction.ML.Code.fst"
let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Extraction.ML.Code.fst"
let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Extraction.ML.Code.fst"
let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Extraction.ML.Code.fst"
let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Extraction.ML.Code.fst"
let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 33 "FStar.Extraction.ML.Code.fst"
type fixity =
| Prefix
| Postfix
| Infix of assoc

# 34 "FStar.Extraction.ML.Code.fst"
let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Extraction.ML.Code.fst"
let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Extraction.ML.Code.fst"
let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 34 "FStar.Extraction.ML.Code.fst"
let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_63_3) -> begin
_63_3
end))

# 34 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 35 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 36 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 38 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 39 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 40 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 42 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 43 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 44 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 45 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 46 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 47 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 48 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 49 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 50 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 51 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 52 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 53 "FStar.Extraction.ML.Code.fst"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 54 "FStar.Extraction.ML.Code.fst"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 55 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 57 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 58 "FStar.Extraction.ML.Code.fst"
let rec in_ns = (fun x -> (match (x) with
| ([], _63_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_63_18, _63_20) -> begin
false
end))

# 67 "FStar.Extraction.ML.Code.fst"
let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (
# 71 "FStar.Extraction.ML.Code.fst"
let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(
# 74 "FStar.Extraction.ML.Code.fst"
let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (
# 75 "FStar.Extraction.ML.Code.fst"
let ns_len = (FStar_List.length ns)
in (
# 76 "FStar.Extraction.ML.Code.fst"
let found = (FStar_Util.find_map cg_libs (fun cg_path -> (
# 77 "FStar.Extraction.ML.Code.fst"
let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(
# 79 "FStar.Extraction.ML.Code.fst"
let _63_31 = (FStar_Util.first_N cg_len ns)
in (match (_63_31) with
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

# 86 "FStar.Extraction.ML.Code.fst"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _63_41 -> begin
(
# 93 "FStar.Extraction.ML.Code.fst"
let _63_44 = x
in (match (_63_44) with
| (ns, x) -> begin
(let _142_36 = (path_of_ns currentModule ns)
in (_142_36, x))
end))
end))

# 94 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _142_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _142_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 99 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 105 "FStar.Extraction.ML.Code.fst"
let _63_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_63_50) with
| (p, s) -> begin
(let _142_46 = (let _142_45 = (let _142_44 = (ptsym_of_symbol s)
in (_142_44)::[])
in (FStar_List.append p _142_45))
in (FStar_String.concat "." _142_46))
end))
end)

# 106 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 110 "FStar.Extraction.ML.Code.fst"
let _63_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_63_55) with
| (p, s) -> begin
(
# 111 "FStar.Extraction.ML.Code.fst"
let s = if ((let _142_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _142_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 112 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 130 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 137 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 140 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 148 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 152 "FStar.Extraction.ML.Code.fst"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _63_60 -> (match (_63_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _63_66 -> (match (_63_66) with
| (y, _63_63, _63_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 159 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 163 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _63_70 -> (match (_63_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _63_74 -> (match (_63_74) with
| (y, _63_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 170 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 174 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _63_78 -> (match (_63_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _63_82 -> (match (_63_82) with
| (y, _63_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 181 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 185 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _63_86 -> (match (_63_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _63_90 -> (match (_63_90) with
| (y, _63_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 192 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 196 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _63_94 inner doc -> (match (_63_94) with
| (outer, side) -> begin
(
# 200 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 201 "FStar.Extraction.ML.Code.fst"
let _63_103 = _inner
in (match (_63_103) with
| (pi, fi) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let _63_106 = _outer
in (match (_63_106) with
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
| (_63_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_63_134, _63_136) -> begin
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

# 215 "FStar.Extraction.ML.Code.fst"
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 219 "FStar.Extraction.ML.Code.fst"
let encode_char : Prims.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(
# 224 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.string_of_char c)
in (
# 225 "FStar.Extraction.ML.Code.fst"
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
| _63_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 240 "FStar.Extraction.ML.Code.fst"
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
# 258 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(
# 262 "FStar.Extraction.ML.Code.fst"
let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

# 263 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 270 "FStar.Extraction.ML.Code.fst"
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
# 277 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 278 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_107 = (let _142_106 = (let _142_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_105 doc))
in (FStar_Format.hbox _142_106))
in (FStar_Format.parens _142_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 282 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _63_198 -> begin
(
# 287 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _142_110 = (let _142_109 = (let _142_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_108 args))
in (FStar_Format.hbox _142_109))
in (FStar_Format.parens _142_110)))
end)
in (
# 292 "FStar.Extraction.ML.Code.fst"
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
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _63_204, t2) -> begin
(
# 302 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 303 "FStar.Extraction.ML.Code.fst"
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
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _142_125 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _142_125)))

# 312 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 318 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_148 = (let _142_147 = (let _142_146 = (FStar_Format.text "Prims.checked_cast")
in (_142_146)::(doc)::[])
in (FStar_Format.reduce _142_147))
in (FStar_Format.parens _142_148))
end else begin
(let _142_153 = (let _142_152 = (let _142_151 = (FStar_Format.text "Obj.magic ")
in (let _142_150 = (let _142_149 = (FStar_Format.parens doc)
in (_142_149)::[])
in (_142_151)::_142_150))
in (FStar_Format.reduce _142_152))
in (FStar_Format.parens _142_153))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 324 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 325 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _142_157 = (let _142_156 = (let _142_155 = (FStar_Format.text ";")
in (_142_155)::(FStar_Format.hardline)::[])
in (d)::_142_156)
in (FStar_Format.reduce _142_157))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _142_158 = (string_of_mlconstant c)
in (FStar_Format.text _142_158))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _63_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _142_159 = (ptsym currentModule path)
in (FStar_Format.text _142_159))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 338 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _63_244 -> (match (_63_244) with
| (name, e) -> begin
(
# 339 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_166 = (let _142_165 = (let _142_162 = (ptsym currentModule (path, name))
in (FStar_Format.text _142_162))
in (let _142_164 = (let _142_163 = (FStar_Format.text "=")
in (_142_163)::(doc)::[])
in (_142_165)::_142_164))
in (FStar_Format.reduce1 _142_166)))
end))
in (let _142_169 = (let _142_168 = (FStar_Format.text "; ")
in (let _142_167 = (FStar_List.map for1 fields)
in (FStar_Format.combine _142_168 _142_167)))
in (FStar_Format.cbrackets _142_169)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 345 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_171 = (let _142_170 = (as_standard_constructor ctor)
in (FStar_Option.get _142_170))
in (Prims.snd _142_171))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 353 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_173 = (let _142_172 = (as_standard_constructor ctor)
in (FStar_Option.get _142_172))
in (Prims.snd _142_173))
end else begin
(ptctor currentModule ctor)
end
in (
# 358 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 359 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _142_177 = (let _142_176 = (FStar_Format.parens x)
in (let _142_175 = (let _142_174 = (FStar_Format.text "::")
in (_142_174)::(xs)::[])
in (_142_176)::_142_175))
in (FStar_Format.reduce _142_177))
end
| (_63_263, _63_265) -> begin
(let _142_183 = (let _142_182 = (FStar_Format.text name)
in (let _142_181 = (let _142_180 = (let _142_179 = (let _142_178 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_178 args))
in (FStar_Format.parens _142_179))
in (_142_180)::[])
in (_142_182)::_142_181))
in (FStar_Format.reduce1 _142_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 367 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 368 "FStar.Extraction.ML.Code.fst"
let docs = (let _142_185 = (let _142_184 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_184 docs))
in (FStar_Format.parens _142_185))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 372 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _142_188 = (let _142_187 = (let _142_186 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_142_186)::[])
in (FStar_Format.hardline)::_142_187)
in (FStar_Format.reduce _142_188))
end else begin
FStar_Format.empty
end
in (
# 377 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 378 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _142_195 = (let _142_194 = (let _142_193 = (let _142_192 = (let _142_191 = (let _142_190 = (let _142_189 = (FStar_Format.text "in")
in (_142_189)::(body)::[])
in (FStar_Format.reduce1 _142_190))
in (_142_191)::[])
in (doc)::_142_192)
in (pre)::_142_193)
in (FStar_Format.combine FStar_Format.hardline _142_194))
in (FStar_Format.parens _142_195)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (_63_305::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _63_303; FStar_Extraction_ML_Syntax.loc = _63_301}::{FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((arg, _63_293)::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _63_290; FStar_Extraction_ML_Syntax.loc = _63_288}::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(
# 387 "FStar.Extraction.ML.Code.fst"
let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _63_320; FStar_Extraction_ML_Syntax.loc = _63_318}, branches); FStar_Extraction_ML_Syntax.mlty = _63_316; FStar_Extraction_ML_Syntax.loc = _63_314} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _63_339; FStar_Extraction_ML_Syntax.loc = _63_337}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _63_359; FStar_Extraction_ML_Syntax.loc = _63_357}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _63_371 -> begin
(
# 410 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 411 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _142_196 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _142_196))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 416 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 417 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_201 = (let _142_200 = (let _142_199 = (FStar_Format.text ".")
in (let _142_198 = (let _142_197 = (FStar_Format.text (Prims.snd f))
in (_142_197)::[])
in (_142_199)::_142_198))
in (e)::_142_200)
in (FStar_Format.reduce _142_201))
end else begin
(let _142_207 = (let _142_206 = (let _142_205 = (FStar_Format.text ".")
in (let _142_204 = (let _142_203 = (let _142_202 = (ptsym currentModule f)
in (FStar_Format.text _142_202))
in (_142_203)::[])
in (_142_205)::_142_204))
in (e)::_142_206)
in (FStar_Format.reduce _142_207))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 424 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_223 = (let _142_222 = (FStar_Format.text "(")
in (let _142_221 = (let _142_220 = (FStar_Format.text x)
in (let _142_219 = (let _142_218 = (match (xt) with
| Some (xxt) -> begin
(let _142_215 = (let _142_214 = (FStar_Format.text " : ")
in (let _142_213 = (let _142_212 = (doc_of_mltype currentModule outer xxt)
in (_142_212)::[])
in (_142_214)::_142_213))
in (FStar_Format.reduce1 _142_215))
end
| _63_390 -> begin
(FStar_Format.text "")
end)
in (let _142_217 = (let _142_216 = (FStar_Format.text ")")
in (_142_216)::[])
in (_142_218)::_142_217))
in (_142_220)::_142_219))
in (_142_222)::_142_221))
in (FStar_Format.reduce1 _142_223))
end else begin
(FStar_Format.text x)
end)
in (
# 430 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _63_396 -> (match (_63_396) with
| ((x, _63_393), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 431 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 432 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_230 = (let _142_229 = (FStar_Format.text "fun")
in (let _142_228 = (let _142_227 = (FStar_Format.reduce1 ids)
in (let _142_226 = (let _142_225 = (FStar_Format.text "->")
in (_142_225)::(body)::[])
in (_142_227)::_142_226))
in (_142_229)::_142_228))
in (FStar_Format.reduce1 _142_230))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 436 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 437 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_243 = (let _142_242 = (let _142_237 = (let _142_236 = (FStar_Format.text "if")
in (let _142_235 = (let _142_234 = (let _142_233 = (FStar_Format.text "then")
in (let _142_232 = (let _142_231 = (FStar_Format.text "begin")
in (_142_231)::[])
in (_142_233)::_142_232))
in (cond)::_142_234)
in (_142_236)::_142_235))
in (FStar_Format.reduce1 _142_237))
in (let _142_241 = (let _142_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _142_239 = (let _142_238 = (FStar_Format.text "end")
in (_142_238)::[])
in (_142_240)::_142_239))
in (_142_242)::_142_241))
in (FStar_Format.combine FStar_Format.hardline _142_243))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 447 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 448 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_266 = (let _142_265 = (let _142_250 = (let _142_249 = (FStar_Format.text "if")
in (let _142_248 = (let _142_247 = (let _142_246 = (FStar_Format.text "then")
in (let _142_245 = (let _142_244 = (FStar_Format.text "begin")
in (_142_244)::[])
in (_142_246)::_142_245))
in (cond)::_142_247)
in (_142_249)::_142_248))
in (FStar_Format.reduce1 _142_250))
in (let _142_264 = (let _142_263 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _142_262 = (let _142_261 = (let _142_256 = (let _142_255 = (FStar_Format.text "end")
in (let _142_254 = (let _142_253 = (FStar_Format.text "else")
in (let _142_252 = (let _142_251 = (FStar_Format.text "begin")
in (_142_251)::[])
in (_142_253)::_142_252))
in (_142_255)::_142_254))
in (FStar_Format.reduce1 _142_256))
in (let _142_260 = (let _142_259 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _142_258 = (let _142_257 = (FStar_Format.text "end")
in (_142_257)::[])
in (_142_259)::_142_258))
in (_142_261)::_142_260))
in (_142_263)::_142_262))
in (_142_265)::_142_264))
in (FStar_Format.combine FStar_Format.hardline _142_266))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 460 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 461 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 462 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_273 = (let _142_272 = (let _142_271 = (FStar_Format.text "match")
in (let _142_270 = (let _142_269 = (FStar_Format.parens cond)
in (let _142_268 = (let _142_267 = (FStar_Format.text "with")
in (_142_267)::[])
in (_142_269)::_142_268))
in (_142_271)::_142_270))
in (FStar_Format.reduce1 _142_272))
in (_142_273)::pats)
in (
# 463 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _142_278 = (let _142_277 = (FStar_Format.text "raise")
in (let _142_276 = (let _142_275 = (let _142_274 = (ptctor currentModule exn)
in (FStar_Format.text _142_274))
in (_142_275)::[])
in (_142_277)::_142_276))
in (FStar_Format.reduce1 _142_278))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 471 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _142_287 = (let _142_286 = (FStar_Format.text "raise")
in (let _142_285 = (let _142_284 = (let _142_279 = (ptctor currentModule exn)
in (FStar_Format.text _142_279))
in (let _142_283 = (let _142_282 = (let _142_281 = (let _142_280 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_280 args))
in (FStar_Format.parens _142_281))
in (_142_282)::[])
in (_142_284)::_142_283))
in (_142_286)::_142_285))
in (FStar_Format.reduce1 _142_287)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _142_296 = (let _142_295 = (FStar_Format.text "try")
in (let _142_294 = (let _142_293 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_292 = (let _142_291 = (FStar_Format.text "with")
in (let _142_290 = (let _142_289 = (let _142_288 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _142_288))
in (_142_289)::[])
in (_142_291)::_142_290))
in (_142_293)::_142_292))
in (_142_295)::_142_294))
in (FStar_Format.combine FStar_Format.hardline _142_296))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 482 "FStar.Extraction.ML.Code.fst"
let _63_444 = (let _142_301 = (as_bin_op p)
in (FStar_Option.get _142_301))
in (match (_63_444) with
| (_63_441, prio, txt) -> begin
(
# 483 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 484 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 485 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_304 = (let _142_303 = (let _142_302 = (FStar_Format.text txt)
in (_142_302)::(e2)::[])
in (e1)::_142_303)
in (FStar_Format.reduce1 _142_304))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 489 "FStar.Extraction.ML.Code.fst"
let _63_454 = (let _142_308 = (as_uni_op p)
in (FStar_Option.get _142_308))
in (match (_63_454) with
| (_63_452, txt) -> begin
(
# 490 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 491 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_312 = (let _142_311 = (FStar_Format.text txt)
in (let _142_310 = (let _142_309 = (FStar_Format.parens e1)
in (_142_309)::[])
in (_142_311)::_142_310))
in (FStar_Format.reduce1 _142_312))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _142_315 = (string_of_mlconstant c)
in (FStar_Format.text _142_315))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 501 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _63_471 -> (match (_63_471) with
| (name, p) -> begin
(let _142_324 = (let _142_323 = (let _142_318 = (ptsym currentModule (path, name))
in (FStar_Format.text _142_318))
in (let _142_322 = (let _142_321 = (FStar_Format.text "=")
in (let _142_320 = (let _142_319 = (doc_of_pattern currentModule p)
in (_142_319)::[])
in (_142_321)::_142_320))
in (_142_323)::_142_322))
in (FStar_Format.reduce1 _142_324))
end))
in (let _142_327 = (let _142_326 = (FStar_Format.text "; ")
in (let _142_325 = (FStar_List.map for1 fields)
in (FStar_Format.combine _142_326 _142_325)))
in (FStar_Format.cbrackets _142_327)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 505 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_329 = (let _142_328 = (as_standard_constructor ctor)
in (FStar_Option.get _142_328))
in (Prims.snd _142_329))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 513 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _142_331 = (let _142_330 = (as_standard_constructor ctor)
in (FStar_Option.get _142_330))
in (Prims.snd _142_331))
end else begin
(ptctor currentModule ctor)
end
in (
# 518 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _142_337 = (let _142_336 = (doc_of_pattern currentModule x)
in (let _142_335 = (let _142_334 = (FStar_Format.text "::")
in (let _142_333 = (let _142_332 = (doc_of_pattern currentModule xs)
in (_142_332)::[])
in (_142_334)::_142_333))
in (_142_336)::_142_335))
in (FStar_Format.reduce _142_337))
end
| (_63_488, FStar_Extraction_ML_Syntax.MLP_Tuple (_63_490)::[]) -> begin
(let _142_342 = (let _142_341 = (FStar_Format.text name)
in (let _142_340 = (let _142_339 = (let _142_338 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _142_338))
in (_142_339)::[])
in (_142_341)::_142_340))
in (FStar_Format.reduce1 _142_342))
end
| _63_495 -> begin
(let _142_349 = (let _142_348 = (FStar_Format.text name)
in (let _142_347 = (let _142_346 = (let _142_345 = (let _142_344 = (FStar_Format.text ", ")
in (let _142_343 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _142_344 _142_343)))
in (FStar_Format.parens _142_345))
in (_142_346)::[])
in (_142_348)::_142_347))
in (FStar_Format.reduce1 _142_349))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 527 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _142_351 = (let _142_350 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_350 ps))
in (FStar_Format.parens _142_351)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 531 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 532 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _142_352 = (FStar_Format.text " | ")
in (FStar_Format.combine _142_352 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _63_508 -> (match (_63_508) with
| (p, cond, e) -> begin
(
# 537 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _142_358 = (let _142_357 = (FStar_Format.text "|")
in (let _142_356 = (let _142_355 = (doc_of_pattern currentModule p)
in (_142_355)::[])
in (_142_357)::_142_356))
in (FStar_Format.reduce1 _142_358))
end
| Some (c) -> begin
(
# 541 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _142_364 = (let _142_363 = (FStar_Format.text "|")
in (let _142_362 = (let _142_361 = (doc_of_pattern currentModule p)
in (let _142_360 = (let _142_359 = (FStar_Format.text "when")
in (_142_359)::(c)::[])
in (_142_361)::_142_360))
in (_142_363)::_142_362))
in (FStar_Format.reduce1 _142_364)))
end)
in (let _142_375 = (let _142_374 = (let _142_369 = (let _142_368 = (let _142_367 = (FStar_Format.text "->")
in (let _142_366 = (let _142_365 = (FStar_Format.text "begin")
in (_142_365)::[])
in (_142_367)::_142_366))
in (case)::_142_368)
in (FStar_Format.reduce1 _142_369))
in (let _142_373 = (let _142_372 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _142_371 = (let _142_370 = (FStar_Format.text "end")
in (_142_370)::[])
in (_142_372)::_142_371))
in (_142_374)::_142_373))
in (FStar_Format.combine FStar_Format.hardline _142_375)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _63_518 -> (match (_63_518) with
| (rec_, top_level, lets) -> begin
(
# 552 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _63_526 -> (match (_63_526) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _63_523; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 553 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 554 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 558 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _63_532 -> (match (_63_532) with
| (x, _63_531) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 559 "FStar.Extraction.ML.Code.fst"
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
# 567 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _142_382 = (let _142_381 = (FStar_Format.text ":")
in (_142_381)::(ty)::[])
in (FStar_Format.reduce1 _142_382)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 578 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _142_384 = (let _142_383 = (FStar_Format.text ":")
in (_142_383)::(ty)::[])
in (FStar_Format.reduce1 _142_384)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _142_391 = (let _142_390 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _142_389 = (let _142_388 = (FStar_Format.reduce1 ids)
in (let _142_387 = (let _142_386 = (let _142_385 = (FStar_Format.text "=")
in (_142_385)::(e)::[])
in (ty_annot)::_142_386)
in (_142_388)::_142_387))
in (_142_390)::_142_389))
in (FStar_Format.reduce1 _142_391))))))
end))
in (
# 584 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _142_395 = (let _142_394 = (FStar_Format.text "let")
in (let _142_393 = (let _142_392 = (FStar_Format.text "rec")
in (_142_392)::[])
in (_142_394)::_142_393))
in (FStar_Format.reduce1 _142_395))
end else begin
(FStar_Format.text "let")
end
in (
# 586 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 587 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _142_399 = (let _142_398 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_142_398)::(doc)::[])
in (FStar_Format.reduce1 _142_399))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _63_572 -> (match (_63_572) with
| (lineno, file) -> begin
if ((FStar_ST.read FStar_Options.no_location_info) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 598 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _142_406 = (let _142_405 = (FStar_Format.text "#")
in (let _142_404 = (let _142_403 = (FStar_Format.num lineno)
in (let _142_402 = (let _142_401 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_142_401)::[])
in (_142_403)::_142_402))
in (_142_405)::_142_404))
in (FStar_Format.reduce1 _142_406)))
end
end))

# 599 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 603 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _63_580 -> (match (_63_580) with
| (x, tparams, body) -> begin
(
# 604 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _63_585 -> begin
(
# 609 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _142_415 = (let _142_414 = (FStar_Format.text ", ")
in (FStar_Format.combine _142_414 doc))
in (FStar_Format.parens _142_415)))
end)
in (
# 612 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 618 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _63_598 -> (match (_63_598) with
| (name, ty) -> begin
(
# 619 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 620 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _142_422 = (let _142_421 = (let _142_420 = (FStar_Format.text ":")
in (_142_420)::(ty)::[])
in (name)::_142_421)
in (FStar_Format.reduce1 _142_422))))
end))
in (let _142_425 = (let _142_424 = (FStar_Format.text "; ")
in (let _142_423 = (FStar_List.map forfield fields)
in (FStar_Format.combine _142_424 _142_423)))
in (FStar_Format.cbrackets _142_425)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 627 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _63_606 -> (match (_63_606) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _63_609 -> begin
(
# 631 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 632 "FStar.Extraction.ML.Code.fst"
let tys = (let _142_428 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_428 tys))
in (let _142_432 = (let _142_431 = (FStar_Format.text name)
in (let _142_430 = (let _142_429 = (FStar_Format.text "of")
in (_142_429)::(tys)::[])
in (_142_431)::_142_430))
in (FStar_Format.reduce1 _142_432))))
end)
end))
in (
# 636 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 637 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _142_435 = (let _142_434 = (FStar_Format.text "|")
in (_142_434)::(d)::[])
in (FStar_Format.reduce1 _142_435))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 642 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_439 = (let _142_438 = (let _142_437 = (let _142_436 = (ptsym currentModule ([], x))
in (FStar_Format.text _142_436))
in (_142_437)::[])
in (tparams)::_142_438)
in (FStar_Format.reduce1 _142_439))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 647 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _142_444 = (let _142_443 = (let _142_442 = (let _142_441 = (let _142_440 = (FStar_Format.text "=")
in (_142_440)::[])
in (doc)::_142_441)
in (FStar_Format.reduce1 _142_442))
in (_142_443)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _142_444)))
end))))
end))
in (
# 652 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 653 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _142_449 = (let _142_448 = (FStar_Format.text "type")
in (let _142_447 = (let _142_446 = (let _142_445 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _142_445 doc))
in (_142_446)::[])
in (_142_448)::_142_447))
in (FStar_Format.reduce1 _142_449))
end else begin
(FStar_Format.text "")
end
in doc))))

# 654 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _142_469 = (let _142_468 = (let _142_461 = (let _142_460 = (FStar_Format.text "module")
in (let _142_459 = (let _142_458 = (FStar_Format.text x)
in (let _142_457 = (let _142_456 = (FStar_Format.text "=")
in (_142_456)::[])
in (_142_458)::_142_457))
in (_142_460)::_142_459))
in (FStar_Format.reduce1 _142_461))
in (let _142_467 = (let _142_466 = (doc_of_sig currentModule subsig)
in (let _142_465 = (let _142_464 = (let _142_463 = (let _142_462 = (FStar_Format.text "end")
in (_142_462)::[])
in (FStar_Format.reduce1 _142_463))
in (_142_464)::[])
in (_142_466)::_142_465))
in (_142_468)::_142_467))
in (FStar_Format.combine FStar_Format.hardline _142_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _142_473 = (let _142_472 = (FStar_Format.text "exception")
in (let _142_471 = (let _142_470 = (FStar_Format.text x)
in (_142_470)::[])
in (_142_472)::_142_471))
in (FStar_Format.reduce1 _142_473))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 669 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 670 "FStar.Extraction.ML.Code.fst"
let args = (let _142_475 = (let _142_474 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_474 args))
in (FStar_Format.parens _142_475))
in (let _142_481 = (let _142_480 = (FStar_Format.text "exception")
in (let _142_479 = (let _142_478 = (FStar_Format.text x)
in (let _142_477 = (let _142_476 = (FStar_Format.text "of")
in (_142_476)::(args)::[])
in (_142_478)::_142_477))
in (_142_480)::_142_479))
in (FStar_Format.reduce1 _142_481))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_63_640, ty)) -> begin
(
# 674 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _142_487 = (let _142_486 = (FStar_Format.text "val")
in (let _142_485 = (let _142_484 = (FStar_Format.text x)
in (let _142_483 = (let _142_482 = (FStar_Format.text ": ")
in (_142_482)::(ty)::[])
in (_142_484)::_142_483))
in (_142_486)::_142_485))
in (FStar_Format.reduce1 _142_487)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 682 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 683 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 684 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _142_498 = (let _142_497 = (FStar_Format.text "exception")
in (let _142_496 = (let _142_495 = (FStar_Format.text x)
in (_142_495)::[])
in (_142_497)::_142_496))
in (FStar_Format.reduce1 _142_498))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 694 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 695 "FStar.Extraction.ML.Code.fst"
let args = (let _142_500 = (let _142_499 = (FStar_Format.text " * ")
in (FStar_Format.combine _142_499 args))
in (FStar_Format.parens _142_500))
in (let _142_506 = (let _142_505 = (FStar_Format.text "exception")
in (let _142_504 = (let _142_503 = (FStar_Format.text x)
in (let _142_502 = (let _142_501 = (FStar_Format.text "of")
in (_142_501)::(args)::[])
in (_142_503)::_142_502))
in (_142_505)::_142_504))
in (FStar_Format.reduce1 _142_506))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _142_514 = (let _142_513 = (FStar_Format.text "let")
in (let _142_512 = (let _142_511 = (FStar_Format.text "_")
in (let _142_510 = (let _142_509 = (FStar_Format.text "=")
in (let _142_508 = (let _142_507 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_142_507)::[])
in (_142_509)::_142_508))
in (_142_511)::_142_510))
in (_142_513)::_142_512))
in (FStar_Format.reduce1 _142_514))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 711 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 715 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 716 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_63_680) -> begin
FStar_Format.empty
end
| _63_683 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 718 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _63_686 -> (match (_63_686) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 722 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _63_693 -> (match (_63_693) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 723 "FStar.Extraction.ML.Code.fst"
let head = (let _142_533 = (let _142_532 = (FStar_Format.text "module")
in (let _142_531 = (let _142_530 = (FStar_Format.text x)
in (let _142_529 = (let _142_528 = (FStar_Format.text ":")
in (let _142_527 = (let _142_526 = (FStar_Format.text "sig")
in (_142_526)::[])
in (_142_528)::_142_527))
in (_142_530)::_142_529))
in (_142_532)::_142_531))
in (FStar_Format.reduce1 _142_533))
in (
# 724 "FStar.Extraction.ML.Code.fst"
let tail = (let _142_535 = (let _142_534 = (FStar_Format.text "end")
in (_142_534)::[])
in (FStar_Format.reduce1 _142_535))
in (
# 725 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _63_699 -> (match (_63_699) with
| (s, _63_698) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 726 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 727 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _142_545 = (let _142_544 = (FStar_Format.cat head FStar_Format.hardline)
in (let _142_543 = (let _142_542 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _142_541 = (let _142_540 = (FStar_Format.reduce sub)
in (let _142_539 = (let _142_538 = (FStar_Format.cat tail FStar_Format.hardline)
in (_142_538)::[])
in (_142_540)::_142_539))
in (_142_542)::_142_541))
in (_142_544)::_142_543))
in (FStar_Format.reduce _142_545)))))))
end))
and for1_mod = (fun istop _63_712 -> (match (_63_712) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 738 "FStar.Extraction.ML.Code.fst"
let head = (let _142_558 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_550 = (FStar_Format.text "module")
in (let _142_549 = (let _142_548 = (FStar_Format.text x)
in (_142_548)::[])
in (_142_550)::_142_549))
end else begin
if (not (istop)) then begin
(let _142_557 = (FStar_Format.text "module")
in (let _142_556 = (let _142_555 = (FStar_Format.text x)
in (let _142_554 = (let _142_553 = (FStar_Format.text "=")
in (let _142_552 = (let _142_551 = (FStar_Format.text "struct")
in (_142_551)::[])
in (_142_553)::_142_552))
in (_142_555)::_142_554))
in (_142_557)::_142_556))
end else begin
[]
end
end
in (FStar_Format.reduce1 _142_558))
in (
# 743 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _142_560 = (let _142_559 = (FStar_Format.text "end")
in (_142_559)::[])
in (FStar_Format.reduce1 _142_560))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 746 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _63_718 -> (match (_63_718) with
| (_63_716, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 747 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 748 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 749 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _142_564 = (let _142_563 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _142_563 FStar_Format.hardline))
in (_142_564)::[])
end else begin
[]
end
in (let _142_576 = (let _142_575 = (let _142_574 = (let _142_573 = (let _142_572 = (FStar_Format.text "open Prims")
in (let _142_571 = (let _142_570 = (let _142_569 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _142_568 = (let _142_567 = (FStar_Format.reduce sub)
in (let _142_566 = (let _142_565 = (FStar_Format.cat tail FStar_Format.hardline)
in (_142_565)::[])
in (_142_567)::_142_566))
in (_142_569)::_142_568))
in (FStar_Format.hardline)::_142_570)
in (_142_572)::_142_571))
in (FStar_Format.hardline)::_142_573)
in (head)::_142_574)
in (FStar_List.append prefix _142_575))
in (FStar_All.pipe_left FStar_Format.reduce _142_576))))))))
end))
in (
# 765 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _63_730 -> (match (_63_730) with
| (x, s, m) -> begin
(let _142_578 = (for1_mod true (x, s, m))
in (x, _142_578))
end)) mllib)
in docs))
end))

# 766 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 770 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 773 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_585 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _142_585 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 774 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 777 "FStar.Extraction.ML.Code.fst"
let doc = (let _142_590 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _142_590 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))






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
| Infix (_69_3) -> begin
_69_3
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
| ([], _69_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_69_18, _69_20) -> begin
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
let _69_31 = (FStar_Util.first_N cg_len ns)
in (match (_69_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _154_31 = (let _154_30 = (let _154_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_154_29)::[])
in (FStar_List.append pfx _154_30))
in Some (_154_31))
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
| _69_41 -> begin
(
# 95 "FStar.Extraction.ML.Code.fst"
let _69_44 = x
in (match (_69_44) with
| (ns, x) -> begin
(let _154_36 = (path_of_ns currentModule ns)
in (_154_36, x))
end))
end))

# 96 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _154_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _154_39)) <> (FStar_String.get s 0)) then begin
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
let _69_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_69_50) with
| (p, s) -> begin
(let _154_46 = (let _154_45 = (let _154_44 = (ptsym_of_symbol s)
in (_154_44)::[])
in (FStar_List.append p _154_45))
in (FStar_String.concat "." _154_46))
end))
end)

# 108 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 112 "FStar.Extraction.ML.Code.fst"
let _69_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_69_55) with
| (p, s) -> begin
(
# 113 "FStar.Extraction.ML.Code.fst"
let s = if ((let _154_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _154_51)) <> (FStar_String.get s 0)) then begin
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
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _69_60 -> (match (_69_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _69_66 -> (match (_69_66) with
| (y, _69_63, _69_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 161 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 165 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _69_70 -> (match (_69_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _69_74 -> (match (_69_74) with
| (y, _69_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 172 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 176 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _69_78 -> (match (_69_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _69_82 -> (match (_69_82) with
| (y, _69_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 183 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 187 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _69_86 -> (match (_69_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _69_90 -> (match (_69_90) with
| (y, _69_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 194 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 198 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _69_94 inner doc -> (match (_69_94) with
| (outer, side) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 203 "FStar.Extraction.ML.Code.fst"
let _69_103 = _inner
in (match (_69_103) with
| (pi, fi) -> begin
(
# 204 "FStar.Extraction.ML.Code.fst"
let _69_106 = _outer
in (match (_69_106) with
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
| (_69_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_69_134, _69_136) -> begin
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
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 221 "FStar.Extraction.ML.Code.fst"
let encode_char : Prims.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(
# 226 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Util.string_of_char c)
in (
# 227 "FStar.Extraction.ML.Code.fst"
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
| _69_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 242 "FStar.Extraction.ML.Code.fst"
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
(let _154_92 = (let _154_91 = (encode_char c)
in (Prims.strcat "\'" _154_91))
in (Prims.strcat _154_92 "\'"))
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
# 260 "FStar.Extraction.ML.Code.fst"
let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(
# 264 "FStar.Extraction.ML.Code.fst"
let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

# 265 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 272 "FStar.Extraction.ML.Code.fst"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _154_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _154_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 279 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 280 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_107 = (let _154_106 = (let _154_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_105 doc))
in (FStar_Format.hbox _154_106))
in (FStar_Format.parens _154_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 284 "FStar.Extraction.ML.Code.fst"
let args = (match (args) with
| [] -> begin
FStar_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _69_198 -> begin
(
# 289 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _154_110 = (let _154_109 = (let _154_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_108 args))
in (FStar_Format.hbox _154_109))
in (FStar_Format.parens _154_110)))
end)
in (
# 294 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _154_112 = (let _154_111 = (as_standard_type name)
in (FStar_Option.get _154_111))
in (Prims.snd _154_112))
end else begin
(ptsym currentModule name)
end
in (let _154_116 = (let _154_115 = (let _154_114 = (let _154_113 = (FStar_Format.text name)
in (_154_113)::[])
in (args)::_154_114)
in (FStar_Format.reduce1 _154_115))
in (FStar_Format.hbox _154_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _69_204, t2) -> begin
(
# 304 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 305 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _154_121 = (let _154_120 = (let _154_119 = (let _154_118 = (let _154_117 = (FStar_Format.text " -> ")
in (_154_117)::(d2)::[])
in (d1)::_154_118)
in (FStar_Format.reduce1 _154_119))
in (FStar_Format.hbox _154_120))
in (maybe_paren outer t_prio_fun _154_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (let _154_125 = (FStar_Extraction_ML_Util.resugar_mlty ty)
in (doc_of_mltype' currentModule outer _154_125)))

# 314 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 320 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_148 = (let _154_147 = (let _154_146 = (FStar_Format.text "Prims.checked_cast")
in (_154_146)::(doc)::[])
in (FStar_Format.reduce _154_147))
in (FStar_Format.parens _154_148))
end else begin
(let _154_153 = (let _154_152 = (let _154_151 = (FStar_Format.text "Obj.magic ")
in (let _154_150 = (let _154_149 = (FStar_Format.parens doc)
in (_154_149)::[])
in (_154_151)::_154_150))
in (FStar_Format.reduce _154_152))
in (FStar_Format.parens _154_153))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 326 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 327 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _154_157 = (let _154_156 = (let _154_155 = (FStar_Format.text ";")
in (_154_155)::(FStar_Format.hardline)::[])
in (d)::_154_156)
in (FStar_Format.reduce _154_157))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _154_158 = (string_of_mlconstant c)
in (FStar_Format.text _154_158))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _69_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _154_159 = (ptsym currentModule path)
in (FStar_Format.text _154_159))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 340 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_244 -> (match (_69_244) with
| (name, e) -> begin
(
# 341 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _154_166 = (let _154_165 = (let _154_162 = (ptsym currentModule (path, name))
in (FStar_Format.text _154_162))
in (let _154_164 = (let _154_163 = (FStar_Format.text "=")
in (_154_163)::(doc)::[])
in (_154_165)::_154_164))
in (FStar_Format.reduce1 _154_166)))
end))
in (let _154_169 = (let _154_168 = (FStar_Format.text "; ")
in (let _154_167 = (FStar_List.map for1 fields)
in (FStar_Format.combine _154_168 _154_167)))
in (FStar_Format.cbrackets _154_169)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 347 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_171 = (let _154_170 = (as_standard_constructor ctor)
in (FStar_Option.get _154_170))
in (Prims.snd _154_171))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 355 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_173 = (let _154_172 = (as_standard_constructor ctor)
in (FStar_Option.get _154_172))
in (Prims.snd _154_173))
end else begin
(ptctor currentModule ctor)
end
in (
# 360 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 361 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _154_177 = (let _154_176 = (FStar_Format.parens x)
in (let _154_175 = (let _154_174 = (FStar_Format.text "::")
in (_154_174)::(xs)::[])
in (_154_176)::_154_175))
in (FStar_Format.reduce _154_177))
end
| (_69_263, _69_265) -> begin
(let _154_183 = (let _154_182 = (FStar_Format.text name)
in (let _154_181 = (let _154_180 = (let _154_179 = (let _154_178 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_178 args))
in (FStar_Format.parens _154_179))
in (_154_180)::[])
in (_154_182)::_154_181))
in (FStar_Format.reduce1 _154_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 369 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 370 "FStar.Extraction.ML.Code.fst"
let docs = (let _154_185 = (let _154_184 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_184 docs))
in (FStar_Format.parens _154_185))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 374 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _154_188 = (let _154_187 = (let _154_186 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_154_186)::[])
in (FStar_Format.hardline)::_154_187)
in (FStar_Format.reduce _154_188))
end else begin
FStar_Format.empty
end
in (
# 379 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 380 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _154_195 = (let _154_194 = (let _154_193 = (let _154_192 = (let _154_191 = (let _154_190 = (let _154_189 = (FStar_Format.text "in")
in (_154_189)::(body)::[])
in (FStar_Format.reduce1 _154_190))
in (_154_191)::[])
in (doc)::_154_192)
in (pre)::_154_193)
in (FStar_Format.combine FStar_Format.hardline _154_194))
in (FStar_Format.parens _154_195)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun (_69_305::[], scrutinee); FStar_Extraction_ML_Syntax.mlty = _69_303; FStar_Extraction_ML_Syntax.loc = _69_301}::{FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Fun ((arg, _69_293)::[], possible_match); FStar_Extraction_ML_Syntax.mlty = _69_290; FStar_Extraction_ML_Syntax.loc = _69_288}::[]) when ((FStar_Extraction_ML_Syntax.string_of_mlpath p) = "FStar.All.try_with") -> begin
(
# 389 "FStar.Extraction.ML.Code.fst"
let branches = (match (possible_match) with
| {FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Match ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Var (arg'); FStar_Extraction_ML_Syntax.mlty = _69_320; FStar_Extraction_ML_Syntax.loc = _69_318}, branches); FStar_Extraction_ML_Syntax.mlty = _69_316; FStar_Extraction_ML_Syntax.loc = _69_314} when ((FStar_Extraction_ML_Syntax.idsym arg) = (FStar_Extraction_ML_Syntax.idsym arg')) -> begin
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
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _69_339; FStar_Extraction_ML_Syntax.loc = _69_337}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _69_359; FStar_Extraction_ML_Syntax.loc = _69_357}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _69_371 -> begin
(
# 412 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 413 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _154_196 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _154_196))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 418 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 419 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_201 = (let _154_200 = (let _154_199 = (FStar_Format.text ".")
in (let _154_198 = (let _154_197 = (FStar_Format.text (Prims.snd f))
in (_154_197)::[])
in (_154_199)::_154_198))
in (e)::_154_200)
in (FStar_Format.reduce _154_201))
end else begin
(let _154_207 = (let _154_206 = (let _154_205 = (FStar_Format.text ".")
in (let _154_204 = (let _154_203 = (let _154_202 = (ptsym currentModule f)
in (FStar_Format.text _154_202))
in (_154_203)::[])
in (_154_205)::_154_204))
in (e)::_154_206)
in (FStar_Format.reduce _154_207))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 426 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_223 = (let _154_222 = (FStar_Format.text "(")
in (let _154_221 = (let _154_220 = (FStar_Format.text x)
in (let _154_219 = (let _154_218 = (match (xt) with
| Some (xxt) -> begin
(let _154_215 = (let _154_214 = (FStar_Format.text " : ")
in (let _154_213 = (let _154_212 = (doc_of_mltype currentModule outer xxt)
in (_154_212)::[])
in (_154_214)::_154_213))
in (FStar_Format.reduce1 _154_215))
end
| _69_390 -> begin
(FStar_Format.text "")
end)
in (let _154_217 = (let _154_216 = (FStar_Format.text ")")
in (_154_216)::[])
in (_154_218)::_154_217))
in (_154_220)::_154_219))
in (_154_222)::_154_221))
in (FStar_Format.reduce1 _154_223))
end else begin
(FStar_Format.text x)
end)
in (
# 432 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _69_396 -> (match (_69_396) with
| ((x, _69_393), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 433 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 434 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_230 = (let _154_229 = (FStar_Format.text "fun")
in (let _154_228 = (let _154_227 = (FStar_Format.reduce1 ids)
in (let _154_226 = (let _154_225 = (FStar_Format.text "->")
in (_154_225)::(body)::[])
in (_154_227)::_154_226))
in (_154_229)::_154_228))
in (FStar_Format.reduce1 _154_230))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 438 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 439 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_243 = (let _154_242 = (let _154_237 = (let _154_236 = (FStar_Format.text "if")
in (let _154_235 = (let _154_234 = (let _154_233 = (FStar_Format.text "then")
in (let _154_232 = (let _154_231 = (FStar_Format.text "begin")
in (_154_231)::[])
in (_154_233)::_154_232))
in (cond)::_154_234)
in (_154_236)::_154_235))
in (FStar_Format.reduce1 _154_237))
in (let _154_241 = (let _154_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _154_239 = (let _154_238 = (FStar_Format.text "end")
in (_154_238)::[])
in (_154_240)::_154_239))
in (_154_242)::_154_241))
in (FStar_Format.combine FStar_Format.hardline _154_243))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 449 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 450 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_266 = (let _154_265 = (let _154_250 = (let _154_249 = (FStar_Format.text "if")
in (let _154_248 = (let _154_247 = (let _154_246 = (FStar_Format.text "then")
in (let _154_245 = (let _154_244 = (FStar_Format.text "begin")
in (_154_244)::[])
in (_154_246)::_154_245))
in (cond)::_154_247)
in (_154_249)::_154_248))
in (FStar_Format.reduce1 _154_250))
in (let _154_264 = (let _154_263 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _154_262 = (let _154_261 = (let _154_256 = (let _154_255 = (FStar_Format.text "end")
in (let _154_254 = (let _154_253 = (FStar_Format.text "else")
in (let _154_252 = (let _154_251 = (FStar_Format.text "begin")
in (_154_251)::[])
in (_154_253)::_154_252))
in (_154_255)::_154_254))
in (FStar_Format.reduce1 _154_256))
in (let _154_260 = (let _154_259 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _154_258 = (let _154_257 = (FStar_Format.text "end")
in (_154_257)::[])
in (_154_259)::_154_258))
in (_154_261)::_154_260))
in (_154_263)::_154_262))
in (_154_265)::_154_264))
in (FStar_Format.combine FStar_Format.hardline _154_266))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 462 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 463 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 464 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_273 = (let _154_272 = (let _154_271 = (FStar_Format.text "match")
in (let _154_270 = (let _154_269 = (FStar_Format.parens cond)
in (let _154_268 = (let _154_267 = (FStar_Format.text "with")
in (_154_267)::[])
in (_154_269)::_154_268))
in (_154_271)::_154_270))
in (FStar_Format.reduce1 _154_272))
in (_154_273)::pats)
in (
# 465 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _154_278 = (let _154_277 = (FStar_Format.text "raise")
in (let _154_276 = (let _154_275 = (let _154_274 = (ptctor currentModule exn)
in (FStar_Format.text _154_274))
in (_154_275)::[])
in (_154_277)::_154_276))
in (FStar_Format.reduce1 _154_278))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 473 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _154_287 = (let _154_286 = (FStar_Format.text "raise")
in (let _154_285 = (let _154_284 = (let _154_279 = (ptctor currentModule exn)
in (FStar_Format.text _154_279))
in (let _154_283 = (let _154_282 = (let _154_281 = (let _154_280 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_280 args))
in (FStar_Format.parens _154_281))
in (_154_282)::[])
in (_154_284)::_154_283))
in (_154_286)::_154_285))
in (FStar_Format.reduce1 _154_287)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _154_296 = (let _154_295 = (FStar_Format.text "try")
in (let _154_294 = (let _154_293 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _154_292 = (let _154_291 = (FStar_Format.text "with")
in (let _154_290 = (let _154_289 = (let _154_288 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _154_288))
in (_154_289)::[])
in (_154_291)::_154_290))
in (_154_293)::_154_292))
in (_154_295)::_154_294))
in (FStar_Format.combine FStar_Format.hardline _154_296))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 484 "FStar.Extraction.ML.Code.fst"
let _69_444 = (let _154_301 = (as_bin_op p)
in (FStar_Option.get _154_301))
in (match (_69_444) with
| (_69_441, prio, txt) -> begin
(
# 485 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 486 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 487 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_304 = (let _154_303 = (let _154_302 = (FStar_Format.text txt)
in (_154_302)::(e2)::[])
in (e1)::_154_303)
in (FStar_Format.reduce1 _154_304))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 491 "FStar.Extraction.ML.Code.fst"
let _69_454 = (let _154_308 = (as_uni_op p)
in (FStar_Option.get _154_308))
in (match (_69_454) with
| (_69_452, txt) -> begin
(
# 492 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 493 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_312 = (let _154_311 = (FStar_Format.text txt)
in (let _154_310 = (let _154_309 = (FStar_Format.parens e1)
in (_154_309)::[])
in (_154_311)::_154_310))
in (FStar_Format.reduce1 _154_312))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _154_315 = (string_of_mlconstant c)
in (FStar_Format.text _154_315))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 503 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_471 -> (match (_69_471) with
| (name, p) -> begin
(let _154_324 = (let _154_323 = (let _154_318 = (ptsym currentModule (path, name))
in (FStar_Format.text _154_318))
in (let _154_322 = (let _154_321 = (FStar_Format.text "=")
in (let _154_320 = (let _154_319 = (doc_of_pattern currentModule p)
in (_154_319)::[])
in (_154_321)::_154_320))
in (_154_323)::_154_322))
in (FStar_Format.reduce1 _154_324))
end))
in (let _154_327 = (let _154_326 = (FStar_Format.text "; ")
in (let _154_325 = (FStar_List.map for1 fields)
in (FStar_Format.combine _154_326 _154_325)))
in (FStar_Format.cbrackets _154_327)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 507 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_329 = (let _154_328 = (as_standard_constructor ctor)
in (FStar_Option.get _154_328))
in (Prims.snd _154_329))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 515 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_331 = (let _154_330 = (as_standard_constructor ctor)
in (FStar_Option.get _154_330))
in (Prims.snd _154_331))
end else begin
(ptctor currentModule ctor)
end
in (
# 520 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _154_337 = (let _154_336 = (doc_of_pattern currentModule x)
in (let _154_335 = (let _154_334 = (FStar_Format.text "::")
in (let _154_333 = (let _154_332 = (doc_of_pattern currentModule xs)
in (_154_332)::[])
in (_154_334)::_154_333))
in (_154_336)::_154_335))
in (FStar_Format.reduce _154_337))
end
| (_69_488, FStar_Extraction_ML_Syntax.MLP_Tuple (_69_490)::[]) -> begin
(let _154_342 = (let _154_341 = (FStar_Format.text name)
in (let _154_340 = (let _154_339 = (let _154_338 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _154_338))
in (_154_339)::[])
in (_154_341)::_154_340))
in (FStar_Format.reduce1 _154_342))
end
| _69_495 -> begin
(let _154_349 = (let _154_348 = (FStar_Format.text name)
in (let _154_347 = (let _154_346 = (let _154_345 = (let _154_344 = (FStar_Format.text ", ")
in (let _154_343 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _154_344 _154_343)))
in (FStar_Format.parens _154_345))
in (_154_346)::[])
in (_154_348)::_154_347))
in (FStar_Format.reduce1 _154_349))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 529 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _154_351 = (let _154_350 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_350 ps))
in (FStar_Format.parens _154_351)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 533 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 534 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _154_352 = (FStar_Format.text " | ")
in (FStar_Format.combine _154_352 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _69_508 -> (match (_69_508) with
| (p, cond, e) -> begin
(
# 539 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _154_358 = (let _154_357 = (FStar_Format.text "|")
in (let _154_356 = (let _154_355 = (doc_of_pattern currentModule p)
in (_154_355)::[])
in (_154_357)::_154_356))
in (FStar_Format.reduce1 _154_358))
end
| Some (c) -> begin
(
# 543 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _154_364 = (let _154_363 = (FStar_Format.text "|")
in (let _154_362 = (let _154_361 = (doc_of_pattern currentModule p)
in (let _154_360 = (let _154_359 = (FStar_Format.text "when")
in (_154_359)::(c)::[])
in (_154_361)::_154_360))
in (_154_363)::_154_362))
in (FStar_Format.reduce1 _154_364)))
end)
in (let _154_375 = (let _154_374 = (let _154_369 = (let _154_368 = (let _154_367 = (FStar_Format.text "->")
in (let _154_366 = (let _154_365 = (FStar_Format.text "begin")
in (_154_365)::[])
in (_154_367)::_154_366))
in (case)::_154_368)
in (FStar_Format.reduce1 _154_369))
in (let _154_373 = (let _154_372 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _154_371 = (let _154_370 = (FStar_Format.text "end")
in (_154_370)::[])
in (_154_372)::_154_371))
in (_154_374)::_154_373))
in (FStar_Format.combine FStar_Format.hardline _154_375)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _69_518 -> (match (_69_518) with
| (rec_, top_level, lets) -> begin
(
# 554 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_526 -> (match (_69_526) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _69_523; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 555 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 556 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 560 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _69_532 -> (match (_69_532) with
| (x, _69_531) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 561 "FStar.Extraction.ML.Code.fst"
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
# 569 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_382 = (let _154_381 = (FStar_Format.text ":")
in (_154_381)::(ty)::[])
in (FStar_Format.reduce1 _154_382)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 580 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_384 = (let _154_383 = (FStar_Format.text ":")
in (_154_383)::(ty)::[])
in (FStar_Format.reduce1 _154_384)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _154_391 = (let _154_390 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _154_389 = (let _154_388 = (FStar_Format.reduce1 ids)
in (let _154_387 = (let _154_386 = (let _154_385 = (FStar_Format.text "=")
in (_154_385)::(e)::[])
in (ty_annot)::_154_386)
in (_154_388)::_154_387))
in (_154_390)::_154_389))
in (FStar_Format.reduce1 _154_391))))))
end))
in (
# 586 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _154_395 = (let _154_394 = (FStar_Format.text "let")
in (let _154_393 = (let _154_392 = (FStar_Format.text "rec")
in (_154_392)::[])
in (_154_394)::_154_393))
in (FStar_Format.reduce1 _154_395))
end else begin
(FStar_Format.text "let")
end
in (
# 588 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 589 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _154_399 = (let _154_398 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_154_398)::(doc)::[])
in (FStar_Format.reduce1 _154_399))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _69_572 -> (match (_69_572) with
| (lineno, file) -> begin
if ((FStar_ST.read FStar_Options.no_location_info) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 600 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _154_406 = (let _154_405 = (FStar_Format.text "#")
in (let _154_404 = (let _154_403 = (FStar_Format.num lineno)
in (let _154_402 = (let _154_401 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_154_401)::[])
in (_154_403)::_154_402))
in (_154_405)::_154_404))
in (FStar_Format.reduce1 _154_406)))
end
end))

# 601 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 605 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_580 -> (match (_69_580) with
| (x, tparams, body) -> begin
(
# 606 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _69_585 -> begin
(
# 611 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _154_415 = (let _154_414 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_414 doc))
in (FStar_Format.parens _154_415)))
end)
in (
# 614 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 620 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _69_598 -> (match (_69_598) with
| (name, ty) -> begin
(
# 621 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 622 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_422 = (let _154_421 = (let _154_420 = (FStar_Format.text ":")
in (_154_420)::(ty)::[])
in (name)::_154_421)
in (FStar_Format.reduce1 _154_422))))
end))
in (let _154_425 = (let _154_424 = (FStar_Format.text "; ")
in (let _154_423 = (FStar_List.map forfield fields)
in (FStar_Format.combine _154_424 _154_423)))
in (FStar_Format.cbrackets _154_425)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 629 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _69_606 -> (match (_69_606) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _69_609 -> begin
(
# 633 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 634 "FStar.Extraction.ML.Code.fst"
let tys = (let _154_428 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_428 tys))
in (let _154_432 = (let _154_431 = (FStar_Format.text name)
in (let _154_430 = (let _154_429 = (FStar_Format.text "of")
in (_154_429)::(tys)::[])
in (_154_431)::_154_430))
in (FStar_Format.reduce1 _154_432))))
end)
end))
in (
# 638 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 639 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _154_435 = (let _154_434 = (FStar_Format.text "|")
in (_154_434)::(d)::[])
in (FStar_Format.reduce1 _154_435))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 644 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_439 = (let _154_438 = (let _154_437 = (let _154_436 = (ptsym currentModule ([], x))
in (FStar_Format.text _154_436))
in (_154_437)::[])
in (tparams)::_154_438)
in (FStar_Format.reduce1 _154_439))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 649 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _154_444 = (let _154_443 = (let _154_442 = (let _154_441 = (let _154_440 = (FStar_Format.text "=")
in (_154_440)::[])
in (doc)::_154_441)
in (FStar_Format.reduce1 _154_442))
in (_154_443)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _154_444)))
end))))
end))
in (
# 654 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 655 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _154_449 = (let _154_448 = (FStar_Format.text "type")
in (let _154_447 = (let _154_446 = (let _154_445 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _154_445 doc))
in (_154_446)::[])
in (_154_448)::_154_447))
in (FStar_Format.reduce1 _154_449))
end else begin
(FStar_Format.text "")
end
in doc))))

# 656 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _154_469 = (let _154_468 = (let _154_461 = (let _154_460 = (FStar_Format.text "module")
in (let _154_459 = (let _154_458 = (FStar_Format.text x)
in (let _154_457 = (let _154_456 = (FStar_Format.text "=")
in (_154_456)::[])
in (_154_458)::_154_457))
in (_154_460)::_154_459))
in (FStar_Format.reduce1 _154_461))
in (let _154_467 = (let _154_466 = (doc_of_sig currentModule subsig)
in (let _154_465 = (let _154_464 = (let _154_463 = (let _154_462 = (FStar_Format.text "end")
in (_154_462)::[])
in (FStar_Format.reduce1 _154_463))
in (_154_464)::[])
in (_154_466)::_154_465))
in (_154_468)::_154_467))
in (FStar_Format.combine FStar_Format.hardline _154_469))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _154_473 = (let _154_472 = (FStar_Format.text "exception")
in (let _154_471 = (let _154_470 = (FStar_Format.text x)
in (_154_470)::[])
in (_154_472)::_154_471))
in (FStar_Format.reduce1 _154_473))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 671 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 672 "FStar.Extraction.ML.Code.fst"
let args = (let _154_475 = (let _154_474 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_474 args))
in (FStar_Format.parens _154_475))
in (let _154_481 = (let _154_480 = (FStar_Format.text "exception")
in (let _154_479 = (let _154_478 = (FStar_Format.text x)
in (let _154_477 = (let _154_476 = (FStar_Format.text "of")
in (_154_476)::(args)::[])
in (_154_478)::_154_477))
in (_154_480)::_154_479))
in (FStar_Format.reduce1 _154_481))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_69_640, ty)) -> begin
(
# 676 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_487 = (let _154_486 = (FStar_Format.text "val")
in (let _154_485 = (let _154_484 = (FStar_Format.text x)
in (let _154_483 = (let _154_482 = (FStar_Format.text ": ")
in (_154_482)::(ty)::[])
in (_154_484)::_154_483))
in (_154_486)::_154_485))
in (FStar_Format.reduce1 _154_487)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 684 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 685 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 686 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _154_498 = (let _154_497 = (FStar_Format.text "exception")
in (let _154_496 = (let _154_495 = (FStar_Format.text x)
in (_154_495)::[])
in (_154_497)::_154_496))
in (FStar_Format.reduce1 _154_498))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 696 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 697 "FStar.Extraction.ML.Code.fst"
let args = (let _154_500 = (let _154_499 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_499 args))
in (FStar_Format.parens _154_500))
in (let _154_506 = (let _154_505 = (FStar_Format.text "exception")
in (let _154_504 = (let _154_503 = (FStar_Format.text x)
in (let _154_502 = (let _154_501 = (FStar_Format.text "of")
in (_154_501)::(args)::[])
in (_154_503)::_154_502))
in (_154_505)::_154_504))
in (FStar_Format.reduce1 _154_506))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _154_514 = (let _154_513 = (FStar_Format.text "let")
in (let _154_512 = (let _154_511 = (FStar_Format.text "_")
in (let _154_510 = (let _154_509 = (FStar_Format.text "=")
in (let _154_508 = (let _154_507 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_154_507)::[])
in (_154_509)::_154_508))
in (_154_511)::_154_510))
in (_154_513)::_154_512))
in (FStar_Format.reduce1 _154_514))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 713 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 717 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 718 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_69_680) -> begin
FStar_Format.empty
end
| _69_683 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 720 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _69_686 -> (match (_69_686) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 724 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _69_693 -> (match (_69_693) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 725 "FStar.Extraction.ML.Code.fst"
let head = (let _154_533 = (let _154_532 = (FStar_Format.text "module")
in (let _154_531 = (let _154_530 = (FStar_Format.text x)
in (let _154_529 = (let _154_528 = (FStar_Format.text ":")
in (let _154_527 = (let _154_526 = (FStar_Format.text "sig")
in (_154_526)::[])
in (_154_528)::_154_527))
in (_154_530)::_154_529))
in (_154_532)::_154_531))
in (FStar_Format.reduce1 _154_533))
in (
# 726 "FStar.Extraction.ML.Code.fst"
let tail = (let _154_535 = (let _154_534 = (FStar_Format.text "end")
in (_154_534)::[])
in (FStar_Format.reduce1 _154_535))
in (
# 727 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _69_699 -> (match (_69_699) with
| (s, _69_698) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 728 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 729 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _154_545 = (let _154_544 = (FStar_Format.cat head FStar_Format.hardline)
in (let _154_543 = (let _154_542 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _154_541 = (let _154_540 = (FStar_Format.reduce sub)
in (let _154_539 = (let _154_538 = (FStar_Format.cat tail FStar_Format.hardline)
in (_154_538)::[])
in (_154_540)::_154_539))
in (_154_542)::_154_541))
in (_154_544)::_154_543))
in (FStar_Format.reduce _154_545)))))))
end))
and for1_mod = (fun istop _69_712 -> (match (_69_712) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 740 "FStar.Extraction.ML.Code.fst"
let head = (let _154_558 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_550 = (FStar_Format.text "module")
in (let _154_549 = (let _154_548 = (FStar_Format.text x)
in (_154_548)::[])
in (_154_550)::_154_549))
end else begin
if (not (istop)) then begin
(let _154_557 = (FStar_Format.text "module")
in (let _154_556 = (let _154_555 = (FStar_Format.text x)
in (let _154_554 = (let _154_553 = (FStar_Format.text "=")
in (let _154_552 = (let _154_551 = (FStar_Format.text "struct")
in (_154_551)::[])
in (_154_553)::_154_552))
in (_154_555)::_154_554))
in (_154_557)::_154_556))
end else begin
[]
end
end
in (FStar_Format.reduce1 _154_558))
in (
# 745 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _154_560 = (let _154_559 = (FStar_Format.text "end")
in (_154_559)::[])
in (FStar_Format.reduce1 _154_560))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 748 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _69_718 -> (match (_69_718) with
| (_69_716, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 749 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 750 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 751 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_564 = (let _154_563 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _154_563 FStar_Format.hardline))
in (_154_564)::[])
end else begin
[]
end
in (let _154_576 = (let _154_575 = (let _154_574 = (let _154_573 = (let _154_572 = (FStar_Format.text "open Prims")
in (let _154_571 = (let _154_570 = (let _154_569 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _154_568 = (let _154_567 = (FStar_Format.reduce sub)
in (let _154_566 = (let _154_565 = (FStar_Format.cat tail FStar_Format.hardline)
in (_154_565)::[])
in (_154_567)::_154_566))
in (_154_569)::_154_568))
in (FStar_Format.hardline)::_154_570)
in (_154_572)::_154_571))
in (FStar_Format.hardline)::_154_573)
in (head)::_154_574)
in (FStar_List.append prefix _154_575))
in (FStar_All.pipe_left FStar_Format.reduce _154_576))))))))
end))
in (
# 767 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _69_730 -> (match (_69_730) with
| (x, s, m) -> begin
(let _154_578 = (for1_mod true (x, s, m))
in (x, _154_578))
end)) mllib)
in docs))
end))

# 768 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 772 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 775 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_585 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _154_585 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 776 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 779 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_590 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _154_590 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





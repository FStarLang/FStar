
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
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _69_294; FStar_Extraction_ML_Syntax.loc = _69_292}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _69_314; FStar_Extraction_ML_Syntax.loc = _69_312}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _69_326 -> begin
(
# 395 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 396 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _154_196 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _154_196))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 401 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 402 "FStar.Extraction.ML.Code.fst"
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
# 409 "FStar.Extraction.ML.Code.fst"
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
| _69_345 -> begin
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
# 415 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _69_351 -> (match (_69_351) with
| ((x, _69_348), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 416 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 417 "FStar.Extraction.ML.Code.fst"
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
# 421 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 422 "FStar.Extraction.ML.Code.fst"
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
# 432 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 433 "FStar.Extraction.ML.Code.fst"
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
# 445 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 446 "FStar.Extraction.ML.Code.fst"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 447 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_273 = (let _154_272 = (let _154_271 = (FStar_Format.text "match")
in (let _154_270 = (let _154_269 = (FStar_Format.parens cond)
in (let _154_268 = (let _154_267 = (FStar_Format.text "with")
in (_154_267)::[])
in (_154_269)::_154_268))
in (_154_271)::_154_270))
in (FStar_Format.reduce1 _154_272))
in (_154_273)::pats)
in (
# 448 "FStar.Extraction.ML.Code.fst"
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
# 456 "FStar.Extraction.ML.Code.fst"
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
(let _154_304 = (let _154_303 = (let _154_291 = (let _154_290 = (FStar_Format.text "try")
in (let _154_289 = (let _154_288 = (FStar_Format.text "begin")
in (_154_288)::[])
in (_154_290)::_154_289))
in (FStar_Format.reduce1 _154_291))
in (let _154_302 = (let _154_301 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _154_300 = (let _154_299 = (let _154_295 = (let _154_294 = (FStar_Format.text "end")
in (let _154_293 = (let _154_292 = (FStar_Format.text "with")
in (_154_292)::[])
in (_154_294)::_154_293))
in (FStar_Format.reduce1 _154_295))
in (let _154_298 = (let _154_297 = (let _154_296 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _154_296))
in (_154_297)::[])
in (_154_299)::_154_298))
in (_154_301)::_154_300))
in (_154_303)::_154_302))
in (FStar_Format.combine FStar_Format.hardline _154_304))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 467 "FStar.Extraction.ML.Code.fst"
let _69_399 = (let _154_309 = (as_bin_op p)
in (FStar_Option.get _154_309))
in (match (_69_399) with
| (_69_396, prio, txt) -> begin
(
# 468 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 469 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_312 = (let _154_311 = (let _154_310 = (FStar_Format.text txt)
in (_154_310)::(e2)::[])
in (e1)::_154_311)
in (FStar_Format.reduce1 _154_312))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 474 "FStar.Extraction.ML.Code.fst"
let _69_409 = (let _154_316 = (as_uni_op p)
in (FStar_Option.get _154_316))
in (match (_69_409) with
| (_69_407, txt) -> begin
(
# 475 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 476 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_320 = (let _154_319 = (FStar_Format.text txt)
in (let _154_318 = (let _154_317 = (FStar_Format.parens e1)
in (_154_317)::[])
in (_154_319)::_154_318))
in (FStar_Format.reduce1 _154_320))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _154_323 = (string_of_mlconstant c)
in (FStar_Format.text _154_323))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 486 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_426 -> (match (_69_426) with
| (name, p) -> begin
(let _154_332 = (let _154_331 = (let _154_326 = (ptsym currentModule (path, name))
in (FStar_Format.text _154_326))
in (let _154_330 = (let _154_329 = (FStar_Format.text "=")
in (let _154_328 = (let _154_327 = (doc_of_pattern currentModule p)
in (_154_327)::[])
in (_154_329)::_154_328))
in (_154_331)::_154_330))
in (FStar_Format.reduce1 _154_332))
end))
in (let _154_335 = (let _154_334 = (FStar_Format.text "; ")
in (let _154_333 = (FStar_List.map for1 fields)
in (FStar_Format.combine _154_334 _154_333)))
in (FStar_Format.cbrackets _154_335)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 490 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_337 = (let _154_336 = (as_standard_constructor ctor)
in (FStar_Option.get _154_336))
in (Prims.snd _154_337))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 498 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _154_339 = (let _154_338 = (as_standard_constructor ctor)
in (FStar_Option.get _154_338))
in (Prims.snd _154_339))
end else begin
(ptctor currentModule ctor)
end
in (
# 503 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _154_345 = (let _154_344 = (doc_of_pattern currentModule x)
in (let _154_343 = (let _154_342 = (FStar_Format.text "::")
in (let _154_341 = (let _154_340 = (doc_of_pattern currentModule xs)
in (_154_340)::[])
in (_154_342)::_154_341))
in (_154_344)::_154_343))
in (FStar_Format.reduce _154_345))
end
| (_69_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_69_445)::[]) -> begin
(let _154_350 = (let _154_349 = (FStar_Format.text name)
in (let _154_348 = (let _154_347 = (let _154_346 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _154_346))
in (_154_347)::[])
in (_154_349)::_154_348))
in (FStar_Format.reduce1 _154_350))
end
| _69_450 -> begin
(let _154_357 = (let _154_356 = (FStar_Format.text name)
in (let _154_355 = (let _154_354 = (let _154_353 = (let _154_352 = (FStar_Format.text ", ")
in (let _154_351 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _154_352 _154_351)))
in (FStar_Format.parens _154_353))
in (_154_354)::[])
in (_154_356)::_154_355))
in (FStar_Format.reduce1 _154_357))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 512 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _154_359 = (let _154_358 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_358 ps))
in (FStar_Format.parens _154_359)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 516 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 517 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _154_360 = (FStar_Format.text " | ")
in (FStar_Format.combine _154_360 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _69_463 -> (match (_69_463) with
| (p, cond, e) -> begin
(
# 522 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _154_366 = (let _154_365 = (FStar_Format.text "|")
in (let _154_364 = (let _154_363 = (doc_of_pattern currentModule p)
in (_154_363)::[])
in (_154_365)::_154_364))
in (FStar_Format.reduce1 _154_366))
end
| Some (c) -> begin
(
# 526 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _154_372 = (let _154_371 = (FStar_Format.text "|")
in (let _154_370 = (let _154_369 = (doc_of_pattern currentModule p)
in (let _154_368 = (let _154_367 = (FStar_Format.text "when")
in (_154_367)::(c)::[])
in (_154_369)::_154_368))
in (_154_371)::_154_370))
in (FStar_Format.reduce1 _154_372)))
end)
in (let _154_383 = (let _154_382 = (let _154_377 = (let _154_376 = (let _154_375 = (FStar_Format.text "->")
in (let _154_374 = (let _154_373 = (FStar_Format.text "begin")
in (_154_373)::[])
in (_154_375)::_154_374))
in (case)::_154_376)
in (FStar_Format.reduce1 _154_377))
in (let _154_381 = (let _154_380 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _154_379 = (let _154_378 = (FStar_Format.text "end")
in (_154_378)::[])
in (_154_380)::_154_379))
in (_154_382)::_154_381))
in (FStar_Format.combine FStar_Format.hardline _154_383)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _69_473 -> (match (_69_473) with
| (rec_, top_level, lets) -> begin
(
# 537 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_481 -> (match (_69_481) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _69_478; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 538 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 539 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 543 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _69_487 -> (match (_69_487) with
| (x, _69_486) -> begin
(FStar_Format.text x)
end)) ids)
in (
# 544 "FStar.Extraction.ML.Code.fst"
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
# 552 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_390 = (let _154_389 = (FStar_Format.text ":")
in (_154_389)::(ty)::[])
in (FStar_Format.reduce1 _154_390)))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FStar_Format.text "")
end
| Some ([], ty) -> begin
(
# 563 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_392 = (let _154_391 = (FStar_Format.text ":")
in (_154_391)::(ty)::[])
in (FStar_Format.reduce1 _154_392)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _154_399 = (let _154_398 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _154_397 = (let _154_396 = (FStar_Format.reduce1 ids)
in (let _154_395 = (let _154_394 = (let _154_393 = (FStar_Format.text "=")
in (_154_393)::(e)::[])
in (ty_annot)::_154_394)
in (_154_396)::_154_395))
in (_154_398)::_154_397))
in (FStar_Format.reduce1 _154_399))))))
end))
in (
# 569 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _154_403 = (let _154_402 = (FStar_Format.text "let")
in (let _154_401 = (let _154_400 = (FStar_Format.text "rec")
in (_154_400)::[])
in (_154_402)::_154_401))
in (FStar_Format.reduce1 _154_403))
end else begin
(FStar_Format.text "let")
end
in (
# 571 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 572 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _154_407 = (let _154_406 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_154_406)::(doc)::[])
in (FStar_Format.reduce1 _154_407))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _69_527 -> (match (_69_527) with
| (lineno, file) -> begin
if ((FStar_ST.read FStar_Options.no_location_info) || (FStar_Extraction_ML_Util.codegen_fsharp ())) then begin
FStar_Format.empty
end else begin
(
# 583 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _154_414 = (let _154_413 = (FStar_Format.text "#")
in (let _154_412 = (let _154_411 = (FStar_Format.num lineno)
in (let _154_410 = (let _154_409 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_154_409)::[])
in (_154_411)::_154_410))
in (_154_413)::_154_412))
in (FStar_Format.reduce1 _154_414)))
end
end))

# 584 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 588 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _69_535 -> (match (_69_535) with
| (x, tparams, body) -> begin
(
# 589 "FStar.Extraction.ML.Code.fst"
let tparams = (match (tparams) with
| [] -> begin
FStar_Format.empty
end
| x::[] -> begin
(FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _69_540 -> begin
(
# 594 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _154_423 = (let _154_422 = (FStar_Format.text ", ")
in (FStar_Format.combine _154_422 doc))
in (FStar_Format.parens _154_423)))
end)
in (
# 597 "FStar.Extraction.ML.Code.fst"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 603 "FStar.Extraction.ML.Code.fst"
let forfield = (fun _69_553 -> (match (_69_553) with
| (name, ty) -> begin
(
# 604 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 605 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_430 = (let _154_429 = (let _154_428 = (FStar_Format.text ":")
in (_154_428)::(ty)::[])
in (name)::_154_429)
in (FStar_Format.reduce1 _154_430))))
end))
in (let _154_433 = (let _154_432 = (FStar_Format.text "; ")
in (let _154_431 = (FStar_List.map forfield fields)
in (FStar_Format.combine _154_432 _154_431)))
in (FStar_Format.cbrackets _154_433)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 612 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _69_561 -> (match (_69_561) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _69_564 -> begin
(
# 616 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 617 "FStar.Extraction.ML.Code.fst"
let tys = (let _154_436 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_436 tys))
in (let _154_440 = (let _154_439 = (FStar_Format.text name)
in (let _154_438 = (let _154_437 = (FStar_Format.text "of")
in (_154_437)::(tys)::[])
in (_154_439)::_154_438))
in (FStar_Format.reduce1 _154_440))))
end)
end))
in (
# 621 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 622 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _154_443 = (let _154_442 = (FStar_Format.text "|")
in (_154_442)::(d)::[])
in (FStar_Format.reduce1 _154_443))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 627 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_447 = (let _154_446 = (let _154_445 = (let _154_444 = (ptsym currentModule ([], x))
in (FStar_Format.text _154_444))
in (_154_445)::[])
in (tparams)::_154_446)
in (FStar_Format.reduce1 _154_447))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 632 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _154_452 = (let _154_451 = (let _154_450 = (let _154_449 = (let _154_448 = (FStar_Format.text "=")
in (_154_448)::[])
in (doc)::_154_449)
in (FStar_Format.reduce1 _154_450))
in (_154_451)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _154_452)))
end))))
end))
in (
# 637 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 638 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _154_457 = (let _154_456 = (FStar_Format.text "type")
in (let _154_455 = (let _154_454 = (let _154_453 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _154_453 doc))
in (_154_454)::[])
in (_154_456)::_154_455))
in (FStar_Format.reduce1 _154_457))
end else begin
(FStar_Format.text "")
end
in doc))))

# 639 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _154_477 = (let _154_476 = (let _154_469 = (let _154_468 = (FStar_Format.text "module")
in (let _154_467 = (let _154_466 = (FStar_Format.text x)
in (let _154_465 = (let _154_464 = (FStar_Format.text "=")
in (_154_464)::[])
in (_154_466)::_154_465))
in (_154_468)::_154_467))
in (FStar_Format.reduce1 _154_469))
in (let _154_475 = (let _154_474 = (doc_of_sig currentModule subsig)
in (let _154_473 = (let _154_472 = (let _154_471 = (let _154_470 = (FStar_Format.text "end")
in (_154_470)::[])
in (FStar_Format.reduce1 _154_471))
in (_154_472)::[])
in (_154_474)::_154_473))
in (_154_476)::_154_475))
in (FStar_Format.combine FStar_Format.hardline _154_477))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _154_481 = (let _154_480 = (FStar_Format.text "exception")
in (let _154_479 = (let _154_478 = (FStar_Format.text x)
in (_154_478)::[])
in (_154_480)::_154_479))
in (FStar_Format.reduce1 _154_481))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 654 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 655 "FStar.Extraction.ML.Code.fst"
let args = (let _154_483 = (let _154_482 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_482 args))
in (FStar_Format.parens _154_483))
in (let _154_489 = (let _154_488 = (FStar_Format.text "exception")
in (let _154_487 = (let _154_486 = (FStar_Format.text x)
in (let _154_485 = (let _154_484 = (FStar_Format.text "of")
in (_154_484)::(args)::[])
in (_154_486)::_154_485))
in (_154_488)::_154_487))
in (FStar_Format.reduce1 _154_489))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_69_595, ty)) -> begin
(
# 659 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _154_495 = (let _154_494 = (FStar_Format.text "val")
in (let _154_493 = (let _154_492 = (FStar_Format.text x)
in (let _154_491 = (let _154_490 = (FStar_Format.text ": ")
in (_154_490)::(ty)::[])
in (_154_492)::_154_491))
in (_154_494)::_154_493))
in (FStar_Format.reduce1 _154_495)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FStar_Format.doc = (fun currentModule s -> (
# 667 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 668 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) docs)
in (FStar_Format.reduce docs))))

# 669 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _154_506 = (let _154_505 = (FStar_Format.text "exception")
in (let _154_504 = (let _154_503 = (FStar_Format.text x)
in (_154_503)::[])
in (_154_505)::_154_504))
in (FStar_Format.reduce1 _154_506))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 679 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 680 "FStar.Extraction.ML.Code.fst"
let args = (let _154_508 = (let _154_507 = (FStar_Format.text " * ")
in (FStar_Format.combine _154_507 args))
in (FStar_Format.parens _154_508))
in (let _154_514 = (let _154_513 = (FStar_Format.text "exception")
in (let _154_512 = (let _154_511 = (FStar_Format.text x)
in (let _154_510 = (let _154_509 = (FStar_Format.text "of")
in (_154_509)::(args)::[])
in (_154_511)::_154_510))
in (_154_513)::_154_512))
in (FStar_Format.reduce1 _154_514))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _154_522 = (let _154_521 = (FStar_Format.text "let")
in (let _154_520 = (let _154_519 = (FStar_Format.text "_")
in (let _154_518 = (let _154_517 = (FStar_Format.text "=")
in (let _154_516 = (let _154_515 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_154_515)::[])
in (_154_517)::_154_516))
in (_154_519)::_154_518))
in (_154_521)::_154_520))
in (FStar_Format.reduce1 _154_522))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 696 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 700 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 701 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_69_635) -> begin
FStar_Format.empty
end
| _69_638 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 703 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _69_641 -> (match (_69_641) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 707 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _69_648 -> (match (_69_648) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 708 "FStar.Extraction.ML.Code.fst"
let head = (let _154_541 = (let _154_540 = (FStar_Format.text "module")
in (let _154_539 = (let _154_538 = (FStar_Format.text x)
in (let _154_537 = (let _154_536 = (FStar_Format.text ":")
in (let _154_535 = (let _154_534 = (FStar_Format.text "sig")
in (_154_534)::[])
in (_154_536)::_154_535))
in (_154_538)::_154_537))
in (_154_540)::_154_539))
in (FStar_Format.reduce1 _154_541))
in (
# 709 "FStar.Extraction.ML.Code.fst"
let tail = (let _154_543 = (let _154_542 = (FStar_Format.text "end")
in (_154_542)::[])
in (FStar_Format.reduce1 _154_543))
in (
# 710 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _69_654 -> (match (_69_654) with
| (s, _69_653) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 711 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 712 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _154_553 = (let _154_552 = (FStar_Format.cat head FStar_Format.hardline)
in (let _154_551 = (let _154_550 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _154_549 = (let _154_548 = (FStar_Format.reduce sub)
in (let _154_547 = (let _154_546 = (FStar_Format.cat tail FStar_Format.hardline)
in (_154_546)::[])
in (_154_548)::_154_547))
in (_154_550)::_154_549))
in (_154_552)::_154_551))
in (FStar_Format.reduce _154_553)))))))
end))
and for1_mod = (fun istop _69_667 -> (match (_69_667) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 723 "FStar.Extraction.ML.Code.fst"
let head = (let _154_566 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_558 = (FStar_Format.text "module")
in (let _154_557 = (let _154_556 = (FStar_Format.text x)
in (_154_556)::[])
in (_154_558)::_154_557))
end else begin
if (not (istop)) then begin
(let _154_565 = (FStar_Format.text "module")
in (let _154_564 = (let _154_563 = (FStar_Format.text x)
in (let _154_562 = (let _154_561 = (FStar_Format.text "=")
in (let _154_560 = (let _154_559 = (FStar_Format.text "struct")
in (_154_559)::[])
in (_154_561)::_154_560))
in (_154_563)::_154_562))
in (_154_565)::_154_564))
end else begin
[]
end
end
in (FStar_Format.reduce1 _154_566))
in (
# 728 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _154_568 = (let _154_567 = (FStar_Format.text "end")
in (_154_567)::[])
in (FStar_Format.reduce1 _154_568))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 731 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _69_673 -> (match (_69_673) with
| (_69_671, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 732 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 733 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (
# 734 "FStar.Extraction.ML.Code.fst"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _154_572 = (let _154_571 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _154_571 FStar_Format.hardline))
in (_154_572)::[])
end else begin
[]
end
in (let _154_584 = (let _154_583 = (let _154_582 = (let _154_581 = (let _154_580 = (FStar_Format.text "open Prims")
in (let _154_579 = (let _154_578 = (let _154_577 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _154_576 = (let _154_575 = (FStar_Format.reduce sub)
in (let _154_574 = (let _154_573 = (FStar_Format.cat tail FStar_Format.hardline)
in (_154_573)::[])
in (_154_575)::_154_574))
in (_154_577)::_154_576))
in (FStar_Format.hardline)::_154_578)
in (_154_580)::_154_579))
in (FStar_Format.hardline)::_154_581)
in (head)::_154_582)
in (FStar_List.append prefix _154_583))
in (FStar_All.pipe_left FStar_Format.reduce _154_584))))))))
end))
in (
# 750 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _69_685 -> (match (_69_685) with
| (x, s, m) -> begin
(let _154_586 = (for1_mod true (x, s, m))
in (x, _154_586))
end)) mllib)
in docs))
end))

# 751 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 755 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 758 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_593 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _154_593 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 759 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 762 "FStar.Extraction.ML.Code.fst"
let doc = (let _154_598 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _154_598 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





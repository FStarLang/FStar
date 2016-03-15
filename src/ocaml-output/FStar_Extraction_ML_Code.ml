
open Prims
# 35 "FStar.Extraction.ML.Code.fst"
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

# 36 "FStar.Extraction.ML.Code.fst"
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
| Infix (_68_3) -> begin
_68_3
end))

# 37 "FStar.Extraction.ML.Code.fst"
type opprec =
(Prims.int * fixity)

# 38 "FStar.Extraction.ML.Code.fst"
type level =
(opprec * assoc)

# 40 "FStar.Extraction.ML.Code.fst"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 41 "FStar.Extraction.ML.Code.fst"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 42 "FStar.Extraction.ML.Code.fst"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 44 "FStar.Extraction.ML.Code.fst"
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

# 59 "FStar.Extraction.ML.Code.fst"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 60 "FStar.Extraction.ML.Code.fst"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 66 "FStar.Extraction.ML.Code.fst"
let rec in_ns = (fun x -> (match (x) with
| ([], _68_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_68_18, _68_20) -> begin
false
end))

# 72 "FStar.Extraction.ML.Code.fst"
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
let _68_31 = (FStar_Util.first_N cg_len ns)
in (match (_68_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _152_31 = (let _152_30 = (let _152_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_152_29)::[])
in (FStar_List.append pfx _152_30))
in Some (_152_31))
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

# 90 "FStar.Extraction.ML.Code.fst"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _68_41 -> begin
(
# 95 "FStar.Extraction.ML.Code.fst"
let _68_44 = x
in (match (_68_44) with
| (ns, x) -> begin
(let _152_36 = (path_of_ns currentModule ns)
in (_152_36, x))
end))
end))

# 98 "FStar.Extraction.ML.Code.fst"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _152_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _152_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 103 "FStar.Extraction.ML.Code.fst"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 107 "FStar.Extraction.ML.Code.fst"
let _68_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_68_50) with
| (p, s) -> begin
(let _152_46 = (let _152_45 = (let _152_44 = (ptsym_of_symbol s)
in (_152_44)::[])
in (FStar_List.append p _152_45))
in (FStar_String.concat "." _152_46))
end))
end)

# 111 "FStar.Extraction.ML.Code.fst"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 112 "FStar.Extraction.ML.Code.fst"
let _68_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_68_55) with
| (p, s) -> begin
(
# 113 "FStar.Extraction.ML.Code.fst"
let s = if ((let _152_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _152_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 117 "FStar.Extraction.ML.Code.fst"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 135 "FStar.Extraction.ML.Code.fst"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 142 "FStar.Extraction.ML.Code.fst"
let prim_types = []

# 145 "FStar.Extraction.ML.Code.fst"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 153 "FStar.Extraction.ML.Code.fst"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 157 "FStar.Extraction.ML.Code.fst"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _68_60 -> (match (_68_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _68_66 -> (match (_68_66) with
| (y, _68_63, _68_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 164 "FStar.Extraction.ML.Code.fst"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 168 "FStar.Extraction.ML.Code.fst"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _68_70 -> (match (_68_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _68_74 -> (match (_68_74) with
| (y, _68_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 175 "FStar.Extraction.ML.Code.fst"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 179 "FStar.Extraction.ML.Code.fst"
let as_standard_type = (fun _68_78 -> (match (_68_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _68_82 -> (match (_68_82) with
| (y, _68_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 186 "FStar.Extraction.ML.Code.fst"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 190 "FStar.Extraction.ML.Code.fst"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _68_86 -> (match (_68_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _68_90 -> (match (_68_90) with
| (y, _68_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 197 "FStar.Extraction.ML.Code.fst"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 201 "FStar.Extraction.ML.Code.fst"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun _68_94 inner doc -> (match (_68_94) with
| (outer, side) -> begin
(
# 202 "FStar.Extraction.ML.Code.fst"
let noparens = (fun _inner _outer side -> (
# 203 "FStar.Extraction.ML.Code.fst"
let _68_103 = _inner
in (match (_68_103) with
| (pi, fi) -> begin
(
# 204 "FStar.Extraction.ML.Code.fst"
let _68_106 = _outer
in (match (_68_106) with
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
| (_68_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_68_134, _68_136) -> begin
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

# 220 "FStar.Extraction.ML.Code.fst"
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 224 "FStar.Extraction.ML.Code.fst"
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
| _68_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 245 "FStar.Extraction.ML.Code.fst"
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
(let _152_92 = (let _152_91 = (encode_char c)
in (Prims.strcat "\'" _152_91))
in (Prims.strcat _152_92 "\'"))
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

# 269 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 272 "FStar.Extraction.ML.Code.fst"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _152_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FStar_Format.text _152_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 279 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 280 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_107 = (let _152_106 = (let _152_105 = (FStar_Format.text " * ")
in (FStar_Format.combine _152_105 doc))
in (FStar_Format.hbox _152_106))
in (FStar_Format.parens _152_107))
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
| _68_198 -> begin
(
# 289 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _152_110 = (let _152_109 = (let _152_108 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_108 args))
in (FStar_Format.hbox _152_109))
in (FStar_Format.parens _152_110)))
end)
in (
# 294 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_type name) then begin
(let _152_112 = (let _152_111 = (as_standard_type name)
in (FStar_Option.get _152_111))
in (Prims.snd _152_112))
end else begin
(ptsym currentModule name)
end
in (let _152_116 = (let _152_115 = (let _152_114 = (let _152_113 = (FStar_Format.text name)
in (_152_113)::[])
in (args)::_152_114)
in (FStar_Format.reduce1 _152_115))
in (FStar_Format.hbox _152_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _68_204, t2) -> begin
(
# 304 "FStar.Extraction.ML.Code.fst"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 305 "FStar.Extraction.ML.Code.fst"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _152_121 = (let _152_120 = (let _152_119 = (let _152_118 = (let _152_117 = (FStar_Format.text " -> ")
in (_152_117)::(d2)::[])
in (d1)::_152_118)
in (FStar_Format.reduce1 _152_119))
in (FStar_Format.hbox _152_120))
in (maybe_paren outer t_prio_fun _152_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FStar_Format.text "obj")
end else begin
(FStar_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FStar_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

# 317 "FStar.Extraction.ML.Code.fst"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 320 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _152_147 = (let _152_146 = (let _152_145 = (FStar_Format.text "Prims.checked_cast")
in (_152_145)::(doc)::[])
in (FStar_Format.reduce _152_146))
in (FStar_Format.parens _152_147))
end else begin
(let _152_152 = (let _152_151 = (let _152_150 = (FStar_Format.text "Obj.magic ")
in (let _152_149 = (let _152_148 = (FStar_Format.parens doc)
in (_152_148)::[])
in (_152_150)::_152_149))
in (FStar_Format.reduce _152_151))
in (FStar_Format.parens _152_152))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 326 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 327 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun d -> (let _152_156 = (let _152_155 = (let _152_154 = (FStar_Format.text ";")
in (_152_154)::(FStar_Format.hardline)::[])
in (d)::_152_155)
in (FStar_Format.reduce _152_156))) docs)
in (FStar_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _152_157 = (string_of_mlconstant c)
in (FStar_Format.text _152_157))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _68_232) -> begin
(FStar_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _152_158 = (ptsym currentModule path)
in (FStar_Format.text _152_158))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 340 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _68_244 -> (match (_68_244) with
| (name, e) -> begin
(
# 341 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _152_165 = (let _152_164 = (let _152_161 = (ptsym currentModule (path, name))
in (FStar_Format.text _152_161))
in (let _152_163 = (let _152_162 = (FStar_Format.text "=")
in (_152_162)::(doc)::[])
in (_152_164)::_152_163))
in (FStar_Format.reduce1 _152_165)))
end))
in (let _152_168 = (let _152_167 = (FStar_Format.text "; ")
in (let _152_166 = (FStar_List.map for1 fields)
in (FStar_Format.combine _152_167 _152_166)))
in (FStar_Format.cbrackets _152_168)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 347 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _152_170 = (let _152_169 = (as_standard_constructor ctor)
in (FStar_Option.get _152_169))
in (Prims.snd _152_170))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 355 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _152_172 = (let _152_171 = (as_standard_constructor ctor)
in (FStar_Option.get _152_171))
in (Prims.snd _152_172))
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
(let _152_176 = (let _152_175 = (FStar_Format.parens x)
in (let _152_174 = (let _152_173 = (FStar_Format.text "::")
in (_152_173)::(xs)::[])
in (_152_175)::_152_174))
in (FStar_Format.reduce _152_176))
end
| (_68_263, _68_265) -> begin
(let _152_182 = (let _152_181 = (FStar_Format.text name)
in (let _152_180 = (let _152_179 = (let _152_178 = (let _152_177 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_177 args))
in (FStar_Format.parens _152_178))
in (_152_179)::[])
in (_152_181)::_152_180))
in (FStar_Format.reduce1 _152_182))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 369 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 370 "FStar.Extraction.ML.Code.fst"
let docs = (let _152_184 = (let _152_183 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_183 docs))
in (FStar_Format.parens _152_184))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 374 "FStar.Extraction.ML.Code.fst"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _152_187 = (let _152_186 = (let _152_185 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_152_185)::[])
in (FStar_Format.hardline)::_152_186)
in (FStar_Format.reduce _152_187))
end else begin
FStar_Format.empty
end
in (
# 379 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 380 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _152_194 = (let _152_193 = (let _152_192 = (let _152_191 = (let _152_190 = (let _152_189 = (let _152_188 = (FStar_Format.text "in")
in (_152_188)::(body)::[])
in (FStar_Format.reduce1 _152_189))
in (_152_190)::[])
in (doc)::_152_191)
in (pre)::_152_192)
in (FStar_Format.combine FStar_Format.hardline _152_193))
in (FStar_Format.parens _152_194)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _68_294; FStar_Extraction_ML_Syntax.loc = _68_292}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.mlty = _68_314; FStar_Extraction_ML_Syntax.loc = _68_312}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _68_326 -> begin
(
# 395 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 396 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _152_195 = (FStar_Format.reduce1 ((e)::args))
in (FStar_Format.parens _152_195))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 401 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 402 "FStar.Extraction.ML.Code.fst"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _152_200 = (let _152_199 = (let _152_198 = (FStar_Format.text ".")
in (let _152_197 = (let _152_196 = (FStar_Format.text (Prims.snd f))
in (_152_196)::[])
in (_152_198)::_152_197))
in (e)::_152_199)
in (FStar_Format.reduce _152_200))
end else begin
(let _152_206 = (let _152_205 = (let _152_204 = (FStar_Format.text ".")
in (let _152_203 = (let _152_202 = (let _152_201 = (ptsym currentModule f)
in (FStar_Format.text _152_201))
in (_152_202)::[])
in (_152_204)::_152_203))
in (e)::_152_205)
in (FStar_Format.reduce _152_206))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 409 "FStar.Extraction.ML.Code.fst"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _152_222 = (let _152_221 = (FStar_Format.text "(")
in (let _152_220 = (let _152_219 = (FStar_Format.text x)
in (let _152_218 = (let _152_217 = (match (xt) with
| Some (xxt) -> begin
(let _152_214 = (let _152_213 = (FStar_Format.text " : ")
in (let _152_212 = (let _152_211 = (doc_of_mltype currentModule outer xxt)
in (_152_211)::[])
in (_152_213)::_152_212))
in (FStar_Format.reduce1 _152_214))
end
| _68_345 -> begin
(FStar_Format.text "")
end)
in (let _152_216 = (let _152_215 = (FStar_Format.text ")")
in (_152_215)::[])
in (_152_217)::_152_216))
in (_152_219)::_152_218))
in (_152_221)::_152_220))
in (FStar_Format.reduce1 _152_222))
end else begin
(FStar_Format.text x)
end)
in (
# 415 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _68_351 -> (match (_68_351) with
| ((x, _68_348), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 416 "FStar.Extraction.ML.Code.fst"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 417 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_229 = (let _152_228 = (FStar_Format.text "fun")
in (let _152_227 = (let _152_226 = (FStar_Format.reduce1 ids)
in (let _152_225 = (let _152_224 = (FStar_Format.text "->")
in (_152_224)::(body)::[])
in (_152_226)::_152_225))
in (_152_228)::_152_227))
in (FStar_Format.reduce1 _152_229))
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 421 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 422 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_242 = (let _152_241 = (let _152_236 = (let _152_235 = (FStar_Format.text "if")
in (let _152_234 = (let _152_233 = (let _152_232 = (FStar_Format.text "then")
in (let _152_231 = (let _152_230 = (FStar_Format.text "begin")
in (_152_230)::[])
in (_152_232)::_152_231))
in (cond)::_152_233)
in (_152_235)::_152_234))
in (FStar_Format.reduce1 _152_236))
in (let _152_240 = (let _152_239 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _152_238 = (let _152_237 = (FStar_Format.text "end")
in (_152_237)::[])
in (_152_239)::_152_238))
in (_152_241)::_152_240))
in (FStar_Format.combine FStar_Format.hardline _152_242))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 432 "FStar.Extraction.ML.Code.fst"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 433 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_265 = (let _152_264 = (let _152_249 = (let _152_248 = (FStar_Format.text "if")
in (let _152_247 = (let _152_246 = (let _152_245 = (FStar_Format.text "then")
in (let _152_244 = (let _152_243 = (FStar_Format.text "begin")
in (_152_243)::[])
in (_152_245)::_152_244))
in (cond)::_152_246)
in (_152_248)::_152_247))
in (FStar_Format.reduce1 _152_249))
in (let _152_263 = (let _152_262 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _152_261 = (let _152_260 = (let _152_255 = (let _152_254 = (FStar_Format.text "end")
in (let _152_253 = (let _152_252 = (FStar_Format.text "else")
in (let _152_251 = (let _152_250 = (FStar_Format.text "begin")
in (_152_250)::[])
in (_152_252)::_152_251))
in (_152_254)::_152_253))
in (FStar_Format.reduce1 _152_255))
in (let _152_259 = (let _152_258 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _152_257 = (let _152_256 = (FStar_Format.text "end")
in (_152_256)::[])
in (_152_258)::_152_257))
in (_152_260)::_152_259))
in (_152_262)::_152_261))
in (_152_264)::_152_263))
in (FStar_Format.combine FStar_Format.hardline _152_265))
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
let doc = (let _152_272 = (let _152_271 = (let _152_270 = (FStar_Format.text "match")
in (let _152_269 = (let _152_268 = (FStar_Format.parens cond)
in (let _152_267 = (let _152_266 = (FStar_Format.text "with")
in (_152_266)::[])
in (_152_268)::_152_267))
in (_152_270)::_152_269))
in (FStar_Format.reduce1 _152_271))
in (_152_272)::pats)
in (
# 448 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Format.combine FStar_Format.hardline doc)
in (FStar_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _152_277 = (let _152_276 = (FStar_Format.text "raise")
in (let _152_275 = (let _152_274 = (let _152_273 = (ptctor currentModule exn)
in (FStar_Format.text _152_273))
in (_152_274)::[])
in (_152_276)::_152_275))
in (FStar_Format.reduce1 _152_277))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 456 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _152_286 = (let _152_285 = (FStar_Format.text "raise")
in (let _152_284 = (let _152_283 = (let _152_278 = (ptctor currentModule exn)
in (FStar_Format.text _152_278))
in (let _152_282 = (let _152_281 = (let _152_280 = (let _152_279 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_279 args))
in (FStar_Format.parens _152_280))
in (_152_281)::[])
in (_152_283)::_152_282))
in (_152_285)::_152_284))
in (FStar_Format.reduce1 _152_286)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _152_303 = (let _152_302 = (let _152_290 = (let _152_289 = (FStar_Format.text "try")
in (let _152_288 = (let _152_287 = (FStar_Format.text "begin")
in (_152_287)::[])
in (_152_289)::_152_288))
in (FStar_Format.reduce1 _152_290))
in (let _152_301 = (let _152_300 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _152_299 = (let _152_298 = (let _152_294 = (let _152_293 = (FStar_Format.text "end")
in (let _152_292 = (let _152_291 = (FStar_Format.text "with")
in (_152_291)::[])
in (_152_293)::_152_292))
in (FStar_Format.reduce1 _152_294))
in (let _152_297 = (let _152_296 = (let _152_295 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FStar_Format.combine FStar_Format.hardline _152_295))
in (_152_296)::[])
in (_152_298)::_152_297))
in (_152_300)::_152_299))
in (_152_302)::_152_301))
in (FStar_Format.combine FStar_Format.hardline _152_303))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 e2 -> (
# 467 "FStar.Extraction.ML.Code.fst"
let _68_399 = (let _152_308 = (as_bin_op p)
in (FStar_Option.get _152_308))
in (match (_68_399) with
| (_68_396, prio, txt) -> begin
(
# 468 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 469 "FStar.Extraction.ML.Code.fst"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 470 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_311 = (let _152_310 = (let _152_309 = (FStar_Format.text txt)
in (_152_309)::(e2)::[])
in (e1)::_152_310)
in (FStar_Format.reduce1 _152_311))
in (FStar_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Format.doc = (fun currentModule p e1 -> (
# 474 "FStar.Extraction.ML.Code.fst"
let _68_409 = (let _152_315 = (as_uni_op p)
in (FStar_Option.get _152_315))
in (match (_68_409) with
| (_68_407, txt) -> begin
(
# 475 "FStar.Extraction.ML.Code.fst"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 476 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_319 = (let _152_318 = (FStar_Format.text txt)
in (let _152_317 = (let _152_316 = (FStar_Format.parens e1)
in (_152_316)::[])
in (_152_318)::_152_317))
in (FStar_Format.reduce1 _152_319))
in (FStar_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FStar_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FStar_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _152_322 = (string_of_mlconstant c)
in (FStar_Format.text _152_322))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FStar_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 486 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _68_426 -> (match (_68_426) with
| (name, p) -> begin
(let _152_331 = (let _152_330 = (let _152_325 = (ptsym currentModule (path, name))
in (FStar_Format.text _152_325))
in (let _152_329 = (let _152_328 = (FStar_Format.text "=")
in (let _152_327 = (let _152_326 = (doc_of_pattern currentModule p)
in (_152_326)::[])
in (_152_328)::_152_327))
in (_152_330)::_152_329))
in (FStar_Format.reduce1 _152_331))
end))
in (let _152_334 = (let _152_333 = (FStar_Format.text "; ")
in (let _152_332 = (FStar_List.map for1 fields)
in (FStar_Format.combine _152_333 _152_332)))
in (FStar_Format.cbrackets _152_334)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 490 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _152_336 = (let _152_335 = (as_standard_constructor ctor)
in (FStar_Option.get _152_335))
in (Prims.snd _152_336))
end else begin
(ptctor currentModule ctor)
end
in (FStar_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 498 "FStar.Extraction.ML.Code.fst"
let name = if (is_standard_constructor ctor) then begin
(let _152_338 = (let _152_337 = (as_standard_constructor ctor)
in (FStar_Option.get _152_337))
in (Prims.snd _152_338))
end else begin
(ptctor currentModule ctor)
end
in (
# 503 "FStar.Extraction.ML.Code.fst"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _152_344 = (let _152_343 = (doc_of_pattern currentModule x)
in (let _152_342 = (let _152_341 = (FStar_Format.text "::")
in (let _152_340 = (let _152_339 = (doc_of_pattern currentModule xs)
in (_152_339)::[])
in (_152_341)::_152_340))
in (_152_343)::_152_342))
in (FStar_Format.reduce _152_344))
end
| (_68_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_68_445)::[]) -> begin
(let _152_349 = (let _152_348 = (FStar_Format.text name)
in (let _152_347 = (let _152_346 = (let _152_345 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _152_345))
in (_152_346)::[])
in (_152_348)::_152_347))
in (FStar_Format.reduce1 _152_349))
end
| _68_450 -> begin
(let _152_356 = (let _152_355 = (FStar_Format.text name)
in (let _152_354 = (let _152_353 = (let _152_352 = (let _152_351 = (FStar_Format.text ", ")
in (let _152_350 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FStar_Format.combine _152_351 _152_350)))
in (FStar_Format.parens _152_352))
in (_152_353)::[])
in (_152_355)::_152_354))
in (FStar_Format.reduce1 _152_356))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 512 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _152_358 = (let _152_357 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_357 ps))
in (FStar_Format.parens _152_358)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 516 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 517 "FStar.Extraction.ML.Code.fst"
let ps = (FStar_List.map FStar_Format.parens ps)
in (let _152_359 = (FStar_Format.text " | ")
in (FStar_Format.combine _152_359 ps))))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FStar_Format.doc = (fun currentModule _68_463 -> (match (_68_463) with
| (p, cond, e) -> begin
(
# 522 "FStar.Extraction.ML.Code.fst"
let case = (match (cond) with
| None -> begin
(let _152_365 = (let _152_364 = (FStar_Format.text "|")
in (let _152_363 = (let _152_362 = (doc_of_pattern currentModule p)
in (_152_362)::[])
in (_152_364)::_152_363))
in (FStar_Format.reduce1 _152_365))
end
| Some (c) -> begin
(
# 526 "FStar.Extraction.ML.Code.fst"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _152_371 = (let _152_370 = (FStar_Format.text "|")
in (let _152_369 = (let _152_368 = (doc_of_pattern currentModule p)
in (let _152_367 = (let _152_366 = (FStar_Format.text "when")
in (_152_366)::(c)::[])
in (_152_368)::_152_367))
in (_152_370)::_152_369))
in (FStar_Format.reduce1 _152_371)))
end)
in (let _152_382 = (let _152_381 = (let _152_376 = (let _152_375 = (let _152_374 = (FStar_Format.text "->")
in (let _152_373 = (let _152_372 = (FStar_Format.text "begin")
in (_152_372)::[])
in (_152_374)::_152_373))
in (case)::_152_375)
in (FStar_Format.reduce1 _152_376))
in (let _152_380 = (let _152_379 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _152_378 = (let _152_377 = (FStar_Format.text "end")
in (_152_377)::[])
in (_152_379)::_152_378))
in (_152_381)::_152_380))
in (FStar_Format.combine FStar_Format.hardline _152_382)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FStar_Format.doc = (fun currentModule _68_473 -> (match (_68_473) with
| (rec_, top_level, lets) -> begin
(
# 537 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _68_481 -> (match (_68_481) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _68_478; FStar_Extraction_ML_Syntax.mllb_def = e; FStar_Extraction_ML_Syntax.print_typ = pt} -> begin
(
# 538 "FStar.Extraction.ML.Code.fst"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 539 "FStar.Extraction.ML.Code.fst"
let ids = []
in (
# 543 "FStar.Extraction.ML.Code.fst"
let ids = (FStar_List.map (fun _68_487 -> (match (_68_487) with
| (x, _68_486) -> begin
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
in (let _152_389 = (let _152_388 = (FStar_Format.text ":")
in (_152_388)::(ty)::[])
in (FStar_Format.reduce1 _152_389)))
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
in (let _152_391 = (let _152_390 = (FStar_Format.text ":")
in (_152_390)::(ty)::[])
in (FStar_Format.reduce1 _152_391)))
end)
end else begin
(FStar_Format.text "")
end
end
end
in (let _152_398 = (let _152_397 = (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _152_396 = (let _152_395 = (FStar_Format.reduce1 ids)
in (let _152_394 = (let _152_393 = (let _152_392 = (FStar_Format.text "=")
in (_152_392)::(e)::[])
in (ty_annot)::_152_393)
in (_152_395)::_152_394))
in (_152_397)::_152_396))
in (FStar_Format.reduce1 _152_398))))))
end))
in (
# 569 "FStar.Extraction.ML.Code.fst"
let letdoc = if rec_ then begin
(let _152_402 = (let _152_401 = (FStar_Format.text "let")
in (let _152_400 = (let _152_399 = (FStar_Format.text "rec")
in (_152_399)::[])
in (_152_401)::_152_400))
in (FStar_Format.reduce1 _152_402))
end else begin
(FStar_Format.text "let")
end
in (
# 571 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.map for1 lets)
in (
# 572 "FStar.Extraction.ML.Code.fst"
let lets = (FStar_List.mapi (fun i doc -> (let _152_406 = (let _152_405 = if (i = 0) then begin
letdoc
end else begin
(FStar_Format.text "and")
end
in (_152_405)::(doc)::[])
in (FStar_Format.reduce1 _152_406))) lets)
in (FStar_Format.combine FStar_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FStar_Format.doc = (fun _68_527 -> (match (_68_527) with
| (lineno, file) -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FStar_Format.empty
end else begin
(
# 583 "FStar.Extraction.ML.Code.fst"
let file = (FStar_Util.basename file)
in (let _152_413 = (let _152_412 = (FStar_Format.text "#")
in (let _152_411 = (let _152_410 = (FStar_Format.num lineno)
in (let _152_409 = (let _152_408 = (FStar_Format.text (Prims.strcat (Prims.strcat "\"" file) "\""))
in (_152_408)::[])
in (_152_410)::_152_409))
in (_152_412)::_152_411))
in (FStar_Format.reduce1 _152_413)))
end
end))

# 587 "FStar.Extraction.ML.Code.fst"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FStar_Format.doc = (fun currentModule decls -> (
# 588 "FStar.Extraction.ML.Code.fst"
let for1 = (fun _68_535 -> (match (_68_535) with
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
| _68_540 -> begin
(
# 594 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map (fun x -> (FStar_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _152_422 = (let _152_421 = (FStar_Format.text ", ")
in (FStar_Format.combine _152_421 doc))
in (FStar_Format.parens _152_422)))
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
let forfield = (fun _68_553 -> (match (_68_553) with
| (name, ty) -> begin
(
# 604 "FStar.Extraction.ML.Code.fst"
let name = (FStar_Format.text name)
in (
# 605 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _152_429 = (let _152_428 = (let _152_427 = (FStar_Format.text ":")
in (_152_427)::(ty)::[])
in (name)::_152_428)
in (FStar_Format.reduce1 _152_429))))
end))
in (let _152_432 = (let _152_431 = (FStar_Format.text "; ")
in (let _152_430 = (FStar_List.map forfield fields)
in (FStar_Format.combine _152_431 _152_430)))
in (FStar_Format.cbrackets _152_432)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 612 "FStar.Extraction.ML.Code.fst"
let forctor = (fun _68_561 -> (match (_68_561) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FStar_Format.text name)
end
| _68_564 -> begin
(
# 616 "FStar.Extraction.ML.Code.fst"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 617 "FStar.Extraction.ML.Code.fst"
let tys = (let _152_435 = (FStar_Format.text " * ")
in (FStar_Format.combine _152_435 tys))
in (let _152_439 = (let _152_438 = (FStar_Format.text name)
in (let _152_437 = (let _152_436 = (FStar_Format.text "of")
in (_152_436)::(tys)::[])
in (_152_438)::_152_437))
in (FStar_Format.reduce1 _152_439))))
end)
end))
in (
# 621 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map forctor ctors)
in (
# 622 "FStar.Extraction.ML.Code.fst"
let ctors = (FStar_List.map (fun d -> (let _152_442 = (let _152_441 = (FStar_Format.text "|")
in (_152_441)::(d)::[])
in (FStar_Format.reduce1 _152_442))) ctors)
in (FStar_Format.combine FStar_Format.hardline ctors))))
end))
in (
# 627 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_446 = (let _152_445 = (let _152_444 = (let _152_443 = (ptsym currentModule ([], x))
in (FStar_Format.text _152_443))
in (_152_444)::[])
in (tparams)::_152_445)
in (FStar_Format.reduce1 _152_446))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 632 "FStar.Extraction.ML.Code.fst"
let body = (forbody body)
in (let _152_451 = (let _152_450 = (let _152_449 = (let _152_448 = (let _152_447 = (FStar_Format.text "=")
in (_152_447)::[])
in (doc)::_152_448)
in (FStar_Format.reduce1 _152_449))
in (_152_450)::(body)::[])
in (FStar_Format.combine FStar_Format.hardline _152_451)))
end))))
end))
in (
# 637 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_List.map for1 decls)
in (
# 638 "FStar.Extraction.ML.Code.fst"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _152_456 = (let _152_455 = (FStar_Format.text "type")
in (let _152_454 = (let _152_453 = (let _152_452 = (FStar_Format.text " \n and ")
in (FStar_Format.combine _152_452 doc))
in (_152_453)::[])
in (_152_455)::_152_454))
in (FStar_Format.reduce1 _152_456))
end else begin
(FStar_Format.text "")
end
in doc))))

# 642 "FStar.Extraction.ML.Code.fst"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FStar_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _152_476 = (let _152_475 = (let _152_468 = (let _152_467 = (FStar_Format.text "module")
in (let _152_466 = (let _152_465 = (FStar_Format.text x)
in (let _152_464 = (let _152_463 = (FStar_Format.text "=")
in (_152_463)::[])
in (_152_465)::_152_464))
in (_152_467)::_152_466))
in (FStar_Format.reduce1 _152_468))
in (let _152_474 = (let _152_473 = (doc_of_sig currentModule subsig)
in (let _152_472 = (let _152_471 = (let _152_470 = (let _152_469 = (FStar_Format.text "end")
in (_152_469)::[])
in (FStar_Format.reduce1 _152_470))
in (_152_471)::[])
in (_152_473)::_152_472))
in (_152_475)::_152_474))
in (FStar_Format.combine FStar_Format.hardline _152_476))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _152_480 = (let _152_479 = (FStar_Format.text "exception")
in (let _152_478 = (let _152_477 = (FStar_Format.text x)
in (_152_477)::[])
in (_152_479)::_152_478))
in (FStar_Format.reduce1 _152_480))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 654 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 655 "FStar.Extraction.ML.Code.fst"
let args = (let _152_482 = (let _152_481 = (FStar_Format.text " * ")
in (FStar_Format.combine _152_481 args))
in (FStar_Format.parens _152_482))
in (let _152_488 = (let _152_487 = (FStar_Format.text "exception")
in (let _152_486 = (let _152_485 = (FStar_Format.text x)
in (let _152_484 = (let _152_483 = (FStar_Format.text "of")
in (_152_483)::(args)::[])
in (_152_485)::_152_484))
in (_152_487)::_152_486))
in (FStar_Format.reduce1 _152_488))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_68_595, ty)) -> begin
(
# 659 "FStar.Extraction.ML.Code.fst"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _152_494 = (let _152_493 = (FStar_Format.text "val")
in (let _152_492 = (let _152_491 = (FStar_Format.text x)
in (let _152_490 = (let _152_489 = (FStar_Format.text ": ")
in (_152_489)::(ty)::[])
in (_152_491)::_152_490))
in (_152_493)::_152_492))
in (FStar_Format.reduce1 _152_494)))
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

# 673 "FStar.Extraction.ML.Code.fst"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FStar_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _152_505 = (let _152_504 = (FStar_Format.text "exception")
in (let _152_503 = (let _152_502 = (FStar_Format.text x)
in (_152_502)::[])
in (_152_504)::_152_503))
in (FStar_Format.reduce1 _152_505))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 679 "FStar.Extraction.ML.Code.fst"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 680 "FStar.Extraction.ML.Code.fst"
let args = (let _152_507 = (let _152_506 = (FStar_Format.text " * ")
in (FStar_Format.combine _152_506 args))
in (FStar_Format.parens _152_507))
in (let _152_513 = (let _152_512 = (FStar_Format.text "exception")
in (let _152_511 = (let _152_510 = (FStar_Format.text x)
in (let _152_509 = (let _152_508 = (FStar_Format.text "of")
in (_152_508)::(args)::[])
in (_152_510)::_152_509))
in (_152_512)::_152_511))
in (FStar_Format.reduce1 _152_513))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _152_521 = (let _152_520 = (FStar_Format.text "let")
in (let _152_519 = (let _152_518 = (FStar_Format.text "_")
in (let _152_517 = (let _152_516 = (FStar_Format.text "=")
in (let _152_515 = (let _152_514 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_152_514)::[])
in (_152_516)::_152_515))
in (_152_518)::_152_517))
in (_152_520)::_152_519))
in (FStar_Format.reduce1 _152_521))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 699 "FStar.Extraction.ML.Code.fst"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FStar_Format.doc = (fun currentModule m -> (
# 700 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun x -> (
# 701 "FStar.Extraction.ML.Code.fst"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_68_635) -> begin
FStar_Format.empty
end
| _68_638 -> begin
FStar_Format.hardline
end))::(FStar_Format.hardline)::[])) m)
in (FStar_Format.reduce (FStar_List.flatten docs))))

# 706 "FStar.Extraction.ML.Code.fst"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun _68_641 -> (match (_68_641) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 707 "FStar.Extraction.ML.Code.fst"
let rec for1_sig = (fun _68_648 -> (match (_68_648) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 708 "FStar.Extraction.ML.Code.fst"
let head = (let _152_540 = (let _152_539 = (FStar_Format.text "module")
in (let _152_538 = (let _152_537 = (FStar_Format.text x)
in (let _152_536 = (let _152_535 = (FStar_Format.text ":")
in (let _152_534 = (let _152_533 = (FStar_Format.text "sig")
in (_152_533)::[])
in (_152_535)::_152_534))
in (_152_537)::_152_536))
in (_152_539)::_152_538))
in (FStar_Format.reduce1 _152_540))
in (
# 709 "FStar.Extraction.ML.Code.fst"
let tail = (let _152_542 = (let _152_541 = (FStar_Format.text "end")
in (_152_541)::[])
in (FStar_Format.reduce1 _152_542))
in (
# 710 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _68_654 -> (match (_68_654) with
| (s, _68_653) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 711 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map for1_sig sub)
in (
# 712 "FStar.Extraction.ML.Code.fst"
let sub = (FStar_List.map (fun x -> (FStar_Format.reduce ((x)::(FStar_Format.hardline)::(FStar_Format.hardline)::[]))) sub)
in (let _152_552 = (let _152_551 = (FStar_Format.cat head FStar_Format.hardline)
in (let _152_550 = (let _152_549 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _152_548 = (let _152_547 = (FStar_Format.reduce sub)
in (let _152_546 = (let _152_545 = (FStar_Format.cat tail FStar_Format.hardline)
in (_152_545)::[])
in (_152_547)::_152_546))
in (_152_549)::_152_548))
in (_152_551)::_152_550))
in (FStar_Format.reduce _152_552)))))))
end))
and for1_mod = (fun istop _68_667 -> (match (_68_667) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 723 "FStar.Extraction.ML.Code.fst"
let head = (let _152_565 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _152_557 = (FStar_Format.text "module")
in (let _152_556 = (let _152_555 = (FStar_Format.text x)
in (_152_555)::[])
in (_152_557)::_152_556))
end else begin
if (not (istop)) then begin
(let _152_564 = (FStar_Format.text "module")
in (let _152_563 = (let _152_562 = (FStar_Format.text x)
in (let _152_561 = (let _152_560 = (FStar_Format.text "=")
in (let _152_559 = (let _152_558 = (FStar_Format.text "struct")
in (_152_558)::[])
in (_152_560)::_152_559))
in (_152_562)::_152_561))
in (_152_564)::_152_563))
end else begin
[]
end
end
in (FStar_Format.reduce1 _152_565))
in (
# 728 "FStar.Extraction.ML.Code.fst"
let tail = if (not (istop)) then begin
(let _152_567 = (let _152_566 = (FStar_Format.text "end")
in (_152_566)::[])
in (FStar_Format.reduce1 _152_567))
end else begin
(FStar_Format.reduce1 [])
end
in (
# 731 "FStar.Extraction.ML.Code.fst"
let doc = (FStar_Option.map (fun _68_673 -> (match (_68_673) with
| (_68_671, m) -> begin
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
(let _152_571 = (let _152_570 = (FStar_Format.text "#light \"off\"")
in (FStar_Format.cat _152_570 FStar_Format.hardline))
in (_152_571)::[])
end else begin
[]
end
in (let _152_583 = (let _152_582 = (let _152_581 = (let _152_580 = (let _152_579 = (FStar_Format.text "open Prims")
in (let _152_578 = (let _152_577 = (let _152_576 = (match (doc) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.cat s FStar_Format.hardline)
end)
in (let _152_575 = (let _152_574 = (FStar_Format.reduce sub)
in (let _152_573 = (let _152_572 = (FStar_Format.cat tail FStar_Format.hardline)
in (_152_572)::[])
in (_152_574)::_152_573))
in (_152_576)::_152_575))
in (FStar_Format.hardline)::_152_577)
in (_152_579)::_152_578))
in (FStar_Format.hardline)::_152_580)
in (head)::_152_581)
in (FStar_List.append prefix _152_582))
in (FStar_All.pipe_left FStar_Format.reduce _152_583))))))))
end))
in (
# 750 "FStar.Extraction.ML.Code.fst"
let docs = (FStar_List.map (fun _68_685 -> (match (_68_685) with
| (x, s, m) -> begin
(let _152_585 = (for1_mod true (x, s, m))
in (x, _152_585))
end)) mllib)
in docs))
end))

# 754 "FStar.Extraction.ML.Code.fst"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FStar_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 757 "FStar.Extraction.ML.Code.fst"
let string_of_mlexpr : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun cmod e -> (
# 758 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_592 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_expr _152_592 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))

# 761 "FStar.Extraction.ML.Code.fst"
let string_of_mlty : FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun cmod e -> (
# 762 "FStar.Extraction.ML.Code.fst"
let doc = (let _152_597 = (FStar_Extraction_ML_Util.flatten_mlpath cmod)
in (doc_of_mltype _152_597 (min_op_prec, NonAssoc) e))
in (FStar_Format.pretty 0 doc)))





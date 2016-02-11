
open Prims
# 30 "codegen.fs"
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

# 30 "codegen.fs"
let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "codegen.fs"
let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "codegen.fs"
let is_Left = (fun _discr_ -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "codegen.fs"
let is_Right = (fun _discr_ -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))

# 30 "codegen.fs"
let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "codegen.fs"
type fixity =
| Prefix
| Postfix
| Infix of assoc

# 31 "codegen.fs"
let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "codegen.fs"
let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "codegen.fs"
let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

# 31 "codegen.fs"
let ___Infix____0 : fixity  ->  assoc = (fun projectee -> (match (projectee) with
| Infix (_77_3) -> begin
_77_3
end))

# 32 "codegen.fs"
type opprec =
(Prims.int * fixity)

# 33 "codegen.fs"
type level =
(opprec * assoc)

# 35 "codegen.fs"
let t_prio_fun : (Prims.int * fixity) = (10, Infix (Right))

# 36 "codegen.fs"
let t_prio_tpl : (Prims.int * fixity) = (20, Infix (NonAssoc))

# 37 "codegen.fs"
let t_prio_name : (Prims.int * fixity) = (30, Postfix)

# 39 "codegen.fs"
let e_bin_prio_lambda : (Prims.int * fixity) = (5, Prefix)

# 40 "codegen.fs"
let e_bin_prio_if : (Prims.int * fixity) = (15, Prefix)

# 41 "codegen.fs"
let e_bin_prio_letin : (Prims.int * fixity) = (19, Prefix)

# 42 "codegen.fs"
let e_bin_prio_or : (Prims.int * fixity) = (20, Infix (Left))

# 43 "codegen.fs"
let e_bin_prio_and : (Prims.int * fixity) = (25, Infix (Left))

# 44 "codegen.fs"
let e_bin_prio_eq : (Prims.int * fixity) = (27, Infix (NonAssoc))

# 45 "codegen.fs"
let e_bin_prio_order : (Prims.int * fixity) = (29, Infix (NonAssoc))

# 46 "codegen.fs"
let e_bin_prio_op1 : (Prims.int * fixity) = (30, Infix (Left))

# 47 "codegen.fs"
let e_bin_prio_op2 : (Prims.int * fixity) = (40, Infix (Left))

# 48 "codegen.fs"
let e_bin_prio_op3 : (Prims.int * fixity) = (50, Infix (Left))

# 49 "codegen.fs"
let e_bin_prio_op4 : (Prims.int * fixity) = (60, Infix (Left))

# 50 "codegen.fs"
let e_bin_prio_comb : (Prims.int * fixity) = (70, Infix (Left))

# 51 "codegen.fs"
let e_bin_prio_seq : (Prims.int * fixity) = (100, Infix (Left))

# 52 "codegen.fs"
let e_app_prio : (Prims.int * fixity) = (10000, Infix (Left))

# 54 "codegen.fs"
let min_op_prec : (Prims.int * fixity) = ((- (1)), Infix (NonAssoc))

# 55 "codegen.fs"
let max_op_prec : (Prims.int * fixity) = (FStar_Util.max_int, Infix (NonAssoc))

# 61 "codegen.fs"
let rec in_ns = (fun x -> (match (x) with
| ([], _77_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_77_18, _77_20) -> begin
false
end))

# 67 "codegen.fs"
let path_of_ns : FStar_Extraction_ML_Syntax.mlsymbol  ->  Prims.string Prims.list  ->  Prims.string Prims.list = (fun currentModule ns -> (
# 68 "codegen.fs"
let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(
# 71 "codegen.fs"
let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (
# 72 "codegen.fs"
let ns_len = (FStar_List.length ns)
in (
# 73 "codegen.fs"
let found = (FStar_Util.find_map cg_libs (fun cg_path -> (
# 74 "codegen.fs"
let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(
# 76 "codegen.fs"
let _77_31 = (FStar_Util.first_N cg_len ns)
in (match (_77_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _179_31 = (let _179_30 = (let _179_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_179_29)::[])
in (FStar_List.append pfx _179_30))
in Some (_179_31))
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

# 85 "codegen.fs"
let mlpath_of_mlpath : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _77_41 -> begin
(
# 90 "codegen.fs"
let _77_44 = x
in (match (_77_44) with
| (ns, x) -> begin
(let _179_36 = (path_of_ns currentModule ns)
in (_179_36, x))
end))
end))

# 93 "codegen.fs"
let ptsym_of_symbol : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun s -> if ((let _179_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _179_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

# 98 "codegen.fs"
let ptsym : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(
# 102 "codegen.fs"
let _77_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_50) with
| (p, s) -> begin
(let _179_46 = (let _179_45 = (let _179_44 = (ptsym_of_symbol s)
in (_179_44)::[])
in (FStar_List.append p _179_45))
in (FStar_String.concat "." _179_46))
end))
end)

# 106 "codegen.fs"
let ptctor : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlsymbol = (fun currentModule mlp -> (
# 107 "codegen.fs"
let _77_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_77_55) with
| (p, s) -> begin
(
# 108 "codegen.fs"
let s = if ((let _179_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _179_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

# 112 "codegen.fs"
let infix_prim_ops : (Prims.string * (Prims.int * fixity) * Prims.string) Prims.list = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

# 130 "codegen.fs"
let prim_uni_ops : (Prims.string * Prims.string) Prims.list = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

# 137 "codegen.fs"
let prim_types = []

# 140 "codegen.fs"
let prim_constructors : (Prims.string * Prims.string) Prims.list = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

# 148 "codegen.fs"
let is_prims_ns : FStar_Extraction_ML_Syntax.mlsymbol Prims.list  ->  Prims.bool = (fun ns -> (ns = ("Prims")::[]))

# 152 "codegen.fs"
let as_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * (Prims.int * fixity) * Prims.string) Prims.option = (fun _77_60 -> (match (_77_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_66 -> (match (_77_66) with
| (y, _77_63, _77_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

# 159 "codegen.fs"
let is_bin_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_bin_op p) <> None))

# 163 "codegen.fs"
let as_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_70 -> (match (_77_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_74 -> (match (_77_74) with
| (y, _77_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

# 170 "codegen.fs"
let is_uni_op : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_uni_op p) <> None))

# 174 "codegen.fs"
let as_standard_type = (fun _77_78 -> (match (_77_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_82 -> (match (_77_82) with
| (y, _77_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

# 181 "codegen.fs"
let is_standard_type : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_type p) <> None))

# 185 "codegen.fs"
let as_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  (Prims.string * Prims.string) Prims.option = (fun _77_86 -> (match (_77_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _77_90 -> (match (_77_90) with
| (y, _77_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

# 192 "codegen.fs"
let is_standard_constructor : FStar_Extraction_ML_Syntax.mlpath  ->  Prims.bool = (fun p -> ((as_standard_constructor p) <> None))

# 196 "codegen.fs"
let maybe_paren : ((Prims.int * fixity) * assoc)  ->  (Prims.int * fixity)  ->  FSharp_Format.doc  ->  FSharp_Format.doc = (fun _77_94 inner doc -> (match (_77_94) with
| (outer, side) -> begin
(
# 197 "codegen.fs"
let noparens = (fun _inner _outer side -> (
# 198 "codegen.fs"
let _77_103 = _inner
in (match (_77_103) with
| (pi, fi) -> begin
(
# 199 "codegen.fs"
let _77_106 = _outer
in (match (_77_106) with
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
| (_77_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_77_134, _77_136) -> begin
false
end))
end))
end)))
in if (noparens inner outer side) then begin
doc
end else begin
(FSharp_Format.parens doc)
end)
end))

# 215 "codegen.fs"
let ocaml_u8_codepoint : Prims.byte  ->  Prims.string = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

# 219 "codegen.fs"
let encode_char : Prims.char  ->  Prims.string = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(
# 221 "codegen.fs"
let bytes = (FStar_Util.string_of_char c)
in (
# 222 "codegen.fs"
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
| _77_154 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end)

# 240 "codegen.fs"
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
(let _179_92 = (let _179_91 = (encode_char c)
in (Prims.strcat "\'" _179_91))
in (Prims.strcat _179_92 "\'"))
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
# 255 "codegen.fs"
let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(
# 259 "codegen.fs"
let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

# 264 "codegen.fs"
let rec doc_of_mltype' : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FSharp_Format.doc = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(
# 267 "codegen.fs"
let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _179_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _179_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(
# 274 "codegen.fs"
let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 275 "codegen.fs"
let doc = (let _179_106 = (let _179_105 = (FSharp_Format.combine (FSharp_Format.text " * ") doc)
in (FSharp_Format.hbox _179_105))
in (FSharp_Format.parens _179_106))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(
# 279 "codegen.fs"
let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _77_198 -> begin
(
# 284 "codegen.fs"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _179_108 = (let _179_107 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.hbox _179_107))
in (FSharp_Format.parens _179_108)))
end)
in (
# 289 "codegen.fs"
let name = if (is_standard_type name) then begin
(let _179_110 = (let _179_109 = (as_standard_type name)
in (FStar_Option.get _179_109))
in (Prims.snd _179_110))
end else begin
(ptsym currentModule name)
end
in (let _179_111 = (FSharp_Format.reduce1 ((args)::((FSharp_Format.text name))::[]))
in (FSharp_Format.hbox _179_111))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _77_204, t2) -> begin
(
# 299 "codegen.fs"
let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (
# 300 "codegen.fs"
let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _179_113 = (let _179_112 = (FSharp_Format.reduce1 ((d1)::((FSharp_Format.text " -> "))::(d2)::[]))
in (FSharp_Format.hbox _179_112))
in (maybe_paren outer t_prio_fun _179_113))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.text "obj")
end else begin
(FSharp_Format.text "Obj.t")
end
end))
and doc_of_mltype : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlty  ->  FSharp_Format.doc = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

# 312 "codegen.fs"
let rec doc_of_expr : FStar_Extraction_ML_Syntax.mlsymbol  ->  level  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(
# 315 "codegen.fs"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_137 = (FSharp_Format.reduce (((FSharp_Format.text "Prims.checked_cast"))::(doc)::[]))
in (FSharp_Format.parens _179_137))
end else begin
(let _179_138 = (FSharp_Format.reduce (((FSharp_Format.text "Obj.magic "))::((FSharp_Format.parens doc))::[]))
in (FSharp_Format.parens _179_138))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(
# 321 "codegen.fs"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 322 "codegen.fs"
let docs = (FStar_List.map (fun d -> (FSharp_Format.reduce ((d)::((FSharp_Format.text ";"))::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _179_140 = (string_of_mlconstant c)
in (FSharp_Format.text _179_140))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _77_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _179_141 = (ptsym currentModule path)
in (FSharp_Format.text _179_141))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(
# 335 "codegen.fs"
let for1 = (fun _77_244 -> (match (_77_244) with
| (name, e) -> begin
(
# 336 "codegen.fs"
let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_146 = (let _179_145 = (let _179_144 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_144))
in (_179_145)::((FSharp_Format.text "="))::(doc)::[])
in (FSharp_Format.reduce1 _179_146)))
end))
in (let _179_148 = (let _179_147 = (FStar_List.map for1 fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_147))
in (FSharp_Format.cbrackets _179_148)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(
# 342 "codegen.fs"
let name = if (is_standard_constructor ctor) then begin
(let _179_150 = (let _179_149 = (as_standard_constructor ctor)
in (FStar_Option.get _179_149))
in (Prims.snd _179_150))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(
# 350 "codegen.fs"
let name = if (is_standard_constructor ctor) then begin
(let _179_152 = (let _179_151 = (as_standard_constructor ctor)
in (FStar_Option.get _179_151))
in (Prims.snd _179_152))
end else begin
(ptctor currentModule ctor)
end
in (
# 355 "codegen.fs"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (
# 356 "codegen.fs"
let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(FSharp_Format.reduce (((FSharp_Format.parens x))::((FSharp_Format.text "::"))::(xs)::[]))
end
| (_77_263, _77_265) -> begin
(let _179_156 = (let _179_155 = (let _179_154 = (let _179_153 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.parens _179_153))
in (_179_154)::[])
in ((FSharp_Format.text name))::_179_155)
in (FSharp_Format.reduce1 _179_156))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(
# 364 "codegen.fs"
let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (
# 365 "codegen.fs"
let docs = (let _179_157 = (FSharp_Format.combine (FSharp_Format.text ", ") docs)
in (FSharp_Format.parens _179_157))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(
# 369 "codegen.fs"
let pre = if (e.FStar_Extraction_ML_Syntax.loc <> FStar_Extraction_ML_Syntax.dummy_loc) then begin
(let _179_160 = (let _179_159 = (let _179_158 = (doc_of_loc e.FStar_Extraction_ML_Syntax.loc)
in (_179_158)::[])
in (FSharp_Format.hardline)::_179_159)
in (FSharp_Format.reduce _179_160))
end else begin
FSharp_Format.empty
end
in (
# 374 "codegen.fs"
let doc = (doc_of_lets currentModule (rec_, false, lets))
in (
# 375 "codegen.fs"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _179_165 = (let _179_164 = (let _179_163 = (let _179_162 = (let _179_161 = (FSharp_Format.reduce1 (((FSharp_Format.text "in"))::(body)::[]))
in (_179_161)::[])
in (doc)::_179_162)
in (pre)::_179_163)
in (FSharp_Format.combine FSharp_Format.hardline _179_164))
in (FSharp_Format.parens _179_165)))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _77_294; FStar_Extraction_ML_Syntax.loc = _77_292}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _77_314; FStar_Extraction_ML_Syntax.loc = _77_312}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _77_326 -> begin
(
# 390 "codegen.fs"
let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (
# 391 "codegen.fs"
let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _179_166 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _179_166))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(
# 396 "codegen.fs"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 397 "codegen.fs"
let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.reduce ((e)::((FSharp_Format.text "."))::((FSharp_Format.text (Prims.snd f)))::[]))
end else begin
(let _179_171 = (let _179_170 = (let _179_169 = (let _179_168 = (let _179_167 = (ptsym currentModule f)
in (FSharp_Format.text _179_167))
in (_179_168)::[])
in ((FSharp_Format.text "."))::_179_169)
in (e)::_179_170)
in (FSharp_Format.reduce _179_171))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(
# 404 "codegen.fs"
let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _179_182 = (let _179_181 = (let _179_180 = (let _179_179 = (match (xt) with
| Some (xxt) -> begin
(let _179_178 = (let _179_177 = (let _179_176 = (doc_of_mltype currentModule outer xxt)
in (_179_176)::[])
in ((FSharp_Format.text " : "))::_179_177)
in (FSharp_Format.reduce1 _179_178))
end
| _77_345 -> begin
(FSharp_Format.text "")
end)
in (_179_179)::((FSharp_Format.text ")"))::[])
in ((FSharp_Format.text x))::_179_180)
in ((FSharp_Format.text "("))::_179_181)
in (FSharp_Format.reduce1 _179_182))
end else begin
(FSharp_Format.text x)
end)
in (
# 410 "codegen.fs"
let ids = (FStar_List.map (fun _77_351 -> (match (_77_351) with
| ((x, _77_348), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (
# 411 "codegen.fs"
let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (
# 412 "codegen.fs"
let doc = (let _179_186 = (let _179_185 = (let _179_184 = (FSharp_Format.reduce1 ids)
in (_179_184)::((FSharp_Format.text "->"))::(body)::[])
in ((FSharp_Format.text "fun"))::_179_185)
in (FSharp_Format.reduce1 _179_186))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(
# 416 "codegen.fs"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 417 "codegen.fs"
let doc = (let _179_190 = (let _179_189 = (FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[]))
in (let _179_188 = (let _179_187 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (_179_187)::((FSharp_Format.text "end"))::[])
in (_179_189)::_179_188))
in (FSharp_Format.combine FSharp_Format.hardline _179_190))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(
# 427 "codegen.fs"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 428 "codegen.fs"
let doc = (let _179_198 = (let _179_197 = (FSharp_Format.reduce1 (((FSharp_Format.text "if"))::(cond)::((FSharp_Format.text "then"))::((FSharp_Format.text "begin"))::[]))
in (let _179_196 = (let _179_195 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _179_194 = (let _179_193 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "else"))::((FSharp_Format.text "begin"))::[]))
in (let _179_192 = (let _179_191 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (_179_191)::((FSharp_Format.text "end"))::[])
in (_179_193)::_179_192))
in (_179_195)::_179_194))
in (_179_197)::_179_196))
in (FSharp_Format.combine FSharp_Format.hardline _179_198))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(
# 440 "codegen.fs"
let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (
# 441 "codegen.fs"
let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (
# 442 "codegen.fs"
let doc = (let _179_199 = (FSharp_Format.reduce1 (((FSharp_Format.text "match"))::((FSharp_Format.parens cond))::((FSharp_Format.text "with"))::[]))
in (_179_199)::pats)
in (
# 443 "codegen.fs"
let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _179_203 = (let _179_202 = (let _179_201 = (let _179_200 = (ptctor currentModule exn)
in (FSharp_Format.text _179_200))
in (_179_201)::[])
in ((FSharp_Format.text "raise"))::_179_202)
in (FSharp_Format.reduce1 _179_203))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(
# 451 "codegen.fs"
let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _179_210 = (let _179_209 = (let _179_208 = (let _179_204 = (ptctor currentModule exn)
in (FSharp_Format.text _179_204))
in (let _179_207 = (let _179_206 = (let _179_205 = (FSharp_Format.combine (FSharp_Format.text ", ") args)
in (FSharp_Format.parens _179_205))
in (_179_206)::[])
in (_179_208)::_179_207))
in ((FSharp_Format.text "raise"))::_179_209)
in (FSharp_Format.reduce1 _179_210)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _179_219 = (let _179_218 = (FSharp_Format.reduce1 (((FSharp_Format.text "try"))::((FSharp_Format.text "begin"))::[]))
in (let _179_217 = (let _179_216 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _179_215 = (let _179_214 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::((FSharp_Format.text "with"))::[]))
in (let _179_213 = (let _179_212 = (let _179_211 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _179_211))
in (_179_212)::[])
in (_179_214)::_179_213))
in (_179_216)::_179_215))
in (_179_218)::_179_217))
in (FSharp_Format.combine FSharp_Format.hardline _179_219))
end))
and doc_of_binop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 e2 -> (
# 462 "codegen.fs"
let _77_399 = (let _179_224 = (as_bin_op p)
in (FStar_Option.get _179_224))
in (match (_77_399) with
| (_77_396, prio, txt) -> begin
(
# 463 "codegen.fs"
let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (
# 464 "codegen.fs"
let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (
# 465 "codegen.fs"
let doc = (FSharp_Format.reduce1 ((e1)::((FSharp_Format.text txt))::(e2)::[]))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpath  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  FSharp_Format.doc = (fun currentModule p e1 -> (
# 469 "codegen.fs"
let _77_409 = (let _179_228 = (as_uni_op p)
in (FStar_Option.get _179_228))
in (match (_77_409) with
| (_77_407, txt) -> begin
(
# 470 "codegen.fs"
let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (
# 471 "codegen.fs"
let doc = (FSharp_Format.reduce1 (((FSharp_Format.text txt))::((FSharp_Format.parens e1))::[]))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlpattern  ->  FSharp_Format.doc = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _179_231 = (string_of_mlconstant c)
in (FSharp_Format.text _179_231))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(
# 481 "codegen.fs"
let for1 = (fun _77_426 -> (match (_77_426) with
| (name, p) -> begin
(let _179_239 = (let _179_238 = (let _179_234 = (ptsym currentModule (path, name))
in (FSharp_Format.text _179_234))
in (let _179_237 = (let _179_236 = (let _179_235 = (doc_of_pattern currentModule p)
in (_179_235)::[])
in ((FSharp_Format.text "="))::_179_236)
in (_179_238)::_179_237))
in (FSharp_Format.reduce1 _179_239))
end))
in (let _179_241 = (let _179_240 = (FStar_List.map for1 fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_240))
in (FSharp_Format.cbrackets _179_241)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(
# 485 "codegen.fs"
let name = if (is_standard_constructor ctor) then begin
(let _179_243 = (let _179_242 = (as_standard_constructor ctor)
in (FStar_Option.get _179_242))
in (Prims.snd _179_243))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(
# 493 "codegen.fs"
let name = if (is_standard_constructor ctor) then begin
(let _179_245 = (let _179_244 = (as_standard_constructor ctor)
in (FStar_Option.get _179_244))
in (Prims.snd _179_245))
end else begin
(ptctor currentModule ctor)
end
in (
# 498 "codegen.fs"
let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _179_250 = (let _179_249 = (doc_of_pattern currentModule x)
in (let _179_248 = (let _179_247 = (let _179_246 = (doc_of_pattern currentModule xs)
in (_179_246)::[])
in ((FSharp_Format.text "::"))::_179_247)
in (_179_249)::_179_248))
in (FSharp_Format.reduce _179_250))
end
| (_77_443, FStar_Extraction_ML_Syntax.MLP_Tuple (_77_445)::[]) -> begin
(let _179_254 = (let _179_253 = (let _179_252 = (let _179_251 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _179_251))
in (_179_252)::[])
in ((FSharp_Format.text name))::_179_253)
in (FSharp_Format.reduce1 _179_254))
end
| _77_450 -> begin
(let _179_259 = (let _179_258 = (let _179_257 = (let _179_256 = (let _179_255 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine (FSharp_Format.text ", ") _179_255))
in (FSharp_Format.parens _179_256))
in (_179_257)::[])
in ((FSharp_Format.text name))::_179_258)
in (FSharp_Format.reduce1 _179_259))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(
# 507 "codegen.fs"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _179_260 = (FSharp_Format.combine (FSharp_Format.text ", ") ps)
in (FSharp_Format.parens _179_260)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(
# 511 "codegen.fs"
let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (
# 512 "codegen.fs"
let ps = (FStar_List.map FSharp_Format.parens ps)
in (FSharp_Format.combine (FSharp_Format.text " | ") ps)))
end))
and doc_of_branch : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlbranch  ->  FSharp_Format.doc = (fun currentModule _77_463 -> (match (_77_463) with
| (p, cond, e) -> begin
(
# 517 "codegen.fs"
let case = (match (cond) with
| None -> begin
(let _179_265 = (let _179_264 = (let _179_263 = (doc_of_pattern currentModule p)
in (_179_263)::[])
in ((FSharp_Format.text "|"))::_179_264)
in (FSharp_Format.reduce1 _179_265))
end
| Some (c) -> begin
(
# 521 "codegen.fs"
let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _179_268 = (let _179_267 = (let _179_266 = (doc_of_pattern currentModule p)
in (_179_266)::((FSharp_Format.text "when"))::(c)::[])
in ((FSharp_Format.text "|"))::_179_267)
in (FSharp_Format.reduce1 _179_268)))
end)
in (let _179_272 = (let _179_271 = (FSharp_Format.reduce1 ((case)::((FSharp_Format.text "->"))::((FSharp_Format.text "begin"))::[]))
in (let _179_270 = (let _179_269 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_179_269)::((FSharp_Format.text "end"))::[])
in (_179_271)::_179_270))
in (FSharp_Format.combine FSharp_Format.hardline _179_272)))
end))
and doc_of_lets : FStar_Extraction_ML_Syntax.mlsymbol  ->  (Prims.bool * Prims.bool * FStar_Extraction_ML_Syntax.mllb Prims.list)  ->  FSharp_Format.doc = (fun currentModule _77_473 -> (match (_77_473) with
| (rec_, top_level, lets) -> begin
(
# 532 "codegen.fs"
let for1 = (fun _77_480 -> (match (_77_480) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _77_477; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(
# 533 "codegen.fs"
let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (
# 534 "codegen.fs"
let ids = []
in (
# 538 "codegen.fs"
let ids = (FStar_List.map (fun _77_486 -> (match (_77_486) with
| (x, _77_485) -> begin
(FSharp_Format.text x)
end)) ids)
in (
# 539 "codegen.fs"
let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (Some (_::_, _)) | (None) -> begin
(FSharp_Format.text "")
end
| Some ([], ty) -> begin
(
# 545 "codegen.fs"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 (((FSharp_Format.text ":"))::(ty)::[])))
end)
end else begin
if top_level then begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FSharp_Format.text "")
end
| Some ([], ty) -> begin
(
# 556 "codegen.fs"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 (((FSharp_Format.text ":"))::(ty)::[])))
end)
end else begin
(FSharp_Format.text "")
end
end
in (let _179_280 = (let _179_279 = (let _179_278 = (FSharp_Format.reduce1 ids)
in (_179_278)::(ty_annot)::((FSharp_Format.text "="))::(e)::[])
in ((FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name)))::_179_279)
in (FSharp_Format.reduce1 _179_280))))))
end))
in (
# 562 "codegen.fs"
let letdoc = if rec_ then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "let"))::((FSharp_Format.text "rec"))::[]))
end else begin
(FSharp_Format.text "let")
end
in (
# 564 "codegen.fs"
let lets = (FStar_List.map for1 lets)
in (
# 565 "codegen.fs"
let lets = (FStar_List.mapi (fun i doc -> (FSharp_Format.reduce1 ((if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end)::(doc)::[]))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))
and doc_of_loc : FStar_Extraction_ML_Syntax.mlloc  ->  FSharp_Format.doc = (fun _77_526 -> (match (_77_526) with
| (lineno, file) -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
FSharp_Format.empty
end else begin
(
# 576 "codegen.fs"
let file = (FStar_Util.basename file)
in (FSharp_Format.reduce1 (((FSharp_Format.text "#"))::((FSharp_Format.num lineno))::((FSharp_Format.text (Prims.strcat (Prims.strcat "\"" file) "\"")))::[])))
end
end))

# 580 "codegen.fs"
let doc_of_mltydecl : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mltydecl  ->  FSharp_Format.doc = (fun currentModule decls -> (
# 581 "codegen.fs"
let for1 = (fun _77_534 -> (match (_77_534) with
| (x, tparams, body) -> begin
(
# 582 "codegen.fs"
let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _77_539 -> begin
(
# 587 "codegen.fs"
let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _179_291 = (FSharp_Format.combine (FSharp_Format.text ", ") doc)
in (FSharp_Format.parens _179_291)))
end)
in (
# 590 "codegen.fs"
let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(
# 596 "codegen.fs"
let forfield = (fun _77_552 -> (match (_77_552) with
| (name, ty) -> begin
(
# 597 "codegen.fs"
let name = (FSharp_Format.text name)
in (
# 598 "codegen.fs"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 ((name)::((FSharp_Format.text ":"))::(ty)::[]))))
end))
in (let _179_297 = (let _179_296 = (FStar_List.map forfield fields)
in (FSharp_Format.combine (FSharp_Format.text "; ") _179_296))
in (FSharp_Format.cbrackets _179_297)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(
# 605 "codegen.fs"
let forctor = (fun _77_560 -> (match (_77_560) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _77_563 -> begin
(
# 609 "codegen.fs"
let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (
# 610 "codegen.fs"
let tys = (FSharp_Format.combine (FSharp_Format.text " * ") tys)
in (FSharp_Format.reduce1 (((FSharp_Format.text name))::((FSharp_Format.text "of"))::(tys)::[]))))
end)
end))
in (
# 614 "codegen.fs"
let ctors = (FStar_List.map forctor ctors)
in (
# 615 "codegen.fs"
let ctors = (FStar_List.map (fun d -> (FSharp_Format.reduce1 (((FSharp_Format.text "|"))::(d)::[]))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (
# 620 "codegen.fs"
let doc = (let _179_304 = (let _179_303 = (let _179_302 = (let _179_301 = (ptsym currentModule ([], x))
in (FSharp_Format.text _179_301))
in (_179_302)::[])
in (tparams)::_179_303)
in (FSharp_Format.reduce1 _179_304))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(
# 625 "codegen.fs"
let body = (forbody body)
in (let _179_306 = (let _179_305 = (FSharp_Format.reduce1 ((doc)::((FSharp_Format.text "="))::[]))
in (_179_305)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _179_306)))
end))))
end))
in (
# 630 "codegen.fs"
let doc = (FStar_List.map for1 decls)
in (
# 631 "codegen.fs"
let doc = if ((FStar_List.length doc) > 0) then begin
(let _179_309 = (let _179_308 = (let _179_307 = (FSharp_Format.combine (FSharp_Format.text " \n and ") doc)
in (_179_307)::[])
in ((FSharp_Format.text "type"))::_179_308)
in (FSharp_Format.reduce1 _179_309))
end else begin
(FSharp_Format.text "")
end
in doc))))

# 635 "codegen.fs"
let rec doc_of_sig1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig1  ->  FSharp_Format.doc = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _179_321 = (let _179_320 = (FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::[]))
in (let _179_319 = (let _179_318 = (doc_of_sig currentModule subsig)
in (let _179_317 = (let _179_316 = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
in (_179_316)::[])
in (_179_318)::_179_317))
in (_179_320)::_179_319))
in (FSharp_Format.combine FSharp_Format.hardline _179_321))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(
# 647 "codegen.fs"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 648 "codegen.fs"
let args = (let _179_322 = (FSharp_Format.combine (FSharp_Format.text " * ") args)
in (FSharp_Format.parens _179_322))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_77_594, ty)) -> begin
(
# 652 "codegen.fs"
let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (FSharp_Format.reduce1 (((FSharp_Format.text "val"))::((FSharp_Format.text x))::((FSharp_Format.text ": "))::(ty)::[])))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlsig  ->  FSharp_Format.doc = (fun currentModule s -> (
# 660 "codegen.fs"
let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (
# 661 "codegen.fs"
let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

# 666 "codegen.fs"
let doc_of_mod1 : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule1  ->  FSharp_Format.doc = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::[]))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(
# 672 "codegen.fs"
let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (
# 673 "codegen.fs"
let args = (let _179_330 = (FSharp_Format.combine (FSharp_Format.text " * ") args)
in (FSharp_Format.parens _179_330))
in (FSharp_Format.reduce1 (((FSharp_Format.text "exception"))::((FSharp_Format.text x))::((FSharp_Format.text "of"))::(args)::[]))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _179_335 = (let _179_334 = (let _179_333 = (let _179_332 = (let _179_331 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_179_331)::[])
in ((FSharp_Format.text "="))::_179_332)
in ((FSharp_Format.text "_"))::_179_333)
in ((FSharp_Format.text "let"))::_179_334)
in (FSharp_Format.reduce1 _179_335))
end
| FStar_Extraction_ML_Syntax.MLM_Loc (loc) -> begin
(doc_of_loc loc)
end))

# 692 "codegen.fs"
let doc_of_mod : FStar_Extraction_ML_Syntax.mlsymbol  ->  FStar_Extraction_ML_Syntax.mlmodule  ->  FSharp_Format.doc = (fun currentModule m -> (
# 693 "codegen.fs"
let docs = (FStar_List.map (fun x -> (
# 694 "codegen.fs"
let doc = (doc_of_mod1 currentModule x)
in (doc)::((match (x) with
| FStar_Extraction_ML_Syntax.MLM_Loc (_77_634) -> begin
FSharp_Format.empty
end
| _77_637 -> begin
FSharp_Format.hardline
end))::(FSharp_Format.hardline)::[])) m)
in (FSharp_Format.reduce (FStar_List.flatten docs))))

# 699 "codegen.fs"
let rec doc_of_mllib_r : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun _77_640 -> (match (_77_640) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(
# 700 "codegen.fs"
let rec for1_sig = (fun _77_647 -> (match (_77_647) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 701 "codegen.fs"
let head = (FSharp_Format.reduce1 (((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text ":"))::((FSharp_Format.text "sig"))::[]))
in (
# 702 "codegen.fs"
let tail = (FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
in (
# 703 "codegen.fs"
let doc = (FStar_Option.map (fun _77_653 -> (match (_77_653) with
| (s, _77_652) -> begin
(doc_of_sig x s)
end)) sigmod)
in (
# 704 "codegen.fs"
let sub = (FStar_List.map for1_sig sub)
in (
# 705 "codegen.fs"
let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _179_352 = (let _179_351 = (let _179_350 = (let _179_349 = (FSharp_Format.reduce sub)
in (_179_349)::((FSharp_Format.cat tail FSharp_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::_179_350)
in ((FSharp_Format.cat head FSharp_Format.hardline))::_179_351)
in (FSharp_Format.reduce _179_352)))))))
end))
and for1_mod = (fun istop _77_666 -> (match (_77_666) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(
# 716 "codegen.fs"
let head = (let _179_355 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FSharp_Format.text "module"))::((FSharp_Format.text x))::[]
end else begin
if (not (istop)) then begin
((FSharp_Format.text "module"))::((FSharp_Format.text x))::((FSharp_Format.text "="))::((FSharp_Format.text "struct"))::[]
end else begin
[]
end
end
in (FSharp_Format.reduce1 _179_355))
in (
# 721 "codegen.fs"
let tail = if (not (istop)) then begin
(FSharp_Format.reduce1 (((FSharp_Format.text "end"))::[]))
end else begin
(FSharp_Format.reduce1 [])
end
in (
# 724 "codegen.fs"
let doc = (FStar_Option.map (fun _77_672 -> (match (_77_672) with
| (_77_670, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (
# 725 "codegen.fs"
let sub = (FStar_List.map (for1_mod false) sub)
in (
# 726 "codegen.fs"
let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (
# 727 "codegen.fs"
let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
((FSharp_Format.cat (FSharp_Format.text "#light \"off\"") FSharp_Format.hardline))::[]
end else begin
[]
end
in (let _179_365 = (let _179_364 = (let _179_363 = (let _179_362 = (let _179_361 = (let _179_360 = (let _179_359 = (let _179_358 = (FSharp_Format.reduce sub)
in (_179_358)::((FSharp_Format.cat tail FSharp_Format.hardline))::[])
in ((match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end))::_179_359)
in (FSharp_Format.hardline)::_179_360)
in ((FSharp_Format.text "open Prims"))::_179_361)
in (FSharp_Format.hardline)::_179_362)
in (head)::_179_363)
in (FStar_List.append prefix _179_364))
in (FStar_All.pipe_left FSharp_Format.reduce _179_365))))))))
end))
in (
# 743 "codegen.fs"
let docs = (FStar_List.map (fun _77_684 -> (match (_77_684) with
| (x, s, m) -> begin
(let _179_367 = (for1_mod true (x, s, m))
in (x, _179_367))
end)) mllib)
in docs))
end))

# 747 "codegen.fs"
let doc_of_mllib : FStar_Extraction_ML_Syntax.mllib  ->  (Prims.string * FSharp_Format.doc) Prims.list = (fun mllib -> (doc_of_mllib_r mllib))

# 751 "codegen.fs"
let string_of_mlexpr : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlexpr  ->  Prims.string = (fun env e -> (
# 752 "codegen.fs"
let doc = (let _179_374 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _179_374 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

# 755 "codegen.fs"
let string_of_mlty : FStar_Extraction_ML_Env.env  ->  FStar_Extraction_ML_Syntax.mlty  ->  Prims.string = (fun env e -> (
# 756 "codegen.fs"
let doc = (let _179_379 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _179_379 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





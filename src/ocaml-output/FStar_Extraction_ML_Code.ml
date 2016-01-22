
open Prims
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

let is_ILeft = (fun _discr_ -> (match (_discr_) with
| ILeft -> begin
true
end
| _ -> begin
false
end))

let is_IRight = (fun _discr_ -> (match (_discr_) with
| IRight -> begin
true
end
| _ -> begin
false
end))

let is_Left = (fun _discr_ -> (match (_discr_) with
| Left -> begin
true
end
| _ -> begin
false
end))

let is_Right = (fun _discr_ -> (match (_discr_) with
| Right -> begin
true
end
| _ -> begin
false
end))

let is_NonAssoc = (fun _discr_ -> (match (_discr_) with
| NonAssoc -> begin
true
end
| _ -> begin
false
end))

type fixity =
| Prefix
| Postfix
| Infix of assoc

let is_Prefix = (fun _discr_ -> (match (_discr_) with
| Prefix -> begin
true
end
| _ -> begin
false
end))

let is_Postfix = (fun _discr_ -> (match (_discr_) with
| Postfix -> begin
true
end
| _ -> begin
false
end))

let is_Infix = (fun _discr_ -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

let ___Infix____0 = (fun projectee -> (match (projectee) with
| Infix (_61_3) -> begin
_61_3
end))

type opprec =
(Prims.int * fixity)

type level =
(opprec * assoc)

let t_prio_fun = (10, Infix (Right))

let t_prio_tpl = (20, Infix (NonAssoc))

let t_prio_name = (30, Postfix)

let e_bin_prio_lambda = (5, Prefix)

let e_bin_prio_if = (15, Prefix)

let e_bin_prio_letin = (19, Prefix)

let e_bin_prio_or = (20, Infix (Left))

let e_bin_prio_and = (25, Infix (Left))

let e_bin_prio_eq = (27, Infix (NonAssoc))

let e_bin_prio_order = (29, Infix (NonAssoc))

let e_bin_prio_op1 = (30, Infix (Left))

let e_bin_prio_op2 = (40, Infix (Left))

let e_bin_prio_op3 = (50, Infix (Left))

let e_bin_prio_op4 = (60, Infix (Left))

let e_bin_prio_comb = (70, Infix (Left))

let e_bin_prio_seq = (100, Infix (Left))

let e_app_prio = (10000, Infix (Left))

let min_op_prec = ((- (1)), Infix (NonAssoc))

let max_op_prec = (FStar_Util.max_int, Infix (NonAssoc))

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

let path_of_ns = (fun currentModule ns -> (let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in if (ns' = currentModule) then begin
[]
end else begin
(let cg_libs = (FStar_ST.read FStar_Options.codegen_libs)
in (let ns_len = (FStar_List.length ns)
in (let found = (FStar_Util.find_map cg_libs (fun cg_path -> (let cg_len = (FStar_List.length cg_path)
in if ((FStar_List.length cg_path) < ns_len) then begin
(let _61_31 = (FStar_Util.first_N cg_len ns)
in (match (_61_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _128_31 = (let _128_30 = (let _128_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_128_29)::[])
in (FStar_List.append pfx _128_30))
in Some (_128_31))
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

let mlpath_of_mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _61_41 -> begin
(let _61_44 = x
in (match (_61_44) with
| (ns, x) -> begin
(let _128_36 = (path_of_ns currentModule ns)
in (_128_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> if ((let _128_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _128_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

let ptsym = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(let _61_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_50) with
| (p, s) -> begin
(let _128_46 = (let _128_45 = (let _128_44 = (ptsym_of_symbol s)
in (_128_44)::[])
in (FStar_List.append p _128_45))
in (FStar_String.concat "." _128_46))
end))
end)

let ptctor = (fun currentModule mlp -> (let _61_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_55) with
| (p, s) -> begin
(let s = if ((let _128_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _128_51)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "U__" s)
end else begin
s
end
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op = (fun _61_60 -> (match (_61_60) with
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

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _61_70 -> (match (_61_70) with
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

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

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

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _61_86 -> (match (_61_86) with
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

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _61_94 inner doc -> (match (_61_94) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _61_103 = _inner
in (match (_61_103) with
| (pi, fi) -> begin
(let _61_106 = _outer
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
(FSharp_Format.parens doc)
end)
end))

let ocaml_u8_codepoint = (fun i -> if ((FStar_Util.int_of_byte i) = 0) then begin
"\\x00"
end else begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end)

let encode_char = (fun c -> if ((FStar_Util.int_of_char c) > 127) then begin
(let bytes = (FStar_Util.string_of_char c)
in (let bytes = (FStar_Util.unicode_of_string bytes)
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

let string_of_mlconstant = (fun sctt -> (match (sctt) with
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
(let _128_92 = (let _128_91 = (encode_char c)
in (Prims.strcat "\'" _128_91))
in (Prims.strcat _128_92 "\'"))
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
(let bytes = (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let chars = (FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

let rec doc_of_mltype' = (fun currentModule outer ty -> (match (ty) with
| FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun s -> if (FStar_Util.starts_with s "\'_") then begin
(FStar_Util.replace_char s '_' 'u')
end else begin
s
end)
in (let _128_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _128_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _128_107 = (let _128_106 = (let _128_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _128_105 doc))
in (FSharp_Format.hbox _128_106))
in (FSharp_Format.parens _128_107))
in doc))
end
| FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _61_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _128_110 = (let _128_109 = (let _128_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_108 args))
in (FSharp_Format.hbox _128_109))
in (FSharp_Format.parens _128_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _128_112 = (let _128_111 = (as_standard_type name)
in (FStar_Option.get _128_111))
in (Prims.snd _128_112))
end else begin
(ptsym currentModule name)
end
in (let _128_116 = (let _128_115 = (let _128_114 = (let _128_113 = (FSharp_Format.text name)
in (_128_113)::[])
in (args)::_128_114)
in (FSharp_Format.reduce1 _128_115))
in (FSharp_Format.hbox _128_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _61_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _128_121 = (let _128_120 = (let _128_119 = (let _128_118 = (let _128_117 = (FSharp_Format.text " -> ")
in (_128_117)::(d2)::[])
in (d1)::_128_118)
in (FSharp_Format.reduce1 _128_119))
in (FSharp_Format.hbox _128_120))
in (maybe_paren outer t_prio_fun _128_121))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(FSharp_Format.text "obj")
end else begin
(FSharp_Format.text "Obj.t")
end
end))
and doc_of_mltype = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun currentModule outer e -> (match (e.FStar_Extraction_ML_Syntax.expr) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _128_146 = (let _128_145 = (let _128_144 = (FSharp_Format.text "Prims.checked_cast")
in (_128_144)::(doc)::[])
in (FSharp_Format.reduce _128_145))
in (FSharp_Format.parens _128_146))
end else begin
(let _128_151 = (let _128_150 = (let _128_149 = (FSharp_Format.text "Obj.magic ")
in (let _128_148 = (let _128_147 = (FSharp_Format.parens doc)
in (_128_147)::[])
in (_128_149)::_128_148))
in (FSharp_Format.reduce _128_150))
in (FSharp_Format.parens _128_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _128_155 = (let _128_154 = (let _128_153 = (FSharp_Format.text ";")
in (_128_153)::(FSharp_Format.hardline)::[])
in (d)::_128_154)
in (FSharp_Format.reduce _128_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _128_156 = (string_of_mlconstant c)
in (FSharp_Format.text _128_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _61_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _128_157 = (ptsym currentModule path)
in (FSharp_Format.text _128_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _61_244 -> (match (_61_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _128_164 = (let _128_163 = (let _128_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _128_160))
in (let _128_162 = (let _128_161 = (FSharp_Format.text "=")
in (_128_161)::(doc)::[])
in (_128_163)::_128_162))
in (FSharp_Format.reduce1 _128_164)))
end))
in (let _128_167 = (let _128_166 = (FSharp_Format.text "; ")
in (let _128_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _128_166 _128_165)))
in (FSharp_Format.cbrackets _128_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _128_169 = (let _128_168 = (as_standard_constructor ctor)
in (FStar_Option.get _128_168))
in (Prims.snd _128_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _128_171 = (let _128_170 = (as_standard_constructor ctor)
in (FStar_Option.get _128_170))
in (Prims.snd _128_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _128_175 = (let _128_174 = (FSharp_Format.parens x)
in (let _128_173 = (let _128_172 = (FSharp_Format.text "::")
in (_128_172)::(xs)::[])
in (_128_174)::_128_173))
in (FSharp_Format.reduce _128_175))
end
| (_61_263, _61_265) -> begin
(let _128_181 = (let _128_180 = (FSharp_Format.text name)
in (let _128_179 = (let _128_178 = (let _128_177 = (let _128_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_176 args))
in (FSharp_Format.parens _128_177))
in (_128_178)::[])
in (_128_180)::_128_179))
in (FSharp_Format.reduce1 _128_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _128_183 = (let _128_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_182 docs))
in (FSharp_Format.parens _128_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _128_189 = (let _128_188 = (let _128_187 = (let _128_186 = (let _128_185 = (let _128_184 = (FSharp_Format.text "in")
in (_128_184)::(body)::[])
in (FSharp_Format.reduce1 _128_185))
in (_128_186)::[])
in (doc)::_128_187)
in (FSharp_Format.combine FSharp_Format.hardline _128_188))
in (FSharp_Format.parens _128_189))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _61_291}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _61_309}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _61_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _128_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _128_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _128_195 = (let _128_194 = (let _128_193 = (FSharp_Format.text ".")
in (let _128_192 = (let _128_191 = (FSharp_Format.text (Prims.snd f))
in (_128_191)::[])
in (_128_193)::_128_192))
in (e)::_128_194)
in (FSharp_Format.reduce _128_195))
end else begin
(let _128_201 = (let _128_200 = (let _128_199 = (FSharp_Format.text ".")
in (let _128_198 = (let _128_197 = (let _128_196 = (ptsym currentModule f)
in (FSharp_Format.text _128_196))
in (_128_197)::[])
in (_128_199)::_128_198))
in (e)::_128_200)
in (FSharp_Format.reduce _128_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _128_217 = (let _128_216 = (FSharp_Format.text "(")
in (let _128_215 = (let _128_214 = (FSharp_Format.text x)
in (let _128_213 = (let _128_212 = (match (xt) with
| Some (xxt) -> begin
(let _128_209 = (let _128_208 = (FSharp_Format.text " : ")
in (let _128_207 = (let _128_206 = (doc_of_mltype currentModule outer xxt)
in (_128_206)::[])
in (_128_208)::_128_207))
in (FSharp_Format.reduce1 _128_209))
end
| _61_340 -> begin
(FSharp_Format.text "")
end)
in (let _128_211 = (let _128_210 = (FSharp_Format.text ")")
in (_128_210)::[])
in (_128_212)::_128_211))
in (_128_214)::_128_213))
in (_128_216)::_128_215))
in (FSharp_Format.reduce1 _128_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _61_346 -> (match (_61_346) with
| ((x, _61_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _128_224 = (let _128_223 = (FSharp_Format.text "fun")
in (let _128_222 = (let _128_221 = (FSharp_Format.reduce1 ids)
in (let _128_220 = (let _128_219 = (FSharp_Format.text "->")
in (_128_219)::(body)::[])
in (_128_221)::_128_220))
in (_128_223)::_128_222))
in (FSharp_Format.reduce1 _128_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _128_237 = (let _128_236 = (let _128_231 = (let _128_230 = (FSharp_Format.text "if")
in (let _128_229 = (let _128_228 = (let _128_227 = (FSharp_Format.text "then")
in (let _128_226 = (let _128_225 = (FSharp_Format.text "begin")
in (_128_225)::[])
in (_128_227)::_128_226))
in (cond)::_128_228)
in (_128_230)::_128_229))
in (FSharp_Format.reduce1 _128_231))
in (let _128_235 = (let _128_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _128_233 = (let _128_232 = (FSharp_Format.text "end")
in (_128_232)::[])
in (_128_234)::_128_233))
in (_128_236)::_128_235))
in (FSharp_Format.combine FSharp_Format.hardline _128_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _128_260 = (let _128_259 = (let _128_244 = (let _128_243 = (FSharp_Format.text "if")
in (let _128_242 = (let _128_241 = (let _128_240 = (FSharp_Format.text "then")
in (let _128_239 = (let _128_238 = (FSharp_Format.text "begin")
in (_128_238)::[])
in (_128_240)::_128_239))
in (cond)::_128_241)
in (_128_243)::_128_242))
in (FSharp_Format.reduce1 _128_244))
in (let _128_258 = (let _128_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _128_256 = (let _128_255 = (let _128_250 = (let _128_249 = (FSharp_Format.text "end")
in (let _128_248 = (let _128_247 = (FSharp_Format.text "else")
in (let _128_246 = (let _128_245 = (FSharp_Format.text "begin")
in (_128_245)::[])
in (_128_247)::_128_246))
in (_128_249)::_128_248))
in (FSharp_Format.reduce1 _128_250))
in (let _128_254 = (let _128_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _128_252 = (let _128_251 = (FSharp_Format.text "end")
in (_128_251)::[])
in (_128_253)::_128_252))
in (_128_255)::_128_254))
in (_128_257)::_128_256))
in (_128_259)::_128_258))
in (FSharp_Format.combine FSharp_Format.hardline _128_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _128_267 = (let _128_266 = (let _128_265 = (FSharp_Format.text "match")
in (let _128_264 = (let _128_263 = (FSharp_Format.parens cond)
in (let _128_262 = (let _128_261 = (FSharp_Format.text "with")
in (_128_261)::[])
in (_128_263)::_128_262))
in (_128_265)::_128_264))
in (FSharp_Format.reduce1 _128_266))
in (_128_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _128_272 = (let _128_271 = (FSharp_Format.text "raise")
in (let _128_270 = (let _128_269 = (let _128_268 = (ptctor currentModule exn)
in (FSharp_Format.text _128_268))
in (_128_269)::[])
in (_128_271)::_128_270))
in (FSharp_Format.reduce1 _128_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _128_281 = (let _128_280 = (FSharp_Format.text "raise")
in (let _128_279 = (let _128_278 = (let _128_273 = (ptctor currentModule exn)
in (FSharp_Format.text _128_273))
in (let _128_277 = (let _128_276 = (let _128_275 = (let _128_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_274 args))
in (FSharp_Format.parens _128_275))
in (_128_276)::[])
in (_128_278)::_128_277))
in (_128_280)::_128_279))
in (FSharp_Format.reduce1 _128_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _128_298 = (let _128_297 = (let _128_285 = (let _128_284 = (FSharp_Format.text "try")
in (let _128_283 = (let _128_282 = (FSharp_Format.text "begin")
in (_128_282)::[])
in (_128_284)::_128_283))
in (FSharp_Format.reduce1 _128_285))
in (let _128_296 = (let _128_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _128_294 = (let _128_293 = (let _128_289 = (let _128_288 = (FSharp_Format.text "end")
in (let _128_287 = (let _128_286 = (FSharp_Format.text "with")
in (_128_286)::[])
in (_128_288)::_128_287))
in (FSharp_Format.reduce1 _128_289))
in (let _128_292 = (let _128_291 = (let _128_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _128_290))
in (_128_291)::[])
in (_128_293)::_128_292))
in (_128_295)::_128_294))
in (_128_297)::_128_296))
in (FSharp_Format.combine FSharp_Format.hardline _128_298))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _61_394 = (let _128_303 = (as_bin_op p)
in (FStar_Option.get _128_303))
in (match (_61_394) with
| (_61_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _128_306 = (let _128_305 = (let _128_304 = (FSharp_Format.text txt)
in (_128_304)::(e2)::[])
in (e1)::_128_305)
in (FSharp_Format.reduce1 _128_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _61_404 = (let _128_310 = (as_uni_op p)
in (FStar_Option.get _128_310))
in (match (_61_404) with
| (_61_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _128_314 = (let _128_313 = (FSharp_Format.text txt)
in (let _128_312 = (let _128_311 = (FSharp_Format.parens e1)
in (_128_311)::[])
in (_128_313)::_128_312))
in (FSharp_Format.reduce1 _128_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _128_317 = (string_of_mlconstant c)
in (FSharp_Format.text _128_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _61_421 -> (match (_61_421) with
| (name, p) -> begin
(let _128_326 = (let _128_325 = (let _128_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _128_320))
in (let _128_324 = (let _128_323 = (FSharp_Format.text "=")
in (let _128_322 = (let _128_321 = (doc_of_pattern currentModule p)
in (_128_321)::[])
in (_128_323)::_128_322))
in (_128_325)::_128_324))
in (FSharp_Format.reduce1 _128_326))
end))
in (let _128_329 = (let _128_328 = (FSharp_Format.text "; ")
in (let _128_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _128_328 _128_327)))
in (FSharp_Format.cbrackets _128_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _128_331 = (let _128_330 = (as_standard_constructor ctor)
in (FStar_Option.get _128_330))
in (Prims.snd _128_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _128_333 = (let _128_332 = (as_standard_constructor ctor)
in (FStar_Option.get _128_332))
in (Prims.snd _128_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _128_339 = (let _128_338 = (doc_of_pattern currentModule x)
in (let _128_337 = (let _128_336 = (FSharp_Format.text "::")
in (let _128_335 = (let _128_334 = (doc_of_pattern currentModule xs)
in (_128_334)::[])
in (_128_336)::_128_335))
in (_128_338)::_128_337))
in (FSharp_Format.reduce _128_339))
end
| (_61_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_61_440)::[]) -> begin
(let _128_344 = (let _128_343 = (FSharp_Format.text name)
in (let _128_342 = (let _128_341 = (let _128_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _128_340))
in (_128_341)::[])
in (_128_343)::_128_342))
in (FSharp_Format.reduce1 _128_344))
end
| _61_445 -> begin
(let _128_351 = (let _128_350 = (FSharp_Format.text name)
in (let _128_349 = (let _128_348 = (let _128_347 = (let _128_346 = (FSharp_Format.text ", ")
in (let _128_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _128_346 _128_345)))
in (FSharp_Format.parens _128_347))
in (_128_348)::[])
in (_128_350)::_128_349))
in (FSharp_Format.reduce1 _128_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _128_353 = (let _128_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_352 ps))
in (FSharp_Format.parens _128_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _128_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _128_354 ps))))
end))
and doc_of_branch = (fun currentModule _61_458 -> (match (_61_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _128_360 = (let _128_359 = (FSharp_Format.text "|")
in (let _128_358 = (let _128_357 = (doc_of_pattern currentModule p)
in (_128_357)::[])
in (_128_359)::_128_358))
in (FSharp_Format.reduce1 _128_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _128_366 = (let _128_365 = (FSharp_Format.text "|")
in (let _128_364 = (let _128_363 = (doc_of_pattern currentModule p)
in (let _128_362 = (let _128_361 = (FSharp_Format.text "when")
in (_128_361)::(c)::[])
in (_128_363)::_128_362))
in (_128_365)::_128_364))
in (FSharp_Format.reduce1 _128_366)))
end)
in (let _128_377 = (let _128_376 = (let _128_371 = (let _128_370 = (let _128_369 = (FSharp_Format.text "->")
in (let _128_368 = (let _128_367 = (FSharp_Format.text "begin")
in (_128_367)::[])
in (_128_369)::_128_368))
in (case)::_128_370)
in (FSharp_Format.reduce1 _128_371))
in (let _128_375 = (let _128_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _128_373 = (let _128_372 = (FSharp_Format.text "end")
in (_128_372)::[])
in (_128_374)::_128_373))
in (_128_376)::_128_375))
in (FSharp_Format.combine FSharp_Format.hardline _128_377)))
end))
and doc_of_lets = (fun currentModule _61_468 -> (match (_61_468) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _61_475 -> (match (_61_475) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _61_472; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _61_481 -> (match (_61_481) with
| (x, _61_480) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (_61_486::_61_484, _61_489) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _128_384 = (let _128_383 = (FSharp_Format.text ":")
in (_128_383)::(ty)::[])
in (FSharp_Format.reduce1 _128_384)))
end)
end else begin
(FSharp_Format.text "")
end
in (let _128_391 = (let _128_390 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _128_389 = (let _128_388 = (FSharp_Format.reduce1 ids)
in (let _128_387 = (let _128_386 = (let _128_385 = (FSharp_Format.text "=")
in (_128_385)::(e)::[])
in (ty_annot)::_128_386)
in (_128_388)::_128_387))
in (_128_390)::_128_389))
in (FSharp_Format.reduce1 _128_391))))))
end))
in (let letdoc = if rec_ then begin
(let _128_395 = (let _128_394 = (FSharp_Format.text "let")
in (let _128_393 = (let _128_392 = (FSharp_Format.text "rec")
in (_128_392)::[])
in (_128_394)::_128_393))
in (FSharp_Format.reduce1 _128_395))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _128_399 = (let _128_398 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_128_398)::(doc)::[])
in (FSharp_Format.reduce1 _128_399))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _61_507 -> (match (_61_507) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _61_512 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _128_408 = (let _128_407 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _128_407 doc))
in (FSharp_Format.parens _128_408)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _61_525 -> (match (_61_525) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _128_415 = (let _128_414 = (let _128_413 = (FSharp_Format.text ":")
in (_128_413)::(ty)::[])
in (name)::_128_414)
in (FSharp_Format.reduce1 _128_415))))
end))
in (let _128_418 = (let _128_417 = (FSharp_Format.text "; ")
in (let _128_416 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _128_417 _128_416)))
in (FSharp_Format.cbrackets _128_418)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _61_533 -> (match (_61_533) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _61_536 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _128_421 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _128_421 tys))
in (let _128_425 = (let _128_424 = (FSharp_Format.text name)
in (let _128_423 = (let _128_422 = (FSharp_Format.text "of")
in (_128_422)::(tys)::[])
in (_128_424)::_128_423))
in (FSharp_Format.reduce1 _128_425))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _128_428 = (let _128_427 = (FSharp_Format.text "|")
in (_128_427)::(d)::[])
in (FSharp_Format.reduce1 _128_428))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _128_432 = (let _128_431 = (let _128_430 = (let _128_429 = (ptsym currentModule ([], x))
in (FSharp_Format.text _128_429))
in (_128_430)::[])
in (tparams)::_128_431)
in (FSharp_Format.reduce1 _128_432))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _128_437 = (let _128_436 = (let _128_435 = (let _128_434 = (let _128_433 = (FSharp_Format.text "=")
in (_128_433)::[])
in (doc)::_128_434)
in (FSharp_Format.reduce1 _128_435))
in (_128_436)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _128_437)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _128_442 = (let _128_441 = (FSharp_Format.text "type")
in (let _128_440 = (let _128_439 = (let _128_438 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _128_438 doc))
in (_128_439)::[])
in (_128_441)::_128_440))
in (FSharp_Format.reduce1 _128_442))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _128_462 = (let _128_461 = (let _128_454 = (let _128_453 = (FSharp_Format.text "module")
in (let _128_452 = (let _128_451 = (FSharp_Format.text x)
in (let _128_450 = (let _128_449 = (FSharp_Format.text "=")
in (_128_449)::[])
in (_128_451)::_128_450))
in (_128_453)::_128_452))
in (FSharp_Format.reduce1 _128_454))
in (let _128_460 = (let _128_459 = (doc_of_sig currentModule subsig)
in (let _128_458 = (let _128_457 = (let _128_456 = (let _128_455 = (FSharp_Format.text "end")
in (_128_455)::[])
in (FSharp_Format.reduce1 _128_456))
in (_128_457)::[])
in (_128_459)::_128_458))
in (_128_461)::_128_460))
in (FSharp_Format.combine FSharp_Format.hardline _128_462))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _128_466 = (let _128_465 = (FSharp_Format.text "exception")
in (let _128_464 = (let _128_463 = (FSharp_Format.text x)
in (_128_463)::[])
in (_128_465)::_128_464))
in (FSharp_Format.reduce1 _128_466))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _128_468 = (let _128_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _128_467 args))
in (FSharp_Format.parens _128_468))
in (let _128_474 = (let _128_473 = (FSharp_Format.text "exception")
in (let _128_472 = (let _128_471 = (FSharp_Format.text x)
in (let _128_470 = (let _128_469 = (FSharp_Format.text "of")
in (_128_469)::(args)::[])
in (_128_471)::_128_470))
in (_128_473)::_128_472))
in (FSharp_Format.reduce1 _128_474))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_61_567, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _128_480 = (let _128_479 = (FSharp_Format.text "val")
in (let _128_478 = (let _128_477 = (FSharp_Format.text x)
in (let _128_476 = (let _128_475 = (FSharp_Format.text ": ")
in (_128_475)::(ty)::[])
in (_128_477)::_128_476))
in (_128_479)::_128_478))
in (FSharp_Format.reduce1 _128_480)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _128_491 = (let _128_490 = (FSharp_Format.text "exception")
in (let _128_489 = (let _128_488 = (FSharp_Format.text x)
in (_128_488)::[])
in (_128_490)::_128_489))
in (FSharp_Format.reduce1 _128_491))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _128_493 = (let _128_492 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _128_492 args))
in (FSharp_Format.parens _128_493))
in (let _128_499 = (let _128_498 = (FSharp_Format.text "exception")
in (let _128_497 = (let _128_496 = (FSharp_Format.text x)
in (let _128_495 = (let _128_494 = (FSharp_Format.text "of")
in (_128_494)::(args)::[])
in (_128_496)::_128_495))
in (_128_498)::_128_497))
in (FSharp_Format.reduce1 _128_499))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _128_507 = (let _128_506 = (FSharp_Format.text "let")
in (let _128_505 = (let _128_504 = (FSharp_Format.text "_")
in (let _128_503 = (let _128_502 = (FSharp_Format.text "=")
in (let _128_501 = (let _128_500 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_128_500)::[])
in (_128_502)::_128_501))
in (_128_504)::_128_503))
in (_128_506)::_128_505))
in (FSharp_Format.reduce1 _128_507))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _61_606 -> (match (_61_606) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _61_613 -> (match (_61_613) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _128_526 = (let _128_525 = (FSharp_Format.text "module")
in (let _128_524 = (let _128_523 = (FSharp_Format.text x)
in (let _128_522 = (let _128_521 = (FSharp_Format.text ":")
in (let _128_520 = (let _128_519 = (FSharp_Format.text "sig")
in (_128_519)::[])
in (_128_521)::_128_520))
in (_128_523)::_128_522))
in (_128_525)::_128_524))
in (FSharp_Format.reduce1 _128_526))
in (let tail = (let _128_528 = (let _128_527 = (FSharp_Format.text "end")
in (_128_527)::[])
in (FSharp_Format.reduce1 _128_528))
in (let doc = (FStar_Option.map (fun _61_619 -> (match (_61_619) with
| (s, _61_618) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _128_538 = (let _128_537 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _128_536 = (let _128_535 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _128_534 = (let _128_533 = (FSharp_Format.reduce sub)
in (let _128_532 = (let _128_531 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_128_531)::[])
in (_128_533)::_128_532))
in (_128_535)::_128_534))
in (_128_537)::_128_536))
in (FSharp_Format.reduce _128_538)))))))
end))
and for1_mod = (fun istop _61_632 -> (match (_61_632) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _128_551 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _128_543 = (FSharp_Format.text "module")
in (let _128_542 = (let _128_541 = (FSharp_Format.text x)
in (_128_541)::[])
in (_128_543)::_128_542))
end else begin
if (not (istop)) then begin
(let _128_550 = (FSharp_Format.text "module")
in (let _128_549 = (let _128_548 = (FSharp_Format.text x)
in (let _128_547 = (let _128_546 = (FSharp_Format.text "=")
in (let _128_545 = (let _128_544 = (FSharp_Format.text "struct")
in (_128_544)::[])
in (_128_546)::_128_545))
in (_128_548)::_128_547))
in (_128_550)::_128_549))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _128_551))
in (let tail = if (not (istop)) then begin
(let _128_553 = (let _128_552 = (FSharp_Format.text "end")
in (_128_552)::[])
in (FSharp_Format.reduce1 _128_553))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (FStar_Option.map (fun _61_638 -> (match (_61_638) with
| (_61_636, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _128_557 = (let _128_556 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _128_556 FSharp_Format.hardline))
in (_128_557)::[])
end else begin
[]
end
in (let _128_569 = (let _128_568 = (let _128_567 = (let _128_566 = (let _128_565 = (FSharp_Format.text "open Prims")
in (let _128_564 = (let _128_563 = (let _128_562 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _128_561 = (let _128_560 = (FSharp_Format.reduce sub)
in (let _128_559 = (let _128_558 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_128_558)::[])
in (_128_560)::_128_559))
in (_128_562)::_128_561))
in (FSharp_Format.hardline)::_128_563)
in (_128_565)::_128_564))
in (FSharp_Format.hardline)::_128_566)
in (head)::_128_567)
in (FStar_List.append prefix _128_568))
in (FStar_All.pipe_left FSharp_Format.reduce _128_569))))))))
end))
in (let docs = (FStar_List.map (fun _61_650 -> (match (_61_650) with
| (x, s, m) -> begin
(let _128_571 = (for1_mod true (x, s, m))
in (x, _128_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _128_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _128_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _128_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _128_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





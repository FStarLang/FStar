
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
(let _127_31 = (let _127_30 = (let _127_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_127_29)::[])
in (FStar_List.append pfx _127_30))
in Some (_127_31))
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
(let _127_36 = (path_of_ns currentModule ns)
in (_127_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> if ((let _127_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _127_39)) <> (FStar_String.get s 0)) then begin
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
(let _127_46 = (let _127_45 = (let _127_44 = (ptsym_of_symbol s)
in (_127_44)::[])
in (FStar_List.append p _127_45))
in (FStar_String.concat "." _127_46))
end))
end)

let ptctor = (fun currentModule mlp -> (let _61_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_55) with
| (p, s) -> begin
(let s = if ((let _127_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _127_51)) <> (FStar_String.get s 0)) then begin
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
(let _127_92 = (let _127_91 = (encode_char c)
in (Prims.strcat "\'" _127_91))
in (Prims.strcat _127_92 "\'"))
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
in (let _127_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _127_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _127_107 = (let _127_106 = (let _127_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_105 doc))
in (FSharp_Format.hbox _127_106))
in (FSharp_Format.parens _127_107))
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
in (let _127_110 = (let _127_109 = (let _127_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_108 args))
in (FSharp_Format.hbox _127_109))
in (FSharp_Format.parens _127_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _127_112 = (let _127_111 = (as_standard_type name)
in (FStar_Option.get _127_111))
in (Prims.snd _127_112))
end else begin
(ptsym currentModule name)
end
in (let _127_116 = (let _127_115 = (let _127_114 = (let _127_113 = (FSharp_Format.text name)
in (_127_113)::[])
in (args)::_127_114)
in (FSharp_Format.reduce1 _127_115))
in (FSharp_Format.hbox _127_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _61_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _127_121 = (let _127_120 = (let _127_119 = (let _127_118 = (let _127_117 = (FSharp_Format.text " -> ")
in (_127_117)::(d2)::[])
in (d1)::_127_118)
in (FSharp_Format.reduce1 _127_119))
in (FSharp_Format.hbox _127_120))
in (maybe_paren outer t_prio_fun _127_121))))
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
(let _127_146 = (let _127_145 = (let _127_144 = (FSharp_Format.text "Prims.checked_cast")
in (_127_144)::(doc)::[])
in (FSharp_Format.reduce _127_145))
in (FSharp_Format.parens _127_146))
end else begin
(let _127_151 = (let _127_150 = (let _127_149 = (FSharp_Format.text "Obj.magic ")
in (let _127_148 = (let _127_147 = (FSharp_Format.parens doc)
in (_127_147)::[])
in (_127_149)::_127_148))
in (FSharp_Format.reduce _127_150))
in (FSharp_Format.parens _127_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _127_155 = (let _127_154 = (let _127_153 = (FSharp_Format.text ";")
in (_127_153)::(FSharp_Format.hardline)::[])
in (d)::_127_154)
in (FSharp_Format.reduce _127_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _127_156 = (string_of_mlconstant c)
in (FSharp_Format.text _127_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _61_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _127_157 = (ptsym currentModule path)
in (FSharp_Format.text _127_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _61_244 -> (match (_61_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_164 = (let _127_163 = (let _127_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _127_160))
in (let _127_162 = (let _127_161 = (FSharp_Format.text "=")
in (_127_161)::(doc)::[])
in (_127_163)::_127_162))
in (FSharp_Format.reduce1 _127_164)))
end))
in (let _127_167 = (let _127_166 = (FSharp_Format.text "; ")
in (let _127_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _127_166 _127_165)))
in (FSharp_Format.cbrackets _127_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _127_169 = (let _127_168 = (as_standard_constructor ctor)
in (FStar_Option.get _127_168))
in (Prims.snd _127_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _127_171 = (let _127_170 = (as_standard_constructor ctor)
in (FStar_Option.get _127_170))
in (Prims.snd _127_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _127_175 = (let _127_174 = (FSharp_Format.parens x)
in (let _127_173 = (let _127_172 = (FSharp_Format.text "::")
in (_127_172)::(xs)::[])
in (_127_174)::_127_173))
in (FSharp_Format.reduce _127_175))
end
| (_61_263, _61_265) -> begin
(let _127_181 = (let _127_180 = (FSharp_Format.text name)
in (let _127_179 = (let _127_178 = (let _127_177 = (let _127_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_176 args))
in (FSharp_Format.parens _127_177))
in (_127_178)::[])
in (_127_180)::_127_179))
in (FSharp_Format.reduce1 _127_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _127_183 = (let _127_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_182 docs))
in (FSharp_Format.parens _127_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _127_189 = (let _127_188 = (let _127_187 = (let _127_186 = (let _127_185 = (let _127_184 = (FSharp_Format.text "in")
in (_127_184)::(body)::[])
in (FSharp_Format.reduce1 _127_185))
in (_127_186)::[])
in (doc)::_127_187)
in (FSharp_Format.combine FSharp_Format.hardline _127_188))
in (FSharp_Format.parens _127_189))))
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
in (let _127_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _127_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _127_195 = (let _127_194 = (let _127_193 = (FSharp_Format.text ".")
in (let _127_192 = (let _127_191 = (FSharp_Format.text (Prims.snd f))
in (_127_191)::[])
in (_127_193)::_127_192))
in (e)::_127_194)
in (FSharp_Format.reduce _127_195))
end else begin
(let _127_201 = (let _127_200 = (let _127_199 = (FSharp_Format.text ".")
in (let _127_198 = (let _127_197 = (let _127_196 = (ptsym currentModule f)
in (FSharp_Format.text _127_196))
in (_127_197)::[])
in (_127_199)::_127_198))
in (e)::_127_200)
in (FSharp_Format.reduce _127_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _127_217 = (let _127_216 = (FSharp_Format.text "(")
in (let _127_215 = (let _127_214 = (FSharp_Format.text x)
in (let _127_213 = (let _127_212 = (match (xt) with
| Some (xxt) -> begin
(let _127_209 = (let _127_208 = (FSharp_Format.text " : ")
in (let _127_207 = (let _127_206 = (doc_of_mltype currentModule outer xxt)
in (_127_206)::[])
in (_127_208)::_127_207))
in (FSharp_Format.reduce1 _127_209))
end
| _61_340 -> begin
(FSharp_Format.text "")
end)
in (let _127_211 = (let _127_210 = (FSharp_Format.text ")")
in (_127_210)::[])
in (_127_212)::_127_211))
in (_127_214)::_127_213))
in (_127_216)::_127_215))
in (FSharp_Format.reduce1 _127_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _61_346 -> (match (_61_346) with
| ((x, _61_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _127_224 = (let _127_223 = (FSharp_Format.text "fun")
in (let _127_222 = (let _127_221 = (FSharp_Format.reduce1 ids)
in (let _127_220 = (let _127_219 = (FSharp_Format.text "->")
in (_127_219)::(body)::[])
in (_127_221)::_127_220))
in (_127_223)::_127_222))
in (FSharp_Format.reduce1 _127_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _127_237 = (let _127_236 = (let _127_231 = (let _127_230 = (FSharp_Format.text "if")
in (let _127_229 = (let _127_228 = (let _127_227 = (FSharp_Format.text "then")
in (let _127_226 = (let _127_225 = (FSharp_Format.text "begin")
in (_127_225)::[])
in (_127_227)::_127_226))
in (cond)::_127_228)
in (_127_230)::_127_229))
in (FSharp_Format.reduce1 _127_231))
in (let _127_235 = (let _127_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _127_233 = (let _127_232 = (FSharp_Format.text "end")
in (_127_232)::[])
in (_127_234)::_127_233))
in (_127_236)::_127_235))
in (FSharp_Format.combine FSharp_Format.hardline _127_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _127_260 = (let _127_259 = (let _127_244 = (let _127_243 = (FSharp_Format.text "if")
in (let _127_242 = (let _127_241 = (let _127_240 = (FSharp_Format.text "then")
in (let _127_239 = (let _127_238 = (FSharp_Format.text "begin")
in (_127_238)::[])
in (_127_240)::_127_239))
in (cond)::_127_241)
in (_127_243)::_127_242))
in (FSharp_Format.reduce1 _127_244))
in (let _127_258 = (let _127_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _127_256 = (let _127_255 = (let _127_250 = (let _127_249 = (FSharp_Format.text "end")
in (let _127_248 = (let _127_247 = (FSharp_Format.text "else")
in (let _127_246 = (let _127_245 = (FSharp_Format.text "begin")
in (_127_245)::[])
in (_127_247)::_127_246))
in (_127_249)::_127_248))
in (FSharp_Format.reduce1 _127_250))
in (let _127_254 = (let _127_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _127_252 = (let _127_251 = (FSharp_Format.text "end")
in (_127_251)::[])
in (_127_253)::_127_252))
in (_127_255)::_127_254))
in (_127_257)::_127_256))
in (_127_259)::_127_258))
in (FSharp_Format.combine FSharp_Format.hardline _127_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _127_267 = (let _127_266 = (let _127_265 = (FSharp_Format.text "match")
in (let _127_264 = (let _127_263 = (FSharp_Format.parens cond)
in (let _127_262 = (let _127_261 = (FSharp_Format.text "with")
in (_127_261)::[])
in (_127_263)::_127_262))
in (_127_265)::_127_264))
in (FSharp_Format.reduce1 _127_266))
in (_127_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _127_272 = (let _127_271 = (FSharp_Format.text "raise")
in (let _127_270 = (let _127_269 = (let _127_268 = (ptctor currentModule exn)
in (FSharp_Format.text _127_268))
in (_127_269)::[])
in (_127_271)::_127_270))
in (FSharp_Format.reduce1 _127_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _127_281 = (let _127_280 = (FSharp_Format.text "raise")
in (let _127_279 = (let _127_278 = (let _127_273 = (ptctor currentModule exn)
in (FSharp_Format.text _127_273))
in (let _127_277 = (let _127_276 = (let _127_275 = (let _127_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_274 args))
in (FSharp_Format.parens _127_275))
in (_127_276)::[])
in (_127_278)::_127_277))
in (_127_280)::_127_279))
in (FSharp_Format.reduce1 _127_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _127_298 = (let _127_297 = (let _127_285 = (let _127_284 = (FSharp_Format.text "try")
in (let _127_283 = (let _127_282 = (FSharp_Format.text "begin")
in (_127_282)::[])
in (_127_284)::_127_283))
in (FSharp_Format.reduce1 _127_285))
in (let _127_296 = (let _127_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_294 = (let _127_293 = (let _127_289 = (let _127_288 = (FSharp_Format.text "end")
in (let _127_287 = (let _127_286 = (FSharp_Format.text "with")
in (_127_286)::[])
in (_127_288)::_127_287))
in (FSharp_Format.reduce1 _127_289))
in (let _127_292 = (let _127_291 = (let _127_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _127_290))
in (_127_291)::[])
in (_127_293)::_127_292))
in (_127_295)::_127_294))
in (_127_297)::_127_296))
in (FSharp_Format.combine FSharp_Format.hardline _127_298))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _61_394 = (let _127_303 = (as_bin_op p)
in (FStar_Option.get _127_303))
in (match (_61_394) with
| (_61_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _127_306 = (let _127_305 = (let _127_304 = (FSharp_Format.text txt)
in (_127_304)::(e2)::[])
in (e1)::_127_305)
in (FSharp_Format.reduce1 _127_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _61_404 = (let _127_310 = (as_uni_op p)
in (FStar_Option.get _127_310))
in (match (_61_404) with
| (_61_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _127_314 = (let _127_313 = (FSharp_Format.text txt)
in (let _127_312 = (let _127_311 = (FSharp_Format.parens e1)
in (_127_311)::[])
in (_127_313)::_127_312))
in (FSharp_Format.reduce1 _127_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _127_317 = (string_of_mlconstant c)
in (FSharp_Format.text _127_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _61_421 -> (match (_61_421) with
| (name, p) -> begin
(let _127_326 = (let _127_325 = (let _127_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _127_320))
in (let _127_324 = (let _127_323 = (FSharp_Format.text "=")
in (let _127_322 = (let _127_321 = (doc_of_pattern currentModule p)
in (_127_321)::[])
in (_127_323)::_127_322))
in (_127_325)::_127_324))
in (FSharp_Format.reduce1 _127_326))
end))
in (let _127_329 = (let _127_328 = (FSharp_Format.text "; ")
in (let _127_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _127_328 _127_327)))
in (FSharp_Format.cbrackets _127_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _127_331 = (let _127_330 = (as_standard_constructor ctor)
in (FStar_Option.get _127_330))
in (Prims.snd _127_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _127_333 = (let _127_332 = (as_standard_constructor ctor)
in (FStar_Option.get _127_332))
in (Prims.snd _127_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _127_339 = (let _127_338 = (doc_of_pattern currentModule x)
in (let _127_337 = (let _127_336 = (FSharp_Format.text "::")
in (let _127_335 = (let _127_334 = (doc_of_pattern currentModule xs)
in (_127_334)::[])
in (_127_336)::_127_335))
in (_127_338)::_127_337))
in (FSharp_Format.reduce _127_339))
end
| (_61_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_61_440)::[]) -> begin
(let _127_344 = (let _127_343 = (FSharp_Format.text name)
in (let _127_342 = (let _127_341 = (let _127_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _127_340))
in (_127_341)::[])
in (_127_343)::_127_342))
in (FSharp_Format.reduce1 _127_344))
end
| _61_445 -> begin
(let _127_351 = (let _127_350 = (FSharp_Format.text name)
in (let _127_349 = (let _127_348 = (let _127_347 = (let _127_346 = (FSharp_Format.text ", ")
in (let _127_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _127_346 _127_345)))
in (FSharp_Format.parens _127_347))
in (_127_348)::[])
in (_127_350)::_127_349))
in (FSharp_Format.reduce1 _127_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _127_353 = (let _127_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_352 ps))
in (FSharp_Format.parens _127_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _127_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _127_354 ps))))
end))
and doc_of_branch = (fun currentModule _61_458 -> (match (_61_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _127_360 = (let _127_359 = (FSharp_Format.text "|")
in (let _127_358 = (let _127_357 = (doc_of_pattern currentModule p)
in (_127_357)::[])
in (_127_359)::_127_358))
in (FSharp_Format.reduce1 _127_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _127_366 = (let _127_365 = (FSharp_Format.text "|")
in (let _127_364 = (let _127_363 = (doc_of_pattern currentModule p)
in (let _127_362 = (let _127_361 = (FSharp_Format.text "when")
in (_127_361)::(c)::[])
in (_127_363)::_127_362))
in (_127_365)::_127_364))
in (FSharp_Format.reduce1 _127_366)))
end)
in (let _127_377 = (let _127_376 = (let _127_371 = (let _127_370 = (let _127_369 = (FSharp_Format.text "->")
in (let _127_368 = (let _127_367 = (FSharp_Format.text "begin")
in (_127_367)::[])
in (_127_369)::_127_368))
in (case)::_127_370)
in (FSharp_Format.reduce1 _127_371))
in (let _127_375 = (let _127_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_373 = (let _127_372 = (FSharp_Format.text "end")
in (_127_372)::[])
in (_127_374)::_127_373))
in (_127_376)::_127_375))
in (FSharp_Format.combine FSharp_Format.hardline _127_377)))
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
in (let _127_384 = (let _127_383 = (FSharp_Format.text ":")
in (_127_383)::(ty)::[])
in (FSharp_Format.reduce1 _127_384)))
end)
end else begin
(FSharp_Format.text "")
end
in (let _127_391 = (let _127_390 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _127_389 = (let _127_388 = (FSharp_Format.reduce1 ids)
in (let _127_387 = (let _127_386 = (let _127_385 = (FSharp_Format.text "=")
in (_127_385)::(e)::[])
in (ty_annot)::_127_386)
in (_127_388)::_127_387))
in (_127_390)::_127_389))
in (FSharp_Format.reduce1 _127_391))))))
end))
in (let letdoc = if rec_ then begin
(let _127_395 = (let _127_394 = (FSharp_Format.text "let")
in (let _127_393 = (let _127_392 = (FSharp_Format.text "rec")
in (_127_392)::[])
in (_127_394)::_127_393))
in (FSharp_Format.reduce1 _127_395))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _127_399 = (let _127_398 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_127_398)::(doc)::[])
in (FSharp_Format.reduce1 _127_399))) lets)
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
in (let _127_408 = (let _127_407 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_407 doc))
in (FSharp_Format.parens _127_408)))
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
in (let _127_415 = (let _127_414 = (let _127_413 = (FSharp_Format.text ":")
in (_127_413)::(ty)::[])
in (name)::_127_414)
in (FSharp_Format.reduce1 _127_415))))
end))
in (let _127_418 = (let _127_417 = (FSharp_Format.text "; ")
in (let _127_416 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _127_417 _127_416)))
in (FSharp_Format.cbrackets _127_418)))
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
in (let tys = (let _127_421 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_421 tys))
in (let _127_425 = (let _127_424 = (FSharp_Format.text name)
in (let _127_423 = (let _127_422 = (FSharp_Format.text "of")
in (_127_422)::(tys)::[])
in (_127_424)::_127_423))
in (FSharp_Format.reduce1 _127_425))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _127_428 = (let _127_427 = (FSharp_Format.text "|")
in (_127_427)::(d)::[])
in (FSharp_Format.reduce1 _127_428))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _127_432 = (let _127_431 = (let _127_430 = (let _127_429 = (ptsym currentModule ([], x))
in (FSharp_Format.text _127_429))
in (_127_430)::[])
in (tparams)::_127_431)
in (FSharp_Format.reduce1 _127_432))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _127_437 = (let _127_436 = (let _127_435 = (let _127_434 = (let _127_433 = (FSharp_Format.text "=")
in (_127_433)::[])
in (doc)::_127_434)
in (FSharp_Format.reduce1 _127_435))
in (_127_436)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _127_437)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _127_442 = (let _127_441 = (FSharp_Format.text "type")
in (let _127_440 = (let _127_439 = (let _127_438 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _127_438 doc))
in (_127_439)::[])
in (_127_441)::_127_440))
in (FSharp_Format.reduce1 _127_442))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _127_462 = (let _127_461 = (let _127_454 = (let _127_453 = (FSharp_Format.text "module")
in (let _127_452 = (let _127_451 = (FSharp_Format.text x)
in (let _127_450 = (let _127_449 = (FSharp_Format.text "=")
in (_127_449)::[])
in (_127_451)::_127_450))
in (_127_453)::_127_452))
in (FSharp_Format.reduce1 _127_454))
in (let _127_460 = (let _127_459 = (doc_of_sig currentModule subsig)
in (let _127_458 = (let _127_457 = (let _127_456 = (let _127_455 = (FSharp_Format.text "end")
in (_127_455)::[])
in (FSharp_Format.reduce1 _127_456))
in (_127_457)::[])
in (_127_459)::_127_458))
in (_127_461)::_127_460))
in (FSharp_Format.combine FSharp_Format.hardline _127_462))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _127_466 = (let _127_465 = (FSharp_Format.text "exception")
in (let _127_464 = (let _127_463 = (FSharp_Format.text x)
in (_127_463)::[])
in (_127_465)::_127_464))
in (FSharp_Format.reduce1 _127_466))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _127_468 = (let _127_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_467 args))
in (FSharp_Format.parens _127_468))
in (let _127_474 = (let _127_473 = (FSharp_Format.text "exception")
in (let _127_472 = (let _127_471 = (FSharp_Format.text x)
in (let _127_470 = (let _127_469 = (FSharp_Format.text "of")
in (_127_469)::(args)::[])
in (_127_471)::_127_470))
in (_127_473)::_127_472))
in (FSharp_Format.reduce1 _127_474))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_61_567, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _127_480 = (let _127_479 = (FSharp_Format.text "val")
in (let _127_478 = (let _127_477 = (FSharp_Format.text x)
in (let _127_476 = (let _127_475 = (FSharp_Format.text ": ")
in (_127_475)::(ty)::[])
in (_127_477)::_127_476))
in (_127_479)::_127_478))
in (FSharp_Format.reduce1 _127_480)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _127_491 = (let _127_490 = (FSharp_Format.text "exception")
in (let _127_489 = (let _127_488 = (FSharp_Format.text x)
in (_127_488)::[])
in (_127_490)::_127_489))
in (FSharp_Format.reduce1 _127_491))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _127_493 = (let _127_492 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_492 args))
in (FSharp_Format.parens _127_493))
in (let _127_499 = (let _127_498 = (FSharp_Format.text "exception")
in (let _127_497 = (let _127_496 = (FSharp_Format.text x)
in (let _127_495 = (let _127_494 = (FSharp_Format.text "of")
in (_127_494)::(args)::[])
in (_127_496)::_127_495))
in (_127_498)::_127_497))
in (FSharp_Format.reduce1 _127_499))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _127_507 = (let _127_506 = (FSharp_Format.text "let")
in (let _127_505 = (let _127_504 = (FSharp_Format.text "_")
in (let _127_503 = (let _127_502 = (FSharp_Format.text "=")
in (let _127_501 = (let _127_500 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_127_500)::[])
in (_127_502)::_127_501))
in (_127_504)::_127_503))
in (_127_506)::_127_505))
in (FSharp_Format.reduce1 _127_507))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _61_606 -> (match (_61_606) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _61_613 -> (match (_61_613) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _127_526 = (let _127_525 = (FSharp_Format.text "module")
in (let _127_524 = (let _127_523 = (FSharp_Format.text x)
in (let _127_522 = (let _127_521 = (FSharp_Format.text ":")
in (let _127_520 = (let _127_519 = (FSharp_Format.text "sig")
in (_127_519)::[])
in (_127_521)::_127_520))
in (_127_523)::_127_522))
in (_127_525)::_127_524))
in (FSharp_Format.reduce1 _127_526))
in (let tail = (let _127_528 = (let _127_527 = (FSharp_Format.text "end")
in (_127_527)::[])
in (FSharp_Format.reduce1 _127_528))
in (let doc = (FStar_Option.map (fun _61_619 -> (match (_61_619) with
| (s, _61_618) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _127_538 = (let _127_537 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _127_536 = (let _127_535 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _127_534 = (let _127_533 = (FSharp_Format.reduce sub)
in (let _127_532 = (let _127_531 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_127_531)::[])
in (_127_533)::_127_532))
in (_127_535)::_127_534))
in (_127_537)::_127_536))
in (FSharp_Format.reduce _127_538)))))))
end))
and for1_mod = (fun istop _61_632 -> (match (_61_632) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _127_551 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _127_543 = (FSharp_Format.text "module")
in (let _127_542 = (let _127_541 = (FSharp_Format.text x)
in (_127_541)::[])
in (_127_543)::_127_542))
end else begin
if (not (istop)) then begin
(let _127_550 = (FSharp_Format.text "module")
in (let _127_549 = (let _127_548 = (FSharp_Format.text x)
in (let _127_547 = (let _127_546 = (FSharp_Format.text "=")
in (let _127_545 = (let _127_544 = (FSharp_Format.text "struct")
in (_127_544)::[])
in (_127_546)::_127_545))
in (_127_548)::_127_547))
in (_127_550)::_127_549))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _127_551))
in (let tail = if (not (istop)) then begin
(let _127_553 = (let _127_552 = (FSharp_Format.text "end")
in (_127_552)::[])
in (FSharp_Format.reduce1 _127_553))
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
(let _127_557 = (let _127_556 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _127_556 FSharp_Format.hardline))
in (_127_557)::[])
end else begin
[]
end
in (let _127_569 = (let _127_568 = (let _127_567 = (let _127_566 = (let _127_565 = (FSharp_Format.text "open Prims")
in (let _127_564 = (let _127_563 = (let _127_562 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _127_561 = (let _127_560 = (FSharp_Format.reduce sub)
in (let _127_559 = (let _127_558 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_127_558)::[])
in (_127_560)::_127_559))
in (_127_562)::_127_561))
in (FSharp_Format.hardline)::_127_563)
in (_127_565)::_127_564))
in (FSharp_Format.hardline)::_127_566)
in (head)::_127_567)
in (FStar_List.append prefix _127_568))
in (FStar_All.pipe_left FSharp_Format.reduce _127_569))))))))
end))
in (let docs = (FStar_List.map (fun _61_650 -> (match (_61_650) with
| (x, s, m) -> begin
(let _127_571 = (for1_mod true (x, s, m))
in (x, _127_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _127_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _127_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _127_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _127_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





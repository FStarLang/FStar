
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
| Infix (_73_3) -> begin
_73_3
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
| ([], _73_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_73_18, _73_20) -> begin
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
(let _73_31 = (FStar_Util.first_N cg_len ns)
in (match (_73_31) with
| (pfx, sfx) -> begin
if (pfx = cg_path) then begin
(let _164_31 = (let _164_30 = (let _164_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_164_29)::[])
in (FStar_List.append pfx _164_30))
in Some (_164_31))
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
| _73_41 -> begin
(let _73_44 = x
in (match (_73_44) with
| (ns, x) -> begin
(let _164_36 = (path_of_ns currentModule ns)
in (_164_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> if ((let _164_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _164_39)) <> (FStar_String.get s 0)) then begin
(Prims.strcat "l__" s)
end else begin
s
end)

let ptsym = (fun currentModule mlp -> if (FStar_List.isEmpty (Prims.fst mlp)) then begin
(ptsym_of_symbol (Prims.snd mlp))
end else begin
(let _73_50 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_50) with
| (p, s) -> begin
(let _164_46 = (let _164_45 = (let _164_44 = (ptsym_of_symbol s)
in (_164_44)::[])
in (FStar_List.append p _164_45))
in (FStar_String.concat "." _164_46))
end))
end)

let ptctor = (fun currentModule mlp -> (let _73_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_55) with
| (p, s) -> begin
(let s = if ((let _164_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _164_51)) <> (FStar_String.get s 0)) then begin
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

let as_bin_op = (fun _73_60 -> (match (_73_60) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_66 -> (match (_73_66) with
| (y, _73_63, _73_65) -> begin
(x = y)
end)) infix_prim_ops)
end else begin
None
end
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _73_70 -> (match (_73_70) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_74 -> (match (_73_74) with
| (y, _73_73) -> begin
(x = y)
end)) prim_uni_ops)
end else begin
None
end
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _73_78 -> (match (_73_78) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_82 -> (match (_73_82) with
| (y, _73_81) -> begin
(x = y)
end)) prim_types)
end else begin
None
end
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _73_86 -> (match (_73_86) with
| (ns, x) -> begin
if (is_prims_ns ns) then begin
(FStar_List.tryFind (fun _73_90 -> (match (_73_90) with
| (y, _73_89) -> begin
(x = y)
end)) prim_constructors)
end else begin
None
end
end))

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _73_94 inner doc -> (match (_73_94) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _73_103 = _inner
in (match (_73_103) with
| (pi, fi) -> begin
(let _73_106 = _outer
in (match (_73_106) with
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
| (_73_130, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_73_134, _73_136) -> begin
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
| _73_154 -> begin
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
(let _164_92 = (let _164_91 = (encode_char c)
in (Prims.strcat "\'" _164_91))
in (Prims.strcat _164_92 "\'"))
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
in (let _164_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _164_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _164_107 = (let _164_106 = (let _164_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _164_105 doc))
in (FSharp_Format.hbox _164_106))
in (FSharp_Format.parens _164_107))
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
| _73_198 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _164_110 = (let _164_109 = (let _164_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_108 args))
in (FSharp_Format.hbox _164_109))
in (FSharp_Format.parens _164_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _164_112 = (let _164_111 = (as_standard_type name)
in (FStar_Option.get _164_111))
in (Prims.snd _164_112))
end else begin
(ptsym currentModule name)
end
in (let _164_116 = (let _164_115 = (let _164_114 = (let _164_113 = (FSharp_Format.text name)
in (_164_113)::[])
in (args)::_164_114)
in (FSharp_Format.reduce1 _164_115))
in (FSharp_Format.hbox _164_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _164_121 = (let _164_120 = (let _164_119 = (let _164_118 = (let _164_117 = (FSharp_Format.text " -> ")
in (_164_117)::(d2)::[])
in (d1)::_164_118)
in (FSharp_Format.reduce1 _164_119))
in (FSharp_Format.hbox _164_120))
in (maybe_paren outer t_prio_fun _164_121))))
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
(let _164_146 = (let _164_145 = (let _164_144 = (FSharp_Format.text "Prims.checked_cast")
in (_164_144)::(doc)::[])
in (FSharp_Format.reduce _164_145))
in (FSharp_Format.parens _164_146))
end else begin
(let _164_151 = (let _164_150 = (let _164_149 = (FSharp_Format.text "Obj.magic ")
in (let _164_148 = (let _164_147 = (FSharp_Format.parens doc)
in (_164_147)::[])
in (_164_149)::_164_148))
in (FSharp_Format.reduce _164_150))
in (FSharp_Format.parens _164_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _164_155 = (let _164_154 = (let _164_153 = (FSharp_Format.text ";")
in (_164_153)::(FSharp_Format.hardline)::[])
in (d)::_164_154)
in (FSharp_Format.reduce _164_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _164_156 = (string_of_mlconstant c)
in (FSharp_Format.text _164_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _164_157 = (ptsym currentModule path)
in (FSharp_Format.text _164_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _73_244 -> (match (_73_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_164 = (let _164_163 = (let _164_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _164_160))
in (let _164_162 = (let _164_161 = (FSharp_Format.text "=")
in (_164_161)::(doc)::[])
in (_164_163)::_164_162))
in (FSharp_Format.reduce1 _164_164)))
end))
in (let _164_167 = (let _164_166 = (FSharp_Format.text "; ")
in (let _164_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _164_166 _164_165)))
in (FSharp_Format.cbrackets _164_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _164_169 = (let _164_168 = (as_standard_constructor ctor)
in (FStar_Option.get _164_168))
in (Prims.snd _164_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _164_171 = (let _164_170 = (as_standard_constructor ctor)
in (FStar_Option.get _164_170))
in (Prims.snd _164_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _164_175 = (let _164_174 = (FSharp_Format.parens x)
in (let _164_173 = (let _164_172 = (FSharp_Format.text "::")
in (_164_172)::(xs)::[])
in (_164_174)::_164_173))
in (FSharp_Format.reduce _164_175))
end
| (_73_263, _73_265) -> begin
(let _164_181 = (let _164_180 = (FSharp_Format.text name)
in (let _164_179 = (let _164_178 = (let _164_177 = (let _164_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_176 args))
in (FSharp_Format.parens _164_177))
in (_164_178)::[])
in (_164_180)::_164_179))
in (FSharp_Format.reduce1 _164_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _164_183 = (let _164_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_182 docs))
in (FSharp_Format.parens _164_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _164_189 = (let _164_188 = (let _164_187 = (let _164_186 = (let _164_185 = (let _164_184 = (FSharp_Format.text "in")
in (_164_184)::(body)::[])
in (FSharp_Format.reduce1 _164_185))
in (_164_186)::[])
in (doc)::_164_187)
in (FSharp_Format.combine FSharp_Format.hardline _164_188))
in (FSharp_Format.parens _164_189))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e.FStar_Extraction_ML_Syntax.expr, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _73_291}, unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App ({FStar_Extraction_ML_Syntax.expr = FStar_Extraction_ML_Syntax.MLE_Name (p); FStar_Extraction_ML_Syntax.ty = _73_309}, unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _73_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _164_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _164_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_195 = (let _164_194 = (let _164_193 = (FSharp_Format.text ".")
in (let _164_192 = (let _164_191 = (FSharp_Format.text (Prims.snd f))
in (_164_191)::[])
in (_164_193)::_164_192))
in (e)::_164_194)
in (FSharp_Format.reduce _164_195))
end else begin
(let _164_201 = (let _164_200 = (let _164_199 = (FSharp_Format.text ".")
in (let _164_198 = (let _164_197 = (let _164_196 = (ptsym currentModule f)
in (FSharp_Format.text _164_196))
in (_164_197)::[])
in (_164_199)::_164_198))
in (e)::_164_200)
in (FSharp_Format.reduce _164_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_217 = (let _164_216 = (FSharp_Format.text "(")
in (let _164_215 = (let _164_214 = (FSharp_Format.text x)
in (let _164_213 = (let _164_212 = (match (xt) with
| Some (xxt) -> begin
(let _164_209 = (let _164_208 = (FSharp_Format.text " : ")
in (let _164_207 = (let _164_206 = (doc_of_mltype currentModule outer xxt)
in (_164_206)::[])
in (_164_208)::_164_207))
in (FSharp_Format.reduce1 _164_209))
end
| _73_340 -> begin
(FSharp_Format.text "")
end)
in (let _164_211 = (let _164_210 = (FSharp_Format.text ")")
in (_164_210)::[])
in (_164_212)::_164_211))
in (_164_214)::_164_213))
in (_164_216)::_164_215))
in (FSharp_Format.reduce1 _164_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _73_346 -> (match (_73_346) with
| ((x, _73_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _164_224 = (let _164_223 = (FSharp_Format.text "fun")
in (let _164_222 = (let _164_221 = (FSharp_Format.reduce1 ids)
in (let _164_220 = (let _164_219 = (FSharp_Format.text "->")
in (_164_219)::(body)::[])
in (_164_221)::_164_220))
in (_164_223)::_164_222))
in (FSharp_Format.reduce1 _164_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _164_237 = (let _164_236 = (let _164_231 = (let _164_230 = (FSharp_Format.text "if")
in (let _164_229 = (let _164_228 = (let _164_227 = (FSharp_Format.text "then")
in (let _164_226 = (let _164_225 = (FSharp_Format.text "begin")
in (_164_225)::[])
in (_164_227)::_164_226))
in (cond)::_164_228)
in (_164_230)::_164_229))
in (FSharp_Format.reduce1 _164_231))
in (let _164_235 = (let _164_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _164_233 = (let _164_232 = (FSharp_Format.text "end")
in (_164_232)::[])
in (_164_234)::_164_233))
in (_164_236)::_164_235))
in (FSharp_Format.combine FSharp_Format.hardline _164_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _164_260 = (let _164_259 = (let _164_244 = (let _164_243 = (FSharp_Format.text "if")
in (let _164_242 = (let _164_241 = (let _164_240 = (FSharp_Format.text "then")
in (let _164_239 = (let _164_238 = (FSharp_Format.text "begin")
in (_164_238)::[])
in (_164_240)::_164_239))
in (cond)::_164_241)
in (_164_243)::_164_242))
in (FSharp_Format.reduce1 _164_244))
in (let _164_258 = (let _164_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _164_256 = (let _164_255 = (let _164_250 = (let _164_249 = (FSharp_Format.text "end")
in (let _164_248 = (let _164_247 = (FSharp_Format.text "else")
in (let _164_246 = (let _164_245 = (FSharp_Format.text "begin")
in (_164_245)::[])
in (_164_247)::_164_246))
in (_164_249)::_164_248))
in (FSharp_Format.reduce1 _164_250))
in (let _164_254 = (let _164_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _164_252 = (let _164_251 = (FSharp_Format.text "end")
in (_164_251)::[])
in (_164_253)::_164_252))
in (_164_255)::_164_254))
in (_164_257)::_164_256))
in (_164_259)::_164_258))
in (FSharp_Format.combine FSharp_Format.hardline _164_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _164_267 = (let _164_266 = (let _164_265 = (FSharp_Format.text "match")
in (let _164_264 = (let _164_263 = (FSharp_Format.parens cond)
in (let _164_262 = (let _164_261 = (FSharp_Format.text "with")
in (_164_261)::[])
in (_164_263)::_164_262))
in (_164_265)::_164_264))
in (FSharp_Format.reduce1 _164_266))
in (_164_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _164_272 = (let _164_271 = (FSharp_Format.text "raise")
in (let _164_270 = (let _164_269 = (let _164_268 = (ptctor currentModule exn)
in (FSharp_Format.text _164_268))
in (_164_269)::[])
in (_164_271)::_164_270))
in (FSharp_Format.reduce1 _164_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _164_281 = (let _164_280 = (FSharp_Format.text "raise")
in (let _164_279 = (let _164_278 = (let _164_273 = (ptctor currentModule exn)
in (FSharp_Format.text _164_273))
in (let _164_277 = (let _164_276 = (let _164_275 = (let _164_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_274 args))
in (FSharp_Format.parens _164_275))
in (_164_276)::[])
in (_164_278)::_164_277))
in (_164_280)::_164_279))
in (FSharp_Format.reduce1 _164_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _164_298 = (let _164_297 = (let _164_285 = (let _164_284 = (FSharp_Format.text "try")
in (let _164_283 = (let _164_282 = (FSharp_Format.text "begin")
in (_164_282)::[])
in (_164_284)::_164_283))
in (FSharp_Format.reduce1 _164_285))
in (let _164_296 = (let _164_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_294 = (let _164_293 = (let _164_289 = (let _164_288 = (FSharp_Format.text "end")
in (let _164_287 = (let _164_286 = (FSharp_Format.text "with")
in (_164_286)::[])
in (_164_288)::_164_287))
in (FSharp_Format.reduce1 _164_289))
in (let _164_292 = (let _164_291 = (let _164_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _164_290))
in (_164_291)::[])
in (_164_293)::_164_292))
in (_164_295)::_164_294))
in (_164_297)::_164_296))
in (FSharp_Format.combine FSharp_Format.hardline _164_298))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _73_394 = (let _164_303 = (as_bin_op p)
in (FStar_Option.get _164_303))
in (match (_73_394) with
| (_73_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _164_306 = (let _164_305 = (let _164_304 = (FSharp_Format.text txt)
in (_164_304)::(e2)::[])
in (e1)::_164_305)
in (FSharp_Format.reduce1 _164_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _73_404 = (let _164_310 = (as_uni_op p)
in (FStar_Option.get _164_310))
in (match (_73_404) with
| (_73_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _164_314 = (let _164_313 = (FSharp_Format.text txt)
in (let _164_312 = (let _164_311 = (FSharp_Format.parens e1)
in (_164_311)::[])
in (_164_313)::_164_312))
in (FSharp_Format.reduce1 _164_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _164_317 = (string_of_mlconstant c)
in (FSharp_Format.text _164_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _73_421 -> (match (_73_421) with
| (name, p) -> begin
(let _164_326 = (let _164_325 = (let _164_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _164_320))
in (let _164_324 = (let _164_323 = (FSharp_Format.text "=")
in (let _164_322 = (let _164_321 = (doc_of_pattern currentModule p)
in (_164_321)::[])
in (_164_323)::_164_322))
in (_164_325)::_164_324))
in (FSharp_Format.reduce1 _164_326))
end))
in (let _164_329 = (let _164_328 = (FSharp_Format.text "; ")
in (let _164_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _164_328 _164_327)))
in (FSharp_Format.cbrackets _164_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _164_331 = (let _164_330 = (as_standard_constructor ctor)
in (FStar_Option.get _164_330))
in (Prims.snd _164_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _164_333 = (let _164_332 = (as_standard_constructor ctor)
in (FStar_Option.get _164_332))
in (Prims.snd _164_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _164_339 = (let _164_338 = (doc_of_pattern currentModule x)
in (let _164_337 = (let _164_336 = (FSharp_Format.text "::")
in (let _164_335 = (let _164_334 = (doc_of_pattern currentModule xs)
in (_164_334)::[])
in (_164_336)::_164_335))
in (_164_338)::_164_337))
in (FSharp_Format.reduce _164_339))
end
| (_73_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_73_440)::[]) -> begin
(let _164_344 = (let _164_343 = (FSharp_Format.text name)
in (let _164_342 = (let _164_341 = (let _164_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _164_340))
in (_164_341)::[])
in (_164_343)::_164_342))
in (FSharp_Format.reduce1 _164_344))
end
| _73_445 -> begin
(let _164_351 = (let _164_350 = (FSharp_Format.text name)
in (let _164_349 = (let _164_348 = (let _164_347 = (let _164_346 = (FSharp_Format.text ", ")
in (let _164_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _164_346 _164_345)))
in (FSharp_Format.parens _164_347))
in (_164_348)::[])
in (_164_350)::_164_349))
in (FSharp_Format.reduce1 _164_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _164_353 = (let _164_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_352 ps))
in (FSharp_Format.parens _164_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _164_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _164_354 ps))))
end))
and doc_of_branch = (fun currentModule _73_458 -> (match (_73_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _164_360 = (let _164_359 = (FSharp_Format.text "|")
in (let _164_358 = (let _164_357 = (doc_of_pattern currentModule p)
in (_164_357)::[])
in (_164_359)::_164_358))
in (FSharp_Format.reduce1 _164_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _164_366 = (let _164_365 = (FSharp_Format.text "|")
in (let _164_364 = (let _164_363 = (doc_of_pattern currentModule p)
in (let _164_362 = (let _164_361 = (FSharp_Format.text "when")
in (_164_361)::(c)::[])
in (_164_363)::_164_362))
in (_164_365)::_164_364))
in (FSharp_Format.reduce1 _164_366)))
end)
in (let _164_377 = (let _164_376 = (let _164_371 = (let _164_370 = (let _164_369 = (FSharp_Format.text "->")
in (let _164_368 = (let _164_367 = (FSharp_Format.text "begin")
in (_164_367)::[])
in (_164_369)::_164_368))
in (case)::_164_370)
in (FSharp_Format.reduce1 _164_371))
in (let _164_375 = (let _164_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _164_373 = (let _164_372 = (FSharp_Format.text "end")
in (_164_372)::[])
in (_164_374)::_164_373))
in (_164_376)::_164_375))
in (FSharp_Format.combine FSharp_Format.hardline _164_377)))
end))
and doc_of_lets = (fun currentModule _73_468 -> (match (_73_468) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _73_475 -> (match (_73_475) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _73_472; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _73_481 -> (match (_73_481) with
| (x, _73_480) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = if ((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level)) then begin
(match (tys) with
| (_73_486::_73_484, _73_489) -> begin
(FSharp_Format.text "")
end
| ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_384 = (let _164_383 = (FSharp_Format.text ":")
in (_164_383)::(ty)::[])
in (FSharp_Format.reduce1 _164_384)))
end)
end else begin
(FSharp_Format.text "")
end
in (let _164_391 = (let _164_390 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _164_389 = (let _164_388 = (FSharp_Format.reduce1 ids)
in (let _164_387 = (let _164_386 = (let _164_385 = (FSharp_Format.text "=")
in (_164_385)::(e)::[])
in (ty_annot)::_164_386)
in (_164_388)::_164_387))
in (_164_390)::_164_389))
in (FSharp_Format.reduce1 _164_391))))))
end))
in (let letdoc = if rec_ then begin
(let _164_395 = (let _164_394 = (FSharp_Format.text "let")
in (let _164_393 = (let _164_392 = (FSharp_Format.text "rec")
in (_164_392)::[])
in (_164_394)::_164_393))
in (FSharp_Format.reduce1 _164_395))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _164_399 = (let _164_398 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_164_398)::(doc)::[])
in (FSharp_Format.reduce1 _164_399))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _73_507 -> (match (_73_507) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _73_512 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _164_408 = (let _164_407 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _164_407 doc))
in (FSharp_Format.parens _164_408)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _73_525 -> (match (_73_525) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_415 = (let _164_414 = (let _164_413 = (FSharp_Format.text ":")
in (_164_413)::(ty)::[])
in (name)::_164_414)
in (FSharp_Format.reduce1 _164_415))))
end))
in (let _164_418 = (let _164_417 = (FSharp_Format.text "; ")
in (let _164_416 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _164_417 _164_416)))
in (FSharp_Format.cbrackets _164_418)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _73_533 -> (match (_73_533) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _73_536 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _164_421 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _164_421 tys))
in (let _164_425 = (let _164_424 = (FSharp_Format.text name)
in (let _164_423 = (let _164_422 = (FSharp_Format.text "of")
in (_164_422)::(tys)::[])
in (_164_424)::_164_423))
in (FSharp_Format.reduce1 _164_425))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _164_428 = (let _164_427 = (FSharp_Format.text "|")
in (_164_427)::(d)::[])
in (FSharp_Format.reduce1 _164_428))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _164_432 = (let _164_431 = (let _164_430 = (let _164_429 = (ptsym currentModule ([], x))
in (FSharp_Format.text _164_429))
in (_164_430)::[])
in (tparams)::_164_431)
in (FSharp_Format.reduce1 _164_432))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _164_437 = (let _164_436 = (let _164_435 = (let _164_434 = (let _164_433 = (FSharp_Format.text "=")
in (_164_433)::[])
in (doc)::_164_434)
in (FSharp_Format.reduce1 _164_435))
in (_164_436)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _164_437)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _164_442 = (let _164_441 = (FSharp_Format.text "type")
in (let _164_440 = (let _164_439 = (let _164_438 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _164_438 doc))
in (_164_439)::[])
in (_164_441)::_164_440))
in (FSharp_Format.reduce1 _164_442))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _164_462 = (let _164_461 = (let _164_454 = (let _164_453 = (FSharp_Format.text "module")
in (let _164_452 = (let _164_451 = (FSharp_Format.text x)
in (let _164_450 = (let _164_449 = (FSharp_Format.text "=")
in (_164_449)::[])
in (_164_451)::_164_450))
in (_164_453)::_164_452))
in (FSharp_Format.reduce1 _164_454))
in (let _164_460 = (let _164_459 = (doc_of_sig currentModule subsig)
in (let _164_458 = (let _164_457 = (let _164_456 = (let _164_455 = (FSharp_Format.text "end")
in (_164_455)::[])
in (FSharp_Format.reduce1 _164_456))
in (_164_457)::[])
in (_164_459)::_164_458))
in (_164_461)::_164_460))
in (FSharp_Format.combine FSharp_Format.hardline _164_462))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _164_466 = (let _164_465 = (FSharp_Format.text "exception")
in (let _164_464 = (let _164_463 = (FSharp_Format.text x)
in (_164_463)::[])
in (_164_465)::_164_464))
in (FSharp_Format.reduce1 _164_466))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _164_468 = (let _164_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _164_467 args))
in (FSharp_Format.parens _164_468))
in (let _164_474 = (let _164_473 = (FSharp_Format.text "exception")
in (let _164_472 = (let _164_471 = (FSharp_Format.text x)
in (let _164_470 = (let _164_469 = (FSharp_Format.text "of")
in (_164_469)::(args)::[])
in (_164_471)::_164_470))
in (_164_473)::_164_472))
in (FSharp_Format.reduce1 _164_474))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_567, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _164_480 = (let _164_479 = (FSharp_Format.text "val")
in (let _164_478 = (let _164_477 = (FSharp_Format.text x)
in (let _164_476 = (let _164_475 = (FSharp_Format.text ": ")
in (_164_475)::(ty)::[])
in (_164_477)::_164_476))
in (_164_479)::_164_478))
in (FSharp_Format.reduce1 _164_480)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _164_491 = (let _164_490 = (FSharp_Format.text "exception")
in (let _164_489 = (let _164_488 = (FSharp_Format.text x)
in (_164_488)::[])
in (_164_490)::_164_489))
in (FSharp_Format.reduce1 _164_491))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _164_493 = (let _164_492 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _164_492 args))
in (FSharp_Format.parens _164_493))
in (let _164_499 = (let _164_498 = (FSharp_Format.text "exception")
in (let _164_497 = (let _164_496 = (FSharp_Format.text x)
in (let _164_495 = (let _164_494 = (FSharp_Format.text "of")
in (_164_494)::(args)::[])
in (_164_496)::_164_495))
in (_164_498)::_164_497))
in (FSharp_Format.reduce1 _164_499))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _164_507 = (let _164_506 = (FSharp_Format.text "let")
in (let _164_505 = (let _164_504 = (FSharp_Format.text "_")
in (let _164_503 = (let _164_502 = (FSharp_Format.text "=")
in (let _164_501 = (let _164_500 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_164_500)::[])
in (_164_502)::_164_501))
in (_164_504)::_164_503))
in (_164_506)::_164_505))
in (FSharp_Format.reduce1 _164_507))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _73_606 -> (match (_73_606) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _73_613 -> (match (_73_613) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _164_526 = (let _164_525 = (FSharp_Format.text "module")
in (let _164_524 = (let _164_523 = (FSharp_Format.text x)
in (let _164_522 = (let _164_521 = (FSharp_Format.text ":")
in (let _164_520 = (let _164_519 = (FSharp_Format.text "sig")
in (_164_519)::[])
in (_164_521)::_164_520))
in (_164_523)::_164_522))
in (_164_525)::_164_524))
in (FSharp_Format.reduce1 _164_526))
in (let tail = (let _164_528 = (let _164_527 = (FSharp_Format.text "end")
in (_164_527)::[])
in (FSharp_Format.reduce1 _164_528))
in (let doc = (FStar_Option.map (fun _73_619 -> (match (_73_619) with
| (s, _73_618) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _164_538 = (let _164_537 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _164_536 = (let _164_535 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _164_534 = (let _164_533 = (FSharp_Format.reduce sub)
in (let _164_532 = (let _164_531 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_164_531)::[])
in (_164_533)::_164_532))
in (_164_535)::_164_534))
in (_164_537)::_164_536))
in (FSharp_Format.reduce _164_538)))))))
end))
and for1_mod = (fun istop _73_632 -> (match (_73_632) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _164_551 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_543 = (FSharp_Format.text "module")
in (let _164_542 = (let _164_541 = (FSharp_Format.text x)
in (_164_541)::[])
in (_164_543)::_164_542))
end else begin
if (not (istop)) then begin
(let _164_550 = (FSharp_Format.text "module")
in (let _164_549 = (let _164_548 = (FSharp_Format.text x)
in (let _164_547 = (let _164_546 = (FSharp_Format.text "=")
in (let _164_545 = (let _164_544 = (FSharp_Format.text "struct")
in (_164_544)::[])
in (_164_546)::_164_545))
in (_164_548)::_164_547))
in (_164_550)::_164_549))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _164_551))
in (let tail = if (not (istop)) then begin
(let _164_553 = (let _164_552 = (FSharp_Format.text "end")
in (_164_552)::[])
in (FSharp_Format.reduce1 _164_553))
end else begin
(FSharp_Format.reduce1 [])
end
in (let doc = (FStar_Option.map (fun _73_638 -> (match (_73_638) with
| (_73_636, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _164_557 = (let _164_556 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _164_556 FSharp_Format.hardline))
in (_164_557)::[])
end else begin
[]
end
in (let _164_569 = (let _164_568 = (let _164_567 = (let _164_566 = (let _164_565 = (FSharp_Format.text "open Prims")
in (let _164_564 = (let _164_563 = (let _164_562 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _164_561 = (let _164_560 = (FSharp_Format.reduce sub)
in (let _164_559 = (let _164_558 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_164_558)::[])
in (_164_560)::_164_559))
in (_164_562)::_164_561))
in (FSharp_Format.hardline)::_164_563)
in (_164_565)::_164_564))
in (FSharp_Format.hardline)::_164_566)
in (head)::_164_567)
in (FStar_List.append prefix _164_568))
in (FStar_All.pipe_left FSharp_Format.reduce _164_569))))))))
end))
in (let docs = (FStar_List.map (fun _73_650 -> (match (_73_650) with
| (x, s, m) -> begin
(let _164_571 = (for1_mod true (x, s, m))
in (x, _164_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _164_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _164_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _164_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _164_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





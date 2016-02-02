
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
(let _150_31 = (let _150_30 = (let _150_29 = (FStar_Extraction_ML_Util.flatten_ns sfx)
in (_150_29)::[])
in (FStar_List.append pfx _150_30))
in Some (_150_31))
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
(let _150_36 = (path_of_ns currentModule ns)
in (_150_36, x))
end))
end))

let ptsym_of_symbol = (fun s -> if ((let _150_39 = (FStar_String.get s 0)
in (FStar_Char.lowercase _150_39)) <> (FStar_String.get s 0)) then begin
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
(let _150_46 = (let _150_45 = (let _150_44 = (ptsym_of_symbol s)
in (_150_44)::[])
in (FStar_List.append p _150_45))
in (FStar_String.concat "." _150_46))
end))
end)

let ptctor = (fun currentModule mlp -> (let _73_55 = (mlpath_of_mlpath currentModule mlp)
in (match (_73_55) with
| (p, s) -> begin
(let s = if ((let _150_51 = (FStar_String.get s 0)
in (FStar_Char.uppercase _150_51)) <> (FStar_String.get s 0)) then begin
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
(let _150_92 = (let _150_91 = (encode_char c)
in (Prims.strcat "\'" _150_91))
in (Prims.strcat _150_92 "\'"))
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
in (let _150_104 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _150_104)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _150_107 = (let _150_106 = (let _150_105 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _150_105 doc))
in (FSharp_Format.hbox _150_106))
in (FSharp_Format.parens _150_107))
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
in (let _150_110 = (let _150_109 = (let _150_108 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_108 args))
in (FSharp_Format.hbox _150_109))
in (FSharp_Format.parens _150_110)))
end)
in (let name = if (is_standard_type name) then begin
(let _150_112 = (let _150_111 = (as_standard_type name)
in (FStar_Option.get _150_111))
in (Prims.snd _150_112))
end else begin
(ptsym currentModule name)
end
in (let _150_116 = (let _150_115 = (let _150_114 = (let _150_113 = (FSharp_Format.text name)
in (_150_113)::[])
in (args)::_150_114)
in (FSharp_Format.reduce1 _150_115))
in (FSharp_Format.hbox _150_116))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _73_204, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _150_121 = (let _150_120 = (let _150_119 = (let _150_118 = (let _150_117 = (FSharp_Format.text " -> ")
in (_150_117)::(d2)::[])
in (d1)::_150_118)
in (FSharp_Format.reduce1 _150_119))
in (FSharp_Format.hbox _150_120))
in (maybe_paren outer t_prio_fun _150_121))))
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
(let _150_146 = (let _150_145 = (let _150_144 = (FSharp_Format.text "Prims.checked_cast")
in (_150_144)::(doc)::[])
in (FSharp_Format.reduce _150_145))
in (FSharp_Format.parens _150_146))
end else begin
(let _150_151 = (let _150_150 = (let _150_149 = (FSharp_Format.text "Obj.magic ")
in (let _150_148 = (let _150_147 = (FSharp_Format.parens doc)
in (_150_147)::[])
in (_150_149)::_150_148))
in (FSharp_Format.reduce _150_150))
in (FSharp_Format.parens _150_151))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _150_155 = (let _150_154 = (let _150_153 = (FSharp_Format.text ";")
in (_150_153)::(FSharp_Format.hardline)::[])
in (d)::_150_154)
in (FSharp_Format.reduce _150_155))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _150_156 = (string_of_mlconstant c)
in (FSharp_Format.text _150_156))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _73_232) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _150_157 = (ptsym currentModule path)
in (FSharp_Format.text _150_157))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _73_244 -> (match (_73_244) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _150_164 = (let _150_163 = (let _150_160 = (ptsym currentModule (path, name))
in (FSharp_Format.text _150_160))
in (let _150_162 = (let _150_161 = (FSharp_Format.text "=")
in (_150_161)::(doc)::[])
in (_150_163)::_150_162))
in (FSharp_Format.reduce1 _150_164)))
end))
in (let _150_167 = (let _150_166 = (FSharp_Format.text "; ")
in (let _150_165 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _150_166 _150_165)))
in (FSharp_Format.cbrackets _150_167)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _150_169 = (let _150_168 = (as_standard_constructor ctor)
in (FStar_Option.get _150_168))
in (Prims.snd _150_169))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _150_171 = (let _150_170 = (as_standard_constructor ctor)
in (FStar_Option.get _150_170))
in (Prims.snd _150_171))
end else begin
(ptctor currentModule ctor)
end
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _150_175 = (let _150_174 = (FSharp_Format.parens x)
in (let _150_173 = (let _150_172 = (FSharp_Format.text "::")
in (_150_172)::(xs)::[])
in (_150_174)::_150_173))
in (FSharp_Format.reduce _150_175))
end
| (_73_263, _73_265) -> begin
(let _150_181 = (let _150_180 = (FSharp_Format.text name)
in (let _150_179 = (let _150_178 = (let _150_177 = (let _150_176 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_176 args))
in (FSharp_Format.parens _150_177))
in (_150_178)::[])
in (_150_180)::_150_179))
in (FSharp_Format.reduce1 _150_181))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _150_183 = (let _150_182 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_182 docs))
in (FSharp_Format.parens _150_183))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _150_189 = (let _150_188 = (let _150_187 = (let _150_186 = (let _150_185 = (let _150_184 = (FSharp_Format.text "in")
in (_150_184)::(body)::[])
in (FSharp_Format.reduce1 _150_185))
in (_150_186)::[])
in (doc)::_150_187)
in (FSharp_Format.combine FSharp_Format.hardline _150_188))
in (FSharp_Format.parens _150_189))))
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
in (let _150_190 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _150_190))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _150_195 = (let _150_194 = (let _150_193 = (FSharp_Format.text ".")
in (let _150_192 = (let _150_191 = (FSharp_Format.text (Prims.snd f))
in (_150_191)::[])
in (_150_193)::_150_192))
in (e)::_150_194)
in (FSharp_Format.reduce _150_195))
end else begin
(let _150_201 = (let _150_200 = (let _150_199 = (FSharp_Format.text ".")
in (let _150_198 = (let _150_197 = (let _150_196 = (ptsym currentModule f)
in (FSharp_Format.text _150_196))
in (_150_197)::[])
in (_150_199)::_150_198))
in (e)::_150_200)
in (FSharp_Format.reduce _150_201))
end
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _150_217 = (let _150_216 = (FSharp_Format.text "(")
in (let _150_215 = (let _150_214 = (FSharp_Format.text x)
in (let _150_213 = (let _150_212 = (match (xt) with
| Some (xxt) -> begin
(let _150_209 = (let _150_208 = (FSharp_Format.text " : ")
in (let _150_207 = (let _150_206 = (doc_of_mltype currentModule outer xxt)
in (_150_206)::[])
in (_150_208)::_150_207))
in (FSharp_Format.reduce1 _150_209))
end
| _73_340 -> begin
(FSharp_Format.text "")
end)
in (let _150_211 = (let _150_210 = (FSharp_Format.text ")")
in (_150_210)::[])
in (_150_212)::_150_211))
in (_150_214)::_150_213))
in (_150_216)::_150_215))
in (FSharp_Format.reduce1 _150_217))
end else begin
(FSharp_Format.text x)
end)
in (let ids = (FStar_List.map (fun _73_346 -> (match (_73_346) with
| ((x, _73_343), xt) -> begin
(bvar_annot x (Some (xt)))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _150_224 = (let _150_223 = (FSharp_Format.text "fun")
in (let _150_222 = (let _150_221 = (FSharp_Format.reduce1 ids)
in (let _150_220 = (let _150_219 = (FSharp_Format.text "->")
in (_150_219)::(body)::[])
in (_150_221)::_150_220))
in (_150_223)::_150_222))
in (FSharp_Format.reduce1 _150_224))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _150_237 = (let _150_236 = (let _150_231 = (let _150_230 = (FSharp_Format.text "if")
in (let _150_229 = (let _150_228 = (let _150_227 = (FSharp_Format.text "then")
in (let _150_226 = (let _150_225 = (FSharp_Format.text "begin")
in (_150_225)::[])
in (_150_227)::_150_226))
in (cond)::_150_228)
in (_150_230)::_150_229))
in (FSharp_Format.reduce1 _150_231))
in (let _150_235 = (let _150_234 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _150_233 = (let _150_232 = (FSharp_Format.text "end")
in (_150_232)::[])
in (_150_234)::_150_233))
in (_150_236)::_150_235))
in (FSharp_Format.combine FSharp_Format.hardline _150_237))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _150_260 = (let _150_259 = (let _150_244 = (let _150_243 = (FSharp_Format.text "if")
in (let _150_242 = (let _150_241 = (let _150_240 = (FSharp_Format.text "then")
in (let _150_239 = (let _150_238 = (FSharp_Format.text "begin")
in (_150_238)::[])
in (_150_240)::_150_239))
in (cond)::_150_241)
in (_150_243)::_150_242))
in (FSharp_Format.reduce1 _150_244))
in (let _150_258 = (let _150_257 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _150_256 = (let _150_255 = (let _150_250 = (let _150_249 = (FSharp_Format.text "end")
in (let _150_248 = (let _150_247 = (FSharp_Format.text "else")
in (let _150_246 = (let _150_245 = (FSharp_Format.text "begin")
in (_150_245)::[])
in (_150_247)::_150_246))
in (_150_249)::_150_248))
in (FSharp_Format.reduce1 _150_250))
in (let _150_254 = (let _150_253 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _150_252 = (let _150_251 = (FSharp_Format.text "end")
in (_150_251)::[])
in (_150_253)::_150_252))
in (_150_255)::_150_254))
in (_150_257)::_150_256))
in (_150_259)::_150_258))
in (FSharp_Format.combine FSharp_Format.hardline _150_260))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _150_267 = (let _150_266 = (let _150_265 = (FSharp_Format.text "match")
in (let _150_264 = (let _150_263 = (FSharp_Format.parens cond)
in (let _150_262 = (let _150_261 = (FSharp_Format.text "with")
in (_150_261)::[])
in (_150_263)::_150_262))
in (_150_265)::_150_264))
in (FSharp_Format.reduce1 _150_266))
in (_150_267)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _150_272 = (let _150_271 = (FSharp_Format.text "raise")
in (let _150_270 = (let _150_269 = (let _150_268 = (ptctor currentModule exn)
in (FSharp_Format.text _150_268))
in (_150_269)::[])
in (_150_271)::_150_270))
in (FSharp_Format.reduce1 _150_272))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _150_281 = (let _150_280 = (FSharp_Format.text "raise")
in (let _150_279 = (let _150_278 = (let _150_273 = (ptctor currentModule exn)
in (FSharp_Format.text _150_273))
in (let _150_277 = (let _150_276 = (let _150_275 = (let _150_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_274 args))
in (FSharp_Format.parens _150_275))
in (_150_276)::[])
in (_150_278)::_150_277))
in (_150_280)::_150_279))
in (FSharp_Format.reduce1 _150_281)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _150_298 = (let _150_297 = (let _150_285 = (let _150_284 = (FSharp_Format.text "try")
in (let _150_283 = (let _150_282 = (FSharp_Format.text "begin")
in (_150_282)::[])
in (_150_284)::_150_283))
in (FSharp_Format.reduce1 _150_285))
in (let _150_296 = (let _150_295 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _150_294 = (let _150_293 = (let _150_289 = (let _150_288 = (FSharp_Format.text "end")
in (let _150_287 = (let _150_286 = (FSharp_Format.text "with")
in (_150_286)::[])
in (_150_288)::_150_287))
in (FSharp_Format.reduce1 _150_289))
in (let _150_292 = (let _150_291 = (let _150_290 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _150_290))
in (_150_291)::[])
in (_150_293)::_150_292))
in (_150_295)::_150_294))
in (_150_297)::_150_296))
in (FSharp_Format.combine FSharp_Format.hardline _150_298))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _73_394 = (let _150_303 = (as_bin_op p)
in (FStar_Option.get _150_303))
in (match (_73_394) with
| (_73_391, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _150_306 = (let _150_305 = (let _150_304 = (FSharp_Format.text txt)
in (_150_304)::(e2)::[])
in (e1)::_150_305)
in (FSharp_Format.reduce1 _150_306))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _73_404 = (let _150_310 = (as_uni_op p)
in (FStar_Option.get _150_310))
in (match (_73_404) with
| (_73_402, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _150_314 = (let _150_313 = (FSharp_Format.text txt)
in (let _150_312 = (let _150_311 = (FSharp_Format.parens e1)
in (_150_311)::[])
in (_150_313)::_150_312))
in (FSharp_Format.reduce1 _150_314))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _150_317 = (string_of_mlconstant c)
in (FSharp_Format.text _150_317))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _73_421 -> (match (_73_421) with
| (name, p) -> begin
(let _150_326 = (let _150_325 = (let _150_320 = (ptsym currentModule (path, name))
in (FSharp_Format.text _150_320))
in (let _150_324 = (let _150_323 = (FSharp_Format.text "=")
in (let _150_322 = (let _150_321 = (doc_of_pattern currentModule p)
in (_150_321)::[])
in (_150_323)::_150_322))
in (_150_325)::_150_324))
in (FSharp_Format.reduce1 _150_326))
end))
in (let _150_329 = (let _150_328 = (FSharp_Format.text "; ")
in (let _150_327 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _150_328 _150_327)))
in (FSharp_Format.cbrackets _150_329)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _150_331 = (let _150_330 = (as_standard_constructor ctor)
in (FStar_Option.get _150_330))
in (Prims.snd _150_331))
end else begin
(ptctor currentModule ctor)
end
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = if (is_standard_constructor ctor) then begin
(let _150_333 = (let _150_332 = (as_standard_constructor ctor)
in (FStar_Option.get _150_332))
in (Prims.snd _150_333))
end else begin
(ptctor currentModule ctor)
end
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _150_339 = (let _150_338 = (doc_of_pattern currentModule x)
in (let _150_337 = (let _150_336 = (FSharp_Format.text "::")
in (let _150_335 = (let _150_334 = (doc_of_pattern currentModule xs)
in (_150_334)::[])
in (_150_336)::_150_335))
in (_150_338)::_150_337))
in (FSharp_Format.reduce _150_339))
end
| (_73_438, FStar_Extraction_ML_Syntax.MLP_Tuple (_73_440)::[]) -> begin
(let _150_344 = (let _150_343 = (FSharp_Format.text name)
in (let _150_342 = (let _150_341 = (let _150_340 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _150_340))
in (_150_341)::[])
in (_150_343)::_150_342))
in (FSharp_Format.reduce1 _150_344))
end
| _73_445 -> begin
(let _150_351 = (let _150_350 = (FSharp_Format.text name)
in (let _150_349 = (let _150_348 = (let _150_347 = (let _150_346 = (FSharp_Format.text ", ")
in (let _150_345 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _150_346 _150_345)))
in (FSharp_Format.parens _150_347))
in (_150_348)::[])
in (_150_350)::_150_349))
in (FSharp_Format.reduce1 _150_351))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _150_353 = (let _150_352 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_352 ps))
in (FSharp_Format.parens _150_353)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _150_354 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _150_354 ps))))
end))
and doc_of_branch = (fun currentModule _73_458 -> (match (_73_458) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _150_360 = (let _150_359 = (FSharp_Format.text "|")
in (let _150_358 = (let _150_357 = (doc_of_pattern currentModule p)
in (_150_357)::[])
in (_150_359)::_150_358))
in (FSharp_Format.reduce1 _150_360))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _150_366 = (let _150_365 = (FSharp_Format.text "|")
in (let _150_364 = (let _150_363 = (doc_of_pattern currentModule p)
in (let _150_362 = (let _150_361 = (FSharp_Format.text "when")
in (_150_361)::(c)::[])
in (_150_363)::_150_362))
in (_150_365)::_150_364))
in (FSharp_Format.reduce1 _150_366)))
end)
in (let _150_377 = (let _150_376 = (let _150_371 = (let _150_370 = (let _150_369 = (FSharp_Format.text "->")
in (let _150_368 = (let _150_367 = (FSharp_Format.text "begin")
in (_150_367)::[])
in (_150_369)::_150_368))
in (case)::_150_370)
in (FSharp_Format.reduce1 _150_371))
in (let _150_375 = (let _150_374 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _150_373 = (let _150_372 = (FSharp_Format.text "end")
in (_150_372)::[])
in (_150_374)::_150_373))
in (_150_376)::_150_375))
in (FSharp_Format.combine FSharp_Format.hardline _150_377)))
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
in (let _150_384 = (let _150_383 = (FSharp_Format.text ":")
in (_150_383)::(ty)::[])
in (FSharp_Format.reduce1 _150_384)))
end)
end else begin
(FSharp_Format.text "")
end
in (let _150_391 = (let _150_390 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _150_389 = (let _150_388 = (FSharp_Format.reduce1 ids)
in (let _150_387 = (let _150_386 = (let _150_385 = (FSharp_Format.text "=")
in (_150_385)::(e)::[])
in (ty_annot)::_150_386)
in (_150_388)::_150_387))
in (_150_390)::_150_389))
in (FSharp_Format.reduce1 _150_391))))))
end))
in (let letdoc = if rec_ then begin
(let _150_395 = (let _150_394 = (FSharp_Format.text "let")
in (let _150_393 = (let _150_392 = (FSharp_Format.text "rec")
in (_150_392)::[])
in (_150_394)::_150_393))
in (FSharp_Format.reduce1 _150_395))
end else begin
(FSharp_Format.text "let")
end
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _150_399 = (let _150_398 = if (i = 0) then begin
letdoc
end else begin
(FSharp_Format.text "and")
end
in (_150_398)::(doc)::[])
in (FSharp_Format.reduce1 _150_399))) lets)
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
in (let _150_408 = (let _150_407 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _150_407 doc))
in (FSharp_Format.parens _150_408)))
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
in (let _150_415 = (let _150_414 = (let _150_413 = (FSharp_Format.text ":")
in (_150_413)::(ty)::[])
in (name)::_150_414)
in (FSharp_Format.reduce1 _150_415))))
end))
in (let _150_418 = (let _150_417 = (FSharp_Format.text "; ")
in (let _150_416 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _150_417 _150_416)))
in (FSharp_Format.cbrackets _150_418)))
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
in (let tys = (let _150_421 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _150_421 tys))
in (let _150_425 = (let _150_424 = (FSharp_Format.text name)
in (let _150_423 = (let _150_422 = (FSharp_Format.text "of")
in (_150_422)::(tys)::[])
in (_150_424)::_150_423))
in (FSharp_Format.reduce1 _150_425))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _150_428 = (let _150_427 = (FSharp_Format.text "|")
in (_150_427)::(d)::[])
in (FSharp_Format.reduce1 _150_428))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _150_432 = (let _150_431 = (let _150_430 = (let _150_429 = (ptsym currentModule ([], x))
in (FSharp_Format.text _150_429))
in (_150_430)::[])
in (tparams)::_150_431)
in (FSharp_Format.reduce1 _150_432))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _150_437 = (let _150_436 = (let _150_435 = (let _150_434 = (let _150_433 = (FSharp_Format.text "=")
in (_150_433)::[])
in (doc)::_150_434)
in (FSharp_Format.reduce1 _150_435))
in (_150_436)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _150_437)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = if ((FStar_List.length doc) > 0) then begin
(let _150_442 = (let _150_441 = (FSharp_Format.text "type")
in (let _150_440 = (let _150_439 = (let _150_438 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _150_438 doc))
in (_150_439)::[])
in (_150_441)::_150_440))
in (FSharp_Format.reduce1 _150_442))
end else begin
(FSharp_Format.text "")
end
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _150_462 = (let _150_461 = (let _150_454 = (let _150_453 = (FSharp_Format.text "module")
in (let _150_452 = (let _150_451 = (FSharp_Format.text x)
in (let _150_450 = (let _150_449 = (FSharp_Format.text "=")
in (_150_449)::[])
in (_150_451)::_150_450))
in (_150_453)::_150_452))
in (FSharp_Format.reduce1 _150_454))
in (let _150_460 = (let _150_459 = (doc_of_sig currentModule subsig)
in (let _150_458 = (let _150_457 = (let _150_456 = (let _150_455 = (FSharp_Format.text "end")
in (_150_455)::[])
in (FSharp_Format.reduce1 _150_456))
in (_150_457)::[])
in (_150_459)::_150_458))
in (_150_461)::_150_460))
in (FSharp_Format.combine FSharp_Format.hardline _150_462))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _150_466 = (let _150_465 = (FSharp_Format.text "exception")
in (let _150_464 = (let _150_463 = (FSharp_Format.text x)
in (_150_463)::[])
in (_150_465)::_150_464))
in (FSharp_Format.reduce1 _150_466))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _150_468 = (let _150_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _150_467 args))
in (FSharp_Format.parens _150_468))
in (let _150_474 = (let _150_473 = (FSharp_Format.text "exception")
in (let _150_472 = (let _150_471 = (FSharp_Format.text x)
in (let _150_470 = (let _150_469 = (FSharp_Format.text "of")
in (_150_469)::(args)::[])
in (_150_471)::_150_470))
in (_150_473)::_150_472))
in (FSharp_Format.reduce1 _150_474))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_73_567, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _150_480 = (let _150_479 = (FSharp_Format.text "val")
in (let _150_478 = (let _150_477 = (FSharp_Format.text x)
in (let _150_476 = (let _150_475 = (FSharp_Format.text ": ")
in (_150_475)::(ty)::[])
in (_150_477)::_150_476))
in (_150_479)::_150_478))
in (FSharp_Format.reduce1 _150_480)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _150_491 = (let _150_490 = (FSharp_Format.text "exception")
in (let _150_489 = (let _150_488 = (FSharp_Format.text x)
in (_150_488)::[])
in (_150_490)::_150_489))
in (FSharp_Format.reduce1 _150_491))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _150_493 = (let _150_492 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _150_492 args))
in (FSharp_Format.parens _150_493))
in (let _150_499 = (let _150_498 = (FSharp_Format.text "exception")
in (let _150_497 = (let _150_496 = (FSharp_Format.text x)
in (let _150_495 = (let _150_494 = (FSharp_Format.text "of")
in (_150_494)::(args)::[])
in (_150_496)::_150_495))
in (_150_498)::_150_497))
in (FSharp_Format.reduce1 _150_499))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _150_507 = (let _150_506 = (FSharp_Format.text "let")
in (let _150_505 = (let _150_504 = (FSharp_Format.text "_")
in (let _150_503 = (let _150_502 = (FSharp_Format.text "=")
in (let _150_501 = (let _150_500 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_150_500)::[])
in (_150_502)::_150_501))
in (_150_504)::_150_503))
in (_150_506)::_150_505))
in (FSharp_Format.reduce1 _150_507))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _73_606 -> (match (_73_606) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _73_613 -> (match (_73_613) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _150_526 = (let _150_525 = (FSharp_Format.text "module")
in (let _150_524 = (let _150_523 = (FSharp_Format.text x)
in (let _150_522 = (let _150_521 = (FSharp_Format.text ":")
in (let _150_520 = (let _150_519 = (FSharp_Format.text "sig")
in (_150_519)::[])
in (_150_521)::_150_520))
in (_150_523)::_150_522))
in (_150_525)::_150_524))
in (FSharp_Format.reduce1 _150_526))
in (let tail = (let _150_528 = (let _150_527 = (FSharp_Format.text "end")
in (_150_527)::[])
in (FSharp_Format.reduce1 _150_528))
in (let doc = (FStar_Option.map (fun _73_619 -> (match (_73_619) with
| (s, _73_618) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _150_538 = (let _150_537 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _150_536 = (let _150_535 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _150_534 = (let _150_533 = (FSharp_Format.reduce sub)
in (let _150_532 = (let _150_531 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_150_531)::[])
in (_150_533)::_150_532))
in (_150_535)::_150_534))
in (_150_537)::_150_536))
in (FSharp_Format.reduce _150_538)))))))
end))
and for1_mod = (fun istop _73_632 -> (match (_73_632) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _150_551 = if (FStar_Extraction_ML_Util.codegen_fsharp ()) then begin
(let _150_543 = (FSharp_Format.text "module")
in (let _150_542 = (let _150_541 = (FSharp_Format.text x)
in (_150_541)::[])
in (_150_543)::_150_542))
end else begin
if (not (istop)) then begin
(let _150_550 = (FSharp_Format.text "module")
in (let _150_549 = (let _150_548 = (FSharp_Format.text x)
in (let _150_547 = (let _150_546 = (FSharp_Format.text "=")
in (let _150_545 = (let _150_544 = (FSharp_Format.text "struct")
in (_150_544)::[])
in (_150_546)::_150_545))
in (_150_548)::_150_547))
in (_150_550)::_150_549))
end else begin
[]
end
end
in (FSharp_Format.reduce1 _150_551))
in (let tail = if (not (istop)) then begin
(let _150_553 = (let _150_552 = (FSharp_Format.text "end")
in (_150_552)::[])
in (FSharp_Format.reduce1 _150_553))
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
(let _150_557 = (let _150_556 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _150_556 FSharp_Format.hardline))
in (_150_557)::[])
end else begin
[]
end
in (let _150_569 = (let _150_568 = (let _150_567 = (let _150_566 = (let _150_565 = (FSharp_Format.text "open Prims")
in (let _150_564 = (let _150_563 = (let _150_562 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _150_561 = (let _150_560 = (FSharp_Format.reduce sub)
in (let _150_559 = (let _150_558 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_150_558)::[])
in (_150_560)::_150_559))
in (_150_562)::_150_561))
in (FSharp_Format.hardline)::_150_563)
in (_150_565)::_150_564))
in (FSharp_Format.hardline)::_150_566)
in (head)::_150_567)
in (FStar_List.append prefix _150_568))
in (FStar_All.pipe_left FSharp_Format.reduce _150_569))))))))
end))
in (let docs = (FStar_List.map (fun _73_650 -> (match (_73_650) with
| (x, s, m) -> begin
(let _150_571 = (for1_mod true (x, s, m))
in (x, _150_571))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _150_578 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _150_578 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _150_583 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _150_583 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





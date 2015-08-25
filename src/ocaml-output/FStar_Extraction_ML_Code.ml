
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
| Infix (_60_3) -> begin
_60_3
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
| ([], _60_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_60_18, _60_20) -> begin
false
end))

let path_of_ns = (fun currentModule ns -> (let ns' = (FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| false -> begin
(ns')::[]
end)))

let mlpath_of_mlpath = (fun currentModule x -> (match ((FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _60_30 -> begin
(let _60_33 = x
in (match (_60_33) with
| (ns, x) -> begin
(let _125_32 = (path_of_ns currentModule ns)
in (_125_32, x))
end))
end))

let ptsym_of_symbol = (fun s -> (match (((let _125_35 = (FStar_String.get s 0)
in (FStar_Char.lowercase _125_35)) <> (FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "l__" s)
end
| false -> begin
s
end))

let ptsym = (fun currentModule mlp -> (match ((FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| false -> begin
(let _60_39 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_39) with
| (p, s) -> begin
(let _125_42 = (let _125_41 = (let _125_40 = (ptsym_of_symbol s)
in (_125_40)::[])
in (FStar_List.append p _125_41))
in (FStar_String.concat "." _125_42))
end))
end))

let ptctor = (fun currentModule mlp -> (let _60_44 = (mlpath_of_mlpath currentModule mlp)
in (match (_60_44) with
| (p, s) -> begin
(let s = (match (((let _125_47 = (FStar_String.get s 0)
in (FStar_Char.uppercase _125_47)) <> (FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "U__" s)
end
| false -> begin
s
end)
in (FStar_String.concat "." (FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op = (fun _60_49 -> (match (_60_49) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_55 -> (match (_60_55) with
| (y, _60_52, _60_54) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _60_59 -> (match (_60_59) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_63 -> (match (_60_63) with
| (y, _60_62) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _60_67 -> (match (_60_67) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_71 -> (match (_60_71) with
| (y, _60_70) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _60_75 -> (match (_60_75) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(FStar_List.tryFind (fun _60_79 -> (match (_60_79) with
| (y, _60_78) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _60_83 inner doc -> (match (_60_83) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _60_92 = _inner
in (match (_60_92) with
| (pi, fi) -> begin
(let _60_95 = _outer
in (match (_60_95) with
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
| (_60_119, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_60_123, _60_125) -> begin
false
end))
end))
end)))
in (match ((noparens inner outer side)) with
| true -> begin
doc
end
| false -> begin
(FSharp_Format.parens doc)
end))
end))

let ocaml_u8_codepoint = (fun i -> (match (((FStar_Util.int_of_byte i) = 0)) with
| true -> begin
"\\x00"
end
| false -> begin
(Prims.strcat "\\x" (FStar_Util.hex_string_of_byte i))
end))

let encode_char = (fun c -> (match (((FStar_Util.int_of_char c) > 127)) with
| true -> begin
(let bytes = (FStar_Util.string_of_char c)
in (let bytes = (FStar_Util.unicode_of_string bytes)
in (FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
end
| false -> begin
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
| _60_143 -> begin
(ocaml_u8_codepoint (FStar_Util.byte_of_char c))
end)
end))

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
(let _125_88 = (let _125_87 = (encode_char c)
in (Prims.strcat "\'" _125_87))
in (Prims.strcat _125_88 "\'"))
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
(let escape_tyvar = (fun s -> (match ((FStar_Util.starts_with s "\'_")) with
| true -> begin
(FStar_Util.replace_char s '_' 'u')
end
| false -> begin
s
end))
in (let _125_100 = (FStar_All.pipe_left escape_tyvar (FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _125_100)))
end
| FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _125_103 = (let _125_102 = (let _125_101 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_101 doc))
in (FSharp_Format.hbox _125_102))
in (FSharp_Format.parens _125_103))
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
| _60_185 -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _125_106 = (let _125_105 = (let _125_104 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_104 args))
in (FSharp_Format.hbox _125_105))
in (FSharp_Format.parens _125_106)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _125_108 = (let _125_107 = (as_standard_type name)
in (FStar_Option.get _125_107))
in (Prims.snd _125_108))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _125_112 = (let _125_111 = (let _125_110 = (let _125_109 = (FSharp_Format.text name)
in (_125_109)::[])
in (args)::_125_110)
in (FSharp_Format.reduce1 _125_111))
in (FSharp_Format.hbox _125_112))))
end
| FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _60_191, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_117 = (let _125_116 = (let _125_115 = (let _125_114 = (let _125_113 = (FSharp_Format.text " -> ")
in (_125_113)::(d2)::[])
in (d1)::_125_114)
in (FSharp_Format.reduce1 _125_115))
in (FSharp_Format.hbox _125_116))
in (maybe_paren outer t_prio_fun _125_117))))
end
| FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_122 = (let _125_121 = (let _125_120 = (let _125_119 = (let _125_118 = (FSharp_Format.text " ")
in (_125_118)::(d1)::[])
in (d2)::_125_119)
in (FSharp_Format.reduce1 _125_120))
in (FSharp_Format.hbox _125_121))
in (maybe_paren outer t_prio_fun _125_122))))
end
| FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(FSharp_Format.text "obj")
end
| false -> begin
(FSharp_Format.text "Obj.t")
end)
end))
and doc_of_mltype = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun currentModule outer e -> (match (e) with
| FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_147 = (let _125_146 = (let _125_145 = (FSharp_Format.text "Prims.checked_cast")
in (_125_145)::(doc)::[])
in (FSharp_Format.reduce _125_146))
in (FSharp_Format.parens _125_147))
end
| false -> begin
(let _125_150 = (let _125_149 = (let _125_148 = (FSharp_Format.text "Obj.magic ")
in (_125_148)::(doc)::[])
in (FSharp_Format.reduce _125_149))
in (FSharp_Format.parens _125_150))
end))
end
| FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (FStar_List.map (fun d -> (let _125_154 = (let _125_153 = (let _125_152 = (FSharp_Format.text ";")
in (_125_152)::(FSharp_Format.hardline)::[])
in (d)::_125_153)
in (FSharp_Format.reduce _125_154))) docs)
in (FSharp_Format.reduce docs)))
end
| FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _125_155 = (string_of_mlconstant c)
in (FSharp_Format.text _125_155))
end
| FStar_Extraction_ML_Syntax.MLE_Var (x, _60_225) -> begin
(FSharp_Format.text x)
end
| FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _125_156 = (ptsym currentModule path)
in (FSharp_Format.text _125_156))
end
| FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _60_237 -> (match (_60_237) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_163 = (let _125_162 = (let _125_159 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_159))
in (let _125_161 = (let _125_160 = (FSharp_Format.text "=")
in (_125_160)::(doc)::[])
in (_125_162)::_125_161))
in (FSharp_Format.reduce1 _125_163)))
end))
in (let _125_166 = (let _125_165 = (FSharp_Format.text "; ")
in (let _125_164 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_165 _125_164)))
in (FSharp_Format.cbrackets _125_166)))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_168 = (let _125_167 = (as_standard_constructor ctor)
in (FStar_Option.get _125_167))
in (Prims.snd _125_168))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_170 = (let _125_169 = (as_standard_constructor ctor)
in (FStar_Option.get _125_169))
in (Prims.snd _125_170))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _125_174 = (let _125_173 = (FSharp_Format.parens x)
in (let _125_172 = (let _125_171 = (FSharp_Format.text "::")
in (_125_171)::(xs)::[])
in (_125_173)::_125_172))
in (FSharp_Format.reduce _125_174))
end
| (_60_256, _60_258) -> begin
(let _125_180 = (let _125_179 = (FSharp_Format.text name)
in (let _125_178 = (let _125_177 = (let _125_176 = (let _125_175 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_175 args))
in (FSharp_Format.parens _125_176))
in (_125_177)::[])
in (_125_179)::_125_178))
in (FSharp_Format.reduce1 _125_180))
end)
in (maybe_paren outer e_app_prio doc))))
end
| FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _125_182 = (let _125_181 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_181 docs))
in (FSharp_Format.parens _125_182))
in docs))
end
| FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _125_188 = (let _125_187 = (let _125_186 = (let _125_185 = (let _125_184 = (let _125_183 = (FSharp_Format.text "in")
in (_125_183)::(body)::[])
in (FSharp_Format.reduce1 _125_184))
in (_125_185)::[])
in (doc)::_125_186)
in (FSharp_Format.combine FSharp_Format.hardline _125_187))
in (FSharp_Format.parens _125_188))))
end
| FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e, args)) with
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (FStar_Extraction_ML_Syntax.MLE_App (FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _60_308 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _125_189 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _125_189))))
end)
end
| FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_194 = (let _125_193 = (let _125_192 = (FSharp_Format.text ".")
in (let _125_191 = (let _125_190 = (FSharp_Format.text (Prims.snd f))
in (_125_190)::[])
in (_125_192)::_125_191))
in (e)::_125_193)
in (FSharp_Format.reduce _125_194))
end
| false -> begin
(let _125_200 = (let _125_199 = (let _125_198 = (FSharp_Format.text ".")
in (let _125_197 = (let _125_196 = (let _125_195 = (ptsym currentModule f)
in (FSharp_Format.text _125_195))
in (_125_196)::[])
in (_125_198)::_125_197))
in (e)::_125_199)
in (FSharp_Format.reduce _125_200))
end)
in doc))
end
| FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let bvar_annot = (fun x xt -> (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_216 = (let _125_215 = (FSharp_Format.text "(")
in (let _125_214 = (let _125_213 = (FSharp_Format.text x)
in (let _125_212 = (let _125_211 = (match (xt) with
| Some (xxt) -> begin
(let _125_208 = (let _125_207 = (FSharp_Format.text " : ")
in (let _125_206 = (let _125_205 = (doc_of_mltype currentModule outer xxt)
in (_125_205)::[])
in (_125_207)::_125_206))
in (FSharp_Format.reduce1 _125_208))
end
| _60_327 -> begin
(FSharp_Format.text "")
end)
in (let _125_210 = (let _125_209 = (FSharp_Format.text ")")
in (_125_209)::[])
in (_125_211)::_125_210))
in (_125_213)::_125_212))
in (_125_215)::_125_214))
in (FSharp_Format.reduce1 _125_216))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (FStar_List.map (fun _60_333 -> (match (_60_333) with
| ((x, _60_330), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _125_223 = (let _125_222 = (FSharp_Format.text "fun")
in (let _125_221 = (let _125_220 = (FSharp_Format.reduce1 ids)
in (let _125_219 = (let _125_218 = (FSharp_Format.text "->")
in (_125_218)::(body)::[])
in (_125_220)::_125_219))
in (_125_222)::_125_221))
in (FSharp_Format.reduce1 _125_223))
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_236 = (let _125_235 = (let _125_230 = (let _125_229 = (FSharp_Format.text "if")
in (let _125_228 = (let _125_227 = (let _125_226 = (FSharp_Format.text "then")
in (let _125_225 = (let _125_224 = (FSharp_Format.text "begin")
in (_125_224)::[])
in (_125_226)::_125_225))
in (cond)::_125_227)
in (_125_229)::_125_228))
in (FSharp_Format.reduce1 _125_230))
in (let _125_234 = (let _125_233 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_232 = (let _125_231 = (FSharp_Format.text "end")
in (_125_231)::[])
in (_125_233)::_125_232))
in (_125_235)::_125_234))
in (FSharp_Format.combine FSharp_Format.hardline _125_236))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_259 = (let _125_258 = (let _125_243 = (let _125_242 = (FSharp_Format.text "if")
in (let _125_241 = (let _125_240 = (let _125_239 = (FSharp_Format.text "then")
in (let _125_238 = (let _125_237 = (FSharp_Format.text "begin")
in (_125_237)::[])
in (_125_239)::_125_238))
in (cond)::_125_240)
in (_125_242)::_125_241))
in (FSharp_Format.reduce1 _125_243))
in (let _125_257 = (let _125_256 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_255 = (let _125_254 = (let _125_249 = (let _125_248 = (FSharp_Format.text "end")
in (let _125_247 = (let _125_246 = (FSharp_Format.text "else")
in (let _125_245 = (let _125_244 = (FSharp_Format.text "begin")
in (_125_244)::[])
in (_125_246)::_125_245))
in (_125_248)::_125_247))
in (FSharp_Format.reduce1 _125_249))
in (let _125_253 = (let _125_252 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _125_251 = (let _125_250 = (FSharp_Format.text "end")
in (_125_250)::[])
in (_125_252)::_125_251))
in (_125_254)::_125_253))
in (_125_256)::_125_255))
in (_125_258)::_125_257))
in (FSharp_Format.combine FSharp_Format.hardline _125_259))
in (maybe_paren outer e_bin_prio_if doc)))
end
| FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _125_266 = (let _125_265 = (let _125_264 = (FSharp_Format.text "match")
in (let _125_263 = (let _125_262 = (FSharp_Format.parens cond)
in (let _125_261 = (let _125_260 = (FSharp_Format.text "with")
in (_125_260)::[])
in (_125_262)::_125_261))
in (_125_264)::_125_263))
in (FSharp_Format.reduce1 _125_265))
in (_125_266)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _125_271 = (let _125_270 = (FSharp_Format.text "raise")
in (let _125_269 = (let _125_268 = (let _125_267 = (ptctor currentModule exn)
in (FSharp_Format.text _125_267))
in (_125_268)::[])
in (_125_270)::_125_269))
in (FSharp_Format.reduce1 _125_271))
end
| FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _125_280 = (let _125_279 = (FSharp_Format.text "raise")
in (let _125_278 = (let _125_277 = (let _125_272 = (ptctor currentModule exn)
in (FSharp_Format.text _125_272))
in (let _125_276 = (let _125_275 = (let _125_274 = (let _125_273 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_273 args))
in (FSharp_Format.parens _125_274))
in (_125_275)::[])
in (_125_277)::_125_276))
in (_125_279)::_125_278))
in (FSharp_Format.reduce1 _125_280)))
end
| FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _125_297 = (let _125_296 = (let _125_284 = (let _125_283 = (FSharp_Format.text "try")
in (let _125_282 = (let _125_281 = (FSharp_Format.text "begin")
in (_125_281)::[])
in (_125_283)::_125_282))
in (FSharp_Format.reduce1 _125_284))
in (let _125_295 = (let _125_294 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_293 = (let _125_292 = (let _125_288 = (let _125_287 = (FSharp_Format.text "end")
in (let _125_286 = (let _125_285 = (FSharp_Format.text "with")
in (_125_285)::[])
in (_125_287)::_125_286))
in (FSharp_Format.reduce1 _125_288))
in (let _125_291 = (let _125_290 = (let _125_289 = (FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _125_289))
in (_125_290)::[])
in (_125_292)::_125_291))
in (_125_294)::_125_293))
in (_125_296)::_125_295))
in (FSharp_Format.combine FSharp_Format.hardline _125_297))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _60_381 = (let _125_302 = (as_bin_op p)
in (FStar_Option.get _125_302))
in (match (_60_381) with
| (_60_378, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _125_305 = (let _125_304 = (let _125_303 = (FSharp_Format.text txt)
in (_125_303)::(e2)::[])
in (e1)::_125_304)
in (FSharp_Format.reduce1 _125_305))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _60_391 = (let _125_309 = (as_uni_op p)
in (FStar_Option.get _125_309))
in (match (_60_391) with
| (_60_389, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _125_313 = (let _125_312 = (FSharp_Format.text txt)
in (let _125_311 = (let _125_310 = (FSharp_Format.parens e1)
in (_125_310)::[])
in (_125_312)::_125_311))
in (FSharp_Format.reduce1 _125_313))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _125_316 = (string_of_mlconstant c)
in (FSharp_Format.text _125_316))
end
| FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _60_408 -> (match (_60_408) with
| (name, p) -> begin
(let _125_325 = (let _125_324 = (let _125_319 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_319))
in (let _125_323 = (let _125_322 = (FSharp_Format.text "=")
in (let _125_321 = (let _125_320 = (doc_of_pattern currentModule p)
in (_125_320)::[])
in (_125_322)::_125_321))
in (_125_324)::_125_323))
in (FSharp_Format.reduce1 _125_325))
end))
in (let _125_328 = (let _125_327 = (FSharp_Format.text "; ")
in (let _125_326 = (FStar_List.map for1 fields)
in (FSharp_Format.combine _125_327 _125_326)))
in (FSharp_Format.cbrackets _125_328)))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_330 = (let _125_329 = (as_standard_constructor ctor)
in (FStar_Option.get _125_329))
in (Prims.snd _125_330))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| FStar_Extraction_ML_Syntax.MLP_CTor (ctor, pats) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_332 = (let _125_331 = (as_standard_constructor ctor)
in (FStar_Option.get _125_331))
in (Prims.snd _125_332))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _125_338 = (let _125_337 = (doc_of_pattern currentModule x)
in (let _125_336 = (let _125_335 = (FSharp_Format.text "::")
in (let _125_334 = (let _125_333 = (doc_of_pattern currentModule xs)
in (_125_333)::[])
in (_125_335)::_125_334))
in (_125_337)::_125_336))
in (FSharp_Format.reduce _125_338))
end
| (_60_425, FStar_Extraction_ML_Syntax.MLP_Tuple (_60_427)::[]) -> begin
(let _125_343 = (let _125_342 = (FSharp_Format.text name)
in (let _125_341 = (let _125_340 = (let _125_339 = (FStar_List.hd pats)
in (doc_of_pattern currentModule _125_339))
in (_125_340)::[])
in (_125_342)::_125_341))
in (FSharp_Format.reduce1 _125_343))
end
| _60_432 -> begin
(let _125_350 = (let _125_349 = (FSharp_Format.text name)
in (let _125_348 = (let _125_347 = (let _125_346 = (let _125_345 = (FSharp_Format.text ", ")
in (let _125_344 = (FStar_List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _125_345 _125_344)))
in (FSharp_Format.parens _125_346))
in (_125_347)::[])
in (_125_349)::_125_348))
in (FSharp_Format.reduce1 _125_350))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let _125_352 = (let _125_351 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_351 ps))
in (FSharp_Format.parens _125_352)))
end
| FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (FStar_List.map FSharp_Format.parens ps)
in (let _125_353 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _125_353 ps))))
end))
and doc_of_branch = (fun currentModule _60_445 -> (match (_60_445) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _125_359 = (let _125_358 = (FSharp_Format.text "|")
in (let _125_357 = (let _125_356 = (doc_of_pattern currentModule p)
in (_125_356)::[])
in (_125_358)::_125_357))
in (FSharp_Format.reduce1 _125_359))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _125_365 = (let _125_364 = (FSharp_Format.text "|")
in (let _125_363 = (let _125_362 = (doc_of_pattern currentModule p)
in (let _125_361 = (let _125_360 = (FSharp_Format.text "when")
in (_125_360)::(c)::[])
in (_125_362)::_125_361))
in (_125_364)::_125_363))
in (FSharp_Format.reduce1 _125_365)))
end)
in (let _125_376 = (let _125_375 = (let _125_370 = (let _125_369 = (let _125_368 = (FSharp_Format.text "->")
in (let _125_367 = (let _125_366 = (FSharp_Format.text "begin")
in (_125_366)::[])
in (_125_368)::_125_367))
in (case)::_125_369)
in (FSharp_Format.reduce1 _125_370))
in (let _125_374 = (let _125_373 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_372 = (let _125_371 = (FSharp_Format.text "end")
in (_125_371)::[])
in (_125_373)::_125_372))
in (_125_375)::_125_374))
in (FSharp_Format.combine FSharp_Format.hardline _125_376)))
end))
and doc_of_lets = (fun currentModule _60_455 -> (match (_60_455) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun _60_462 -> (match (_60_462) with
| {FStar_Extraction_ML_Syntax.mllb_name = name; FStar_Extraction_ML_Syntax.mllb_tysc = tys; FStar_Extraction_ML_Syntax.mllb_add_unit = _60_459; FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (FStar_List.map (fun _60_468 -> (match (_60_468) with
| (x, _60_467) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = (match (((FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level))) with
| true -> begin
(match (tys) with
| (None) | (Some (_::_, _)) -> begin
(FSharp_Format.text "")
end
| Some ([], ty) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_383 = (let _125_382 = (FSharp_Format.text ":")
in (_125_382)::(ty)::[])
in (FSharp_Format.reduce1 _125_383)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _125_390 = (let _125_389 = (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym name))
in (let _125_388 = (let _125_387 = (FSharp_Format.reduce1 ids)
in (let _125_386 = (let _125_385 = (let _125_384 = (FSharp_Format.text "=")
in (_125_384)::(e)::[])
in (ty_annot)::_125_385)
in (_125_387)::_125_386))
in (_125_389)::_125_388))
in (FSharp_Format.reduce1 _125_390))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _125_394 = (let _125_393 = (FSharp_Format.text "let")
in (let _125_392 = (let _125_391 = (FSharp_Format.text "rec")
in (_125_391)::[])
in (_125_393)::_125_392))
in (FSharp_Format.reduce1 _125_394))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (FStar_List.map for1 lets)
in (let lets = (FStar_List.mapi (fun i doc -> (let _125_398 = (let _125_397 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_125_397)::(doc)::[])
in (FSharp_Format.reduce1 _125_398))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _60_497 -> (match (_60_497) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))
end
| _60_502 -> begin
(let doc = (FStar_List.map (fun x -> (FSharp_Format.text (FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _125_407 = (let _125_406 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_406 doc))
in (FSharp_Format.parens _125_407)))
end)
in (let forbody = (fun body -> (match (body) with
| FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _60_515 -> (match (_60_515) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_414 = (let _125_413 = (let _125_412 = (FSharp_Format.text ":")
in (_125_412)::(ty)::[])
in (name)::_125_413)
in (FSharp_Format.reduce1 _125_414))))
end))
in (let _125_417 = (let _125_416 = (FSharp_Format.text "; ")
in (let _125_415 = (FStar_List.map forfield fields)
in (FSharp_Format.combine _125_416 _125_415)))
in (FSharp_Format.cbrackets _125_417)))
end
| FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _60_523 -> (match (_60_523) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _60_526 -> begin
(let tys = (FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _125_420 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_420 tys))
in (let _125_424 = (let _125_423 = (FSharp_Format.text name)
in (let _125_422 = (let _125_421 = (FSharp_Format.text "of")
in (_125_421)::(tys)::[])
in (_125_423)::_125_422))
in (FSharp_Format.reduce1 _125_424))))
end)
end))
in (let ctors = (FStar_List.map forctor ctors)
in (let ctors = (FStar_List.map (fun d -> (let _125_427 = (let _125_426 = (FSharp_Format.text "|")
in (_125_426)::(d)::[])
in (FSharp_Format.reduce1 _125_427))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _125_431 = (let _125_430 = (let _125_429 = (let _125_428 = (ptsym currentModule ([], x))
in (FSharp_Format.text _125_428))
in (_125_429)::[])
in (tparams)::_125_430)
in (FSharp_Format.reduce1 _125_431))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _125_436 = (let _125_435 = (let _125_434 = (let _125_433 = (let _125_432 = (FSharp_Format.text "=")
in (_125_432)::[])
in (doc)::_125_433)
in (FSharp_Format.reduce1 _125_434))
in (_125_435)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _125_436)))
end))))
end))
in (let doc = (FStar_List.map for1 decls)
in (let doc = (match (((FStar_List.length doc) > 0)) with
| true -> begin
(let _125_441 = (let _125_440 = (FSharp_Format.text "type")
in (let _125_439 = (let _125_438 = (let _125_437 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _125_437 doc))
in (_125_438)::[])
in (_125_440)::_125_439))
in (FSharp_Format.reduce1 _125_441))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _125_461 = (let _125_460 = (let _125_453 = (let _125_452 = (FSharp_Format.text "module")
in (let _125_451 = (let _125_450 = (FSharp_Format.text x)
in (let _125_449 = (let _125_448 = (FSharp_Format.text "=")
in (_125_448)::[])
in (_125_450)::_125_449))
in (_125_452)::_125_451))
in (FSharp_Format.reduce1 _125_453))
in (let _125_459 = (let _125_458 = (doc_of_sig currentModule subsig)
in (let _125_457 = (let _125_456 = (let _125_455 = (let _125_454 = (FSharp_Format.text "end")
in (_125_454)::[])
in (FSharp_Format.reduce1 _125_455))
in (_125_456)::[])
in (_125_458)::_125_457))
in (_125_460)::_125_459))
in (FSharp_Format.combine FSharp_Format.hardline _125_461))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _125_465 = (let _125_464 = (FSharp_Format.text "exception")
in (let _125_463 = (let _125_462 = (FSharp_Format.text x)
in (_125_462)::[])
in (_125_464)::_125_463))
in (FSharp_Format.reduce1 _125_465))
end
| FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_467 = (let _125_466 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_466 args))
in (FSharp_Format.parens _125_467))
in (let _125_473 = (let _125_472 = (FSharp_Format.text "exception")
in (let _125_471 = (let _125_470 = (FSharp_Format.text x)
in (let _125_469 = (let _125_468 = (FSharp_Format.text "of")
in (_125_468)::(args)::[])
in (_125_470)::_125_469))
in (_125_472)::_125_471))
in (FSharp_Format.reduce1 _125_473))))
end
| FStar_Extraction_ML_Syntax.MLS_Val (x, (_60_557, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_479 = (let _125_478 = (FSharp_Format.text "val")
in (let _125_477 = (let _125_476 = (FSharp_Format.text x)
in (let _125_475 = (let _125_474 = (FSharp_Format.text ": ")
in (_125_474)::(ty)::[])
in (_125_476)::_125_475))
in (_125_478)::_125_477))
in (FSharp_Format.reduce1 _125_479)))
end
| FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _125_490 = (let _125_489 = (FSharp_Format.text "exception")
in (let _125_488 = (let _125_487 = (FSharp_Format.text x)
in (_125_487)::[])
in (_125_489)::_125_488))
in (FSharp_Format.reduce1 _125_490))
end
| FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_492 = (let _125_491 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_491 args))
in (FSharp_Format.parens _125_492))
in (let _125_498 = (let _125_497 = (FSharp_Format.text "exception")
in (let _125_496 = (let _125_495 = (FSharp_Format.text x)
in (let _125_494 = (let _125_493 = (FSharp_Format.text "of")
in (_125_493)::(args)::[])
in (_125_495)::_125_494))
in (_125_497)::_125_496))
in (FSharp_Format.reduce1 _125_498))))
end
| FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _125_506 = (let _125_505 = (FSharp_Format.text "let")
in (let _125_504 = (let _125_503 = (FSharp_Format.text "_")
in (let _125_502 = (let _125_501 = (FSharp_Format.text "=")
in (let _125_500 = (let _125_499 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_125_499)::[])
in (_125_501)::_125_500))
in (_125_503)::_125_502))
in (_125_505)::_125_504))
in (FSharp_Format.reduce1 _125_506))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _60_596 -> (match (_60_596) with
| FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _60_603 -> (match (_60_603) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_525 = (let _125_524 = (FSharp_Format.text "module")
in (let _125_523 = (let _125_522 = (FSharp_Format.text x)
in (let _125_521 = (let _125_520 = (FSharp_Format.text ":")
in (let _125_519 = (let _125_518 = (FSharp_Format.text "sig")
in (_125_518)::[])
in (_125_520)::_125_519))
in (_125_522)::_125_521))
in (_125_524)::_125_523))
in (FSharp_Format.reduce1 _125_525))
in (let tail = (let _125_527 = (let _125_526 = (FSharp_Format.text "end")
in (_125_526)::[])
in (FSharp_Format.reduce1 _125_527))
in (let doc = (FStar_Option.map (fun _60_609 -> (match (_60_609) with
| (s, _60_608) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (FStar_List.map for1_sig sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _125_537 = (let _125_536 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_535 = (let _125_534 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_533 = (let _125_532 = (FSharp_Format.reduce sub)
in (let _125_531 = (let _125_530 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_530)::[])
in (_125_532)::_125_531))
in (_125_534)::_125_533))
in (_125_536)::_125_535))
in (FSharp_Format.reduce _125_537)))))))
end))
and for1_mod = (fun istop _60_622 -> (match (_60_622) with
| (x, sigmod, FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _60_623 = (FStar_Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _125_550 = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_542 = (FSharp_Format.text "module")
in (let _125_541 = (let _125_540 = (FSharp_Format.text x)
in (_125_540)::[])
in (_125_542)::_125_541))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _125_549 = (FSharp_Format.text "module")
in (let _125_548 = (let _125_547 = (FSharp_Format.text x)
in (let _125_546 = (let _125_545 = (FSharp_Format.text "=")
in (let _125_544 = (let _125_543 = (FSharp_Format.text "struct")
in (_125_543)::[])
in (_125_545)::_125_544))
in (_125_547)::_125_546))
in (_125_549)::_125_548))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _125_550))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _125_552 = (let _125_551 = (FSharp_Format.text "end")
in (_125_551)::[])
in (FSharp_Format.reduce1 _125_552))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (FStar_Option.map (fun _60_630 -> (match (_60_630) with
| (_60_628, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (FStar_List.map (for1_mod false) sub)
in (let sub = (FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = (match ((FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _125_556 = (let _125_555 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _125_555 FSharp_Format.hardline))
in (_125_556)::[])
end
| false -> begin
[]
end)
in (let _125_565 = (let _125_564 = (let _125_563 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_562 = (let _125_561 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_560 = (let _125_559 = (FSharp_Format.reduce sub)
in (let _125_558 = (let _125_557 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_557)::[])
in (_125_559)::_125_558))
in (_125_561)::_125_560))
in (_125_563)::_125_562))
in (FStar_List.append prefix _125_564))
in (FStar_All.pipe_left FSharp_Format.reduce _125_565)))))))))
end))
in (let docs = (FStar_List.map (fun _60_642 -> (match (_60_642) with
| (x, s, m) -> begin
(let _125_567 = (for1_mod true (x, s, m))
in (x, _125_567))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _125_574 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _125_574 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _125_579 = (FStar_Extraction_ML_Util.flatten_mlpath env.FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _125_579 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





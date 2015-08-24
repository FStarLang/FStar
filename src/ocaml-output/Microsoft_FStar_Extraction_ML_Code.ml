
type assoc =
| ILeft
| IRight
| Left
| Right
| NonAssoc

let is_ILeft = (fun ( _discr_ ) -> (match (_discr_) with
| ILeft -> begin
true
end
| _ -> begin
false
end))

let is_IRight = (fun ( _discr_ ) -> (match (_discr_) with
| IRight -> begin
true
end
| _ -> begin
false
end))

let is_Left = (fun ( _discr_ ) -> (match (_discr_) with
| Left -> begin
true
end
| _ -> begin
false
end))

let is_Right = (fun ( _discr_ ) -> (match (_discr_) with
| Right -> begin
true
end
| _ -> begin
false
end))

let is_NonAssoc = (fun ( _discr_ ) -> (match (_discr_) with
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

let is_Prefix = (fun ( _discr_ ) -> (match (_discr_) with
| Prefix -> begin
true
end
| _ -> begin
false
end))

let is_Postfix = (fun ( _discr_ ) -> (match (_discr_) with
| Postfix -> begin
true
end
| _ -> begin
false
end))

let is_Infix = (fun ( _discr_ ) -> (match (_discr_) with
| Infix (_) -> begin
true
end
| _ -> begin
false
end))

let ___Infix____0 = (fun ( projectee ) -> (match (projectee) with
| Infix (_61_3) -> begin
_61_3
end))

type opprec =
(int * fixity)

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

let max_op_prec = (Support.Microsoft.FStar.Util.max_int, Infix (NonAssoc))

let rec in_ns = (fun ( x ) -> (match (x) with
| ([], _61_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_61_18, _61_20) -> begin
false
end))

let path_of_ns = (fun ( currentModule ) ( ns ) -> (let ns' = (Microsoft_FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| false -> begin
(ns')::[]
end)))

let mlpath_of_mlpath = (fun ( currentModule ) ( x ) -> (match ((Microsoft_FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| _61_30 -> begin
(let _61_33 = x
in (match (_61_33) with
| (ns, x) -> begin
(let _127_32 = (path_of_ns currentModule ns)
in (_127_32, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _127_35 = (Support.String.get s 0)
in (Support.Char.lowercase _127_35)) <> (Support.String.get s 0))) with
| true -> begin
(Support.Prims.strcat "l__" s)
end
| false -> begin
s
end))

let ptsym = (fun ( currentModule ) ( mlp ) -> (match ((Support.List.isEmpty (Support.Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Support.Prims.snd mlp))
end
| false -> begin
(let _61_39 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_39) with
| (p, s) -> begin
(let _127_42 = (let _127_41 = (let _127_40 = (ptsym_of_symbol s)
in (_127_40)::[])
in (Support.List.append p _127_41))
in (Support.String.concat "." _127_42))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _61_44 = (mlpath_of_mlpath currentModule mlp)
in (match (_61_44) with
| (p, s) -> begin
(let s = (match (((let _127_47 = (Support.String.get s 0)
in (Support.Char.uppercase _127_47)) <> (Support.String.get s 0))) with
| true -> begin
(Support.Prims.strcat "U__" s)
end
| false -> begin
s
end)
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "%"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::[]

let prim_types = []

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ( ns ) -> (ns = ("Prims")::[]))

let as_bin_op = (fun ( _61_49 ) -> (match (_61_49) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _61_55 ) -> (match (_61_55) with
| (y, _61_52, _61_54) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _61_59 ) -> (match (_61_59) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _61_63 ) -> (match (_61_63) with
| (y, _61_62) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _61_67 ) -> (match (_61_67) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _61_71 ) -> (match (_61_71) with
| (y, _61_70) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _61_75 ) -> (match (_61_75) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _61_79 ) -> (match (_61_79) with
| (y, _61_78) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _61_83 ) ( inner ) ( doc ) -> (match (_61_83) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _61_92 = _inner
in (match (_61_92) with
| (pi, fi) -> begin
(let _61_95 = _outer
in (match (_61_95) with
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
| (_61_119, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_61_123, _61_125) -> begin
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

let ocaml_u8_codepoint = (fun ( i ) -> (match (((Support.Microsoft.FStar.Util.int_of_byte i) = 0)) with
| true -> begin
"\\x00"
end
| false -> begin
(Support.Prims.strcat "\\x" (Support.Microsoft.FStar.Util.hex_string_of_byte i))
end))

let encode_char = (fun ( c ) -> (match (((Support.Microsoft.FStar.Util.int_of_char c) > 127)) with
| true -> begin
(let bytes = (Support.Microsoft.FStar.Util.string_of_char c)
in (let bytes = (Support.Microsoft.FStar.Util.unicode_of_string bytes)
in (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)))
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
| c when (Support.Microsoft.FStar.Util.is_letter_or_digit c) -> begin
(Support.Microsoft.FStar.Util.string_of_char c)
end
| c when (Support.Microsoft.FStar.Util.is_punctuation c) -> begin
(Support.Microsoft.FStar.Util.string_of_char c)
end
| c when (Support.Microsoft.FStar.Util.is_symbol c) -> begin
(Support.Microsoft.FStar.Util.string_of_char c)
end
| _61_143 -> begin
(ocaml_u8_codepoint (Support.Microsoft.FStar.Util.byte_of_char c))
end)
end))

let string_of_mlconstant = (fun ( sctt ) -> (match (sctt) with
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Unit -> begin
"()"
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (true) -> begin
"true"
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Bool (false) -> begin
"false"
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Char (c) -> begin
(let _127_88 = (let _127_87 = (encode_char c)
in (Support.Prims.strcat "\'" _127_87))
in (Support.Prims.strcat _127_88 "\'"))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Byte (c) -> begin
(Support.Prims.strcat (Support.Prims.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int32 (i) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 i)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int64 (i) -> begin
(Support.Prims.strcat (Support.Microsoft.FStar.Util.string_of_int64 i) "L")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(Support.Microsoft.FStar.Util.string_of_float d)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)
in (Support.Prims.strcat (Support.Prims.strcat "\"" bytes) "\""))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let chars = (Support.String.collect encode_char chars)
in (Support.Prims.strcat (Support.Prims.strcat "\"" chars) "\""))
end))

let rec doc_of_mltype' = (fun ( currentModule ) ( outer ) ( ty ) -> (match (ty) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun ( s ) -> (match ((Support.Microsoft.FStar.Util.starts_with s "\'_")) with
| true -> begin
(Support.Microsoft.FStar.Util.replace_char s '_' 'u')
end
| false -> begin
s
end))
in (let _127_100 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _127_100)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _127_103 = (let _127_102 = (let _127_101 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_101 doc))
in (FSharp_Format.hbox _127_102))
in (FSharp_Format.parens _127_103))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named ((args, name)) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _61_185 -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _127_106 = (let _127_105 = (let _127_104 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_104 args))
in (FSharp_Format.hbox _127_105))
in (FSharp_Format.parens _127_106)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _127_108 = (let _127_107 = (as_standard_type name)
in (Support.Option.get _127_107))
in (Support.Prims.snd _127_108))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _127_112 = (let _127_111 = (let _127_110 = (let _127_109 = (FSharp_Format.text name)
in (_127_109)::[])
in (args)::_127_110)
in (FSharp_Format.reduce1 _127_111))
in (FSharp_Format.hbox _127_112))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _61_191, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _127_117 = (let _127_116 = (let _127_115 = (let _127_114 = (let _127_113 = (FSharp_Format.text " -> ")
in (_127_113)::(d2)::[])
in (d1)::_127_114)
in (FSharp_Format.reduce1 _127_115))
in (FSharp_Format.hbox _127_116))
in (maybe_paren outer t_prio_fun _127_117))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _127_122 = (let _127_121 = (let _127_120 = (let _127_119 = (let _127_118 = (FSharp_Format.text " ")
in (_127_118)::(d1)::[])
in (d2)::_127_119)
in (FSharp_Format.reduce1 _127_120))
in (FSharp_Format.hbox _127_121))
in (maybe_paren outer t_prio_fun _127_122))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(FSharp_Format.text "obj")
end
| false -> begin
(FSharp_Format.text "Obj.t")
end)
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _127_147 = (let _127_146 = (let _127_145 = (FSharp_Format.text "Prims.checked_cast")
in (_127_145)::(doc)::[])
in (FSharp_Format.reduce _127_146))
in (FSharp_Format.parens _127_147))
end
| false -> begin
(let _127_150 = (let _127_149 = (let _127_148 = (FSharp_Format.text "Obj.magic ")
in (_127_148)::(doc)::[])
in (FSharp_Format.reduce _127_149))
in (FSharp_Format.parens _127_150))
end))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _127_154 = (let _127_153 = (let _127_152 = (FSharp_Format.text ";")
in (_127_152)::(FSharp_Format.hardline)::[])
in (d)::_127_153)
in (FSharp_Format.reduce _127_154))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _127_155 = (string_of_mlconstant c)
in (FSharp_Format.text _127_155))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _61_225)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _127_156 = (ptsym currentModule path)
in (FSharp_Format.text _127_156))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _61_237 ) -> (match (_61_237) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_163 = (let _127_162 = (let _127_159 = (ptsym currentModule (path, name))
in (FSharp_Format.text _127_159))
in (let _127_161 = (let _127_160 = (FSharp_Format.text "=")
in (_127_160)::(doc)::[])
in (_127_162)::_127_161))
in (FSharp_Format.reduce1 _127_163)))
end))
in (let _127_166 = (let _127_165 = (FSharp_Format.text "; ")
in (let _127_164 = (Support.List.map for1 fields)
in (FSharp_Format.combine _127_165 _127_164)))
in (FSharp_Format.cbrackets _127_166)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _127_168 = (let _127_167 = (as_standard_constructor ctor)
in (Support.Option.get _127_167))
in (Support.Prims.snd _127_168))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _127_170 = (let _127_169 = (as_standard_constructor ctor)
in (Support.Option.get _127_169))
in (Support.Prims.snd _127_170))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _127_174 = (let _127_173 = (FSharp_Format.parens x)
in (let _127_172 = (let _127_171 = (FSharp_Format.text "::")
in (_127_171)::(xs)::[])
in (_127_173)::_127_172))
in (FSharp_Format.reduce _127_174))
end
| (_61_256, _61_258) -> begin
(let _127_180 = (let _127_179 = (FSharp_Format.text name)
in (let _127_178 = (let _127_177 = (let _127_176 = (let _127_175 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_175 args))
in (FSharp_Format.parens _127_176))
in (_127_177)::[])
in (_127_179)::_127_178))
in (FSharp_Format.reduce1 _127_180))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _127_182 = (let _127_181 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_181 docs))
in (FSharp_Format.parens _127_182))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, false, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _127_188 = (let _127_187 = (let _127_186 = (let _127_185 = (let _127_184 = (let _127_183 = (FSharp_Format.text "in")
in (_127_183)::(body)::[])
in (FSharp_Format.reduce1 _127_184))
in (_127_185)::[])
in (doc)::_127_186)
in (FSharp_Format.combine FSharp_Format.hardline _127_187))
in (FSharp_Format.parens _127_188))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[])), e1::e2::[]) when ((is_bin_op p) && (unitVal = Microsoft_FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App ((Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[])), e1::[]) when ((is_uni_op p) && (unitVal = Microsoft_FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _61_308 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _127_189 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _127_189))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _127_194 = (let _127_193 = (let _127_192 = (FSharp_Format.text ".")
in (let _127_191 = (let _127_190 = (FSharp_Format.text (Support.Prims.snd f))
in (_127_190)::[])
in (_127_192)::_127_191))
in (e)::_127_193)
in (FSharp_Format.reduce _127_194))
end
| false -> begin
(let _127_200 = (let _127_199 = (let _127_198 = (FSharp_Format.text ".")
in (let _127_197 = (let _127_196 = (let _127_195 = (ptsym currentModule f)
in (FSharp_Format.text _127_195))
in (_127_196)::[])
in (_127_198)::_127_197))
in (e)::_127_199)
in (FSharp_Format.reduce _127_200))
end)
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let bvar_annot = (fun ( x ) ( xt ) -> (match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _127_216 = (let _127_215 = (FSharp_Format.text "(")
in (let _127_214 = (let _127_213 = (FSharp_Format.text x)
in (let _127_212 = (let _127_211 = (match (xt) with
| Some (xxt) -> begin
(let _127_208 = (let _127_207 = (FSharp_Format.text " : ")
in (let _127_206 = (let _127_205 = (doc_of_mltype currentModule outer xxt)
in (_127_205)::[])
in (_127_207)::_127_206))
in (FSharp_Format.reduce1 _127_208))
end
| _61_327 -> begin
(FSharp_Format.text "")
end)
in (let _127_210 = (let _127_209 = (FSharp_Format.text ")")
in (_127_209)::[])
in (_127_211)::_127_210))
in (_127_213)::_127_212))
in (_127_215)::_127_214))
in (FSharp_Format.reduce1 _127_216))
end
| false -> begin
(FSharp_Format.text x)
end))
in (let ids = (Support.List.map (fun ( _61_333 ) -> (match (_61_333) with
| ((x, _61_330), xt) -> begin
(bvar_annot x xt)
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _127_223 = (let _127_222 = (FSharp_Format.text "fun")
in (let _127_221 = (let _127_220 = (FSharp_Format.reduce1 ids)
in (let _127_219 = (let _127_218 = (FSharp_Format.text "->")
in (_127_218)::(body)::[])
in (_127_220)::_127_219))
in (_127_222)::_127_221))
in (FSharp_Format.reduce1 _127_223))
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _127_236 = (let _127_235 = (let _127_230 = (let _127_229 = (FSharp_Format.text "if")
in (let _127_228 = (let _127_227 = (let _127_226 = (FSharp_Format.text "then")
in (let _127_225 = (let _127_224 = (FSharp_Format.text "begin")
in (_127_224)::[])
in (_127_226)::_127_225))
in (cond)::_127_227)
in (_127_229)::_127_228))
in (FSharp_Format.reduce1 _127_230))
in (let _127_234 = (let _127_233 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _127_232 = (let _127_231 = (FSharp_Format.text "end")
in (_127_231)::[])
in (_127_233)::_127_232))
in (_127_235)::_127_234))
in (FSharp_Format.combine FSharp_Format.hardline _127_236))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _127_259 = (let _127_258 = (let _127_243 = (let _127_242 = (FSharp_Format.text "if")
in (let _127_241 = (let _127_240 = (let _127_239 = (FSharp_Format.text "then")
in (let _127_238 = (let _127_237 = (FSharp_Format.text "begin")
in (_127_237)::[])
in (_127_239)::_127_238))
in (cond)::_127_240)
in (_127_242)::_127_241))
in (FSharp_Format.reduce1 _127_243))
in (let _127_257 = (let _127_256 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _127_255 = (let _127_254 = (let _127_249 = (let _127_248 = (FSharp_Format.text "end")
in (let _127_247 = (let _127_246 = (FSharp_Format.text "else")
in (let _127_245 = (let _127_244 = (FSharp_Format.text "begin")
in (_127_244)::[])
in (_127_246)::_127_245))
in (_127_248)::_127_247))
in (FSharp_Format.reduce1 _127_249))
in (let _127_253 = (let _127_252 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _127_251 = (let _127_250 = (FSharp_Format.text "end")
in (_127_250)::[])
in (_127_252)::_127_251))
in (_127_254)::_127_253))
in (_127_256)::_127_255))
in (_127_258)::_127_257))
in (FSharp_Format.combine FSharp_Format.hardline _127_259))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _127_266 = (let _127_265 = (let _127_264 = (FSharp_Format.text "match")
in (let _127_263 = (let _127_262 = (FSharp_Format.parens cond)
in (let _127_261 = (let _127_260 = (FSharp_Format.text "with")
in (_127_260)::[])
in (_127_262)::_127_261))
in (_127_264)::_127_263))
in (FSharp_Format.reduce1 _127_265))
in (_127_266)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _127_271 = (let _127_270 = (FSharp_Format.text "raise")
in (let _127_269 = (let _127_268 = (let _127_267 = (ptctor currentModule exn)
in (FSharp_Format.text _127_267))
in (_127_268)::[])
in (_127_270)::_127_269))
in (FSharp_Format.reduce1 _127_271))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _127_280 = (let _127_279 = (FSharp_Format.text "raise")
in (let _127_278 = (let _127_277 = (let _127_272 = (ptctor currentModule exn)
in (FSharp_Format.text _127_272))
in (let _127_276 = (let _127_275 = (let _127_274 = (let _127_273 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_273 args))
in (FSharp_Format.parens _127_274))
in (_127_275)::[])
in (_127_277)::_127_276))
in (_127_279)::_127_278))
in (FSharp_Format.reduce1 _127_280)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _127_297 = (let _127_296 = (let _127_284 = (let _127_283 = (FSharp_Format.text "try")
in (let _127_282 = (let _127_281 = (FSharp_Format.text "begin")
in (_127_281)::[])
in (_127_283)::_127_282))
in (FSharp_Format.reduce1 _127_284))
in (let _127_295 = (let _127_294 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_293 = (let _127_292 = (let _127_288 = (let _127_287 = (FSharp_Format.text "end")
in (let _127_286 = (let _127_285 = (FSharp_Format.text "with")
in (_127_285)::[])
in (_127_287)::_127_286))
in (FSharp_Format.reduce1 _127_288))
in (let _127_291 = (let _127_290 = (let _127_289 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _127_289))
in (_127_290)::[])
in (_127_292)::_127_291))
in (_127_294)::_127_293))
in (_127_296)::_127_295))
in (FSharp_Format.combine FSharp_Format.hardline _127_297))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _61_381 = (let _127_302 = (as_bin_op p)
in (Support.Option.get _127_302))
in (match (_61_381) with
| (_61_378, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _127_305 = (let _127_304 = (let _127_303 = (FSharp_Format.text txt)
in (_127_303)::(e2)::[])
in (e1)::_127_304)
in (FSharp_Format.reduce1 _127_305))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _61_391 = (let _127_309 = (as_uni_op p)
in (Support.Option.get _127_309))
in (match (_61_391) with
| (_61_389, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _127_313 = (let _127_312 = (FSharp_Format.text txt)
in (let _127_311 = (let _127_310 = (FSharp_Format.parens e1)
in (_127_310)::[])
in (_127_312)::_127_311))
in (FSharp_Format.reduce1 _127_313))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _127_316 = (string_of_mlconstant c)
in (FSharp_Format.text _127_316))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _61_408 ) -> (match (_61_408) with
| (name, p) -> begin
(let _127_325 = (let _127_324 = (let _127_319 = (ptsym currentModule (path, name))
in (FSharp_Format.text _127_319))
in (let _127_323 = (let _127_322 = (FSharp_Format.text "=")
in (let _127_321 = (let _127_320 = (doc_of_pattern currentModule p)
in (_127_320)::[])
in (_127_322)::_127_321))
in (_127_324)::_127_323))
in (FSharp_Format.reduce1 _127_325))
end))
in (let _127_328 = (let _127_327 = (FSharp_Format.text "; ")
in (let _127_326 = (Support.List.map for1 fields)
in (FSharp_Format.combine _127_327 _127_326)))
in (FSharp_Format.cbrackets _127_328)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _127_330 = (let _127_329 = (as_standard_constructor ctor)
in (Support.Option.get _127_329))
in (Support.Prims.snd _127_330))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, pats)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _127_332 = (let _127_331 = (as_standard_constructor ctor)
in (Support.Option.get _127_331))
in (Support.Prims.snd _127_332))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, pats)) with
| ("::", x::xs::[]) -> begin
(let _127_338 = (let _127_337 = (doc_of_pattern currentModule x)
in (let _127_336 = (let _127_335 = (FSharp_Format.text "::")
in (let _127_334 = (let _127_333 = (doc_of_pattern currentModule xs)
in (_127_333)::[])
in (_127_335)::_127_334))
in (_127_337)::_127_336))
in (FSharp_Format.reduce _127_338))
end
| (_61_425, Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (_61_427)::[]) -> begin
(let _127_343 = (let _127_342 = (FSharp_Format.text name)
in (let _127_341 = (let _127_340 = (let _127_339 = (Support.List.hd pats)
in (doc_of_pattern currentModule _127_339))
in (_127_340)::[])
in (_127_342)::_127_341))
in (FSharp_Format.reduce1 _127_343))
end
| _61_432 -> begin
(let _127_350 = (let _127_349 = (FSharp_Format.text name)
in (let _127_348 = (let _127_347 = (let _127_346 = (let _127_345 = (FSharp_Format.text ", ")
in (let _127_344 = (Support.List.map (doc_of_pattern currentModule) pats)
in (FSharp_Format.combine _127_345 _127_344)))
in (FSharp_Format.parens _127_346))
in (_127_347)::[])
in (_127_349)::_127_348))
in (FSharp_Format.reduce1 _127_350))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _127_352 = (let _127_351 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_351 ps))
in (FSharp_Format.parens _127_352)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _127_353 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _127_353 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _61_445 ) -> (match (_61_445) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _127_359 = (let _127_358 = (FSharp_Format.text "|")
in (let _127_357 = (let _127_356 = (doc_of_pattern currentModule p)
in (_127_356)::[])
in (_127_358)::_127_357))
in (FSharp_Format.reduce1 _127_359))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _127_365 = (let _127_364 = (FSharp_Format.text "|")
in (let _127_363 = (let _127_362 = (doc_of_pattern currentModule p)
in (let _127_361 = (let _127_360 = (FSharp_Format.text "when")
in (_127_360)::(c)::[])
in (_127_362)::_127_361))
in (_127_364)::_127_363))
in (FSharp_Format.reduce1 _127_365)))
end)
in (let _127_376 = (let _127_375 = (let _127_370 = (let _127_369 = (let _127_368 = (FSharp_Format.text "->")
in (let _127_367 = (let _127_366 = (FSharp_Format.text "begin")
in (_127_366)::[])
in (_127_368)::_127_367))
in (case)::_127_369)
in (FSharp_Format.reduce1 _127_370))
in (let _127_374 = (let _127_373 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _127_372 = (let _127_371 = (FSharp_Format.text "end")
in (_127_371)::[])
in (_127_373)::_127_372))
in (_127_375)::_127_374))
in (FSharp_Format.combine FSharp_Format.hardline _127_376)))
end))
and doc_of_lets = (fun ( currentModule ) ( _61_455 ) -> (match (_61_455) with
| (rec_, top_level, lets) -> begin
(let for1 = (fun ( _61_462 ) -> (match (_61_462) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _61_459; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _61_468 ) -> (match (_61_468) with
| (x, _61_467) -> begin
(FSharp_Format.text x)
end)) ids)
in (let ty_annot = (match (((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ()) && (rec_ || top_level))) with
| true -> begin
(match (tys) with
| (None) | (Some ((_::_, _))) -> begin
(FSharp_Format.text "")
end
| Some (([], ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _127_383 = (let _127_382 = (FSharp_Format.text ":")
in (_127_382)::(ty)::[])
in (FSharp_Format.reduce1 _127_383)))
end)
end
| false -> begin
(FSharp_Format.text "")
end)
in (let _127_390 = (let _127_389 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _127_388 = (let _127_387 = (FSharp_Format.reduce1 ids)
in (let _127_386 = (let _127_385 = (let _127_384 = (FSharp_Format.text "=")
in (_127_384)::(e)::[])
in (ty_annot)::_127_385)
in (_127_387)::_127_386))
in (_127_389)::_127_388))
in (FSharp_Format.reduce1 _127_390))))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _127_394 = (let _127_393 = (FSharp_Format.text "let")
in (let _127_392 = (let _127_391 = (FSharp_Format.text "rec")
in (_127_391)::[])
in (_127_393)::_127_392))
in (FSharp_Format.reduce1 _127_394))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _127_398 = (let _127_397 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_127_397)::(doc)::[])
in (FSharp_Format.reduce1 _127_398))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _61_497 ) -> (match (_61_497) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
end
| _61_502 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _127_407 = (let _127_406 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _127_406 doc))
in (FSharp_Format.parens _127_407)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _61_515 ) -> (match (_61_515) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _127_414 = (let _127_413 = (let _127_412 = (FSharp_Format.text ":")
in (_127_412)::(ty)::[])
in (name)::_127_413)
in (FSharp_Format.reduce1 _127_414))))
end))
in (let _127_417 = (let _127_416 = (FSharp_Format.text "; ")
in (let _127_415 = (Support.List.map forfield fields)
in (FSharp_Format.combine _127_416 _127_415)))
in (FSharp_Format.cbrackets _127_417)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _61_523 ) -> (match (_61_523) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _61_526 -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _127_420 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_420 tys))
in (let _127_424 = (let _127_423 = (FSharp_Format.text name)
in (let _127_422 = (let _127_421 = (FSharp_Format.text "of")
in (_127_421)::(tys)::[])
in (_127_423)::_127_422))
in (FSharp_Format.reduce1 _127_424))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _127_427 = (let _127_426 = (FSharp_Format.text "|")
in (_127_426)::(d)::[])
in (FSharp_Format.reduce1 _127_427))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _127_431 = (let _127_430 = (let _127_429 = (let _127_428 = (ptsym currentModule ([], x))
in (FSharp_Format.text _127_428))
in (_127_429)::[])
in (tparams)::_127_430)
in (FSharp_Format.reduce1 _127_431))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _127_436 = (let _127_435 = (let _127_434 = (let _127_433 = (let _127_432 = (FSharp_Format.text "=")
in (_127_432)::[])
in (doc)::_127_433)
in (FSharp_Format.reduce1 _127_434))
in (_127_435)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _127_436)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _127_441 = (let _127_440 = (FSharp_Format.text "type")
in (let _127_439 = (let _127_438 = (let _127_437 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _127_437 doc))
in (_127_438)::[])
in (_127_440)::_127_439))
in (FSharp_Format.reduce1 _127_441))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _127_461 = (let _127_460 = (let _127_453 = (let _127_452 = (FSharp_Format.text "module")
in (let _127_451 = (let _127_450 = (FSharp_Format.text x)
in (let _127_449 = (let _127_448 = (FSharp_Format.text "=")
in (_127_448)::[])
in (_127_450)::_127_449))
in (_127_452)::_127_451))
in (FSharp_Format.reduce1 _127_453))
in (let _127_459 = (let _127_458 = (doc_of_sig currentModule subsig)
in (let _127_457 = (let _127_456 = (let _127_455 = (let _127_454 = (FSharp_Format.text "end")
in (_127_454)::[])
in (FSharp_Format.reduce1 _127_455))
in (_127_456)::[])
in (_127_458)::_127_457))
in (_127_460)::_127_459))
in (FSharp_Format.combine FSharp_Format.hardline _127_461))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _127_465 = (let _127_464 = (FSharp_Format.text "exception")
in (let _127_463 = (let _127_462 = (FSharp_Format.text x)
in (_127_462)::[])
in (_127_464)::_127_463))
in (FSharp_Format.reduce1 _127_465))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _127_467 = (let _127_466 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_466 args))
in (FSharp_Format.parens _127_467))
in (let _127_473 = (let _127_472 = (FSharp_Format.text "exception")
in (let _127_471 = (let _127_470 = (FSharp_Format.text x)
in (let _127_469 = (let _127_468 = (FSharp_Format.text "of")
in (_127_468)::(args)::[])
in (_127_470)::_127_469))
in (_127_472)::_127_471))
in (FSharp_Format.reduce1 _127_473))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_61_557, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _127_479 = (let _127_478 = (FSharp_Format.text "val")
in (let _127_477 = (let _127_476 = (FSharp_Format.text x)
in (let _127_475 = (let _127_474 = (FSharp_Format.text ": ")
in (_127_474)::(ty)::[])
in (_127_476)::_127_475))
in (_127_478)::_127_477))
in (FSharp_Format.reduce1 _127_479)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _127_490 = (let _127_489 = (FSharp_Format.text "exception")
in (let _127_488 = (let _127_487 = (FSharp_Format.text x)
in (_127_487)::[])
in (_127_489)::_127_488))
in (FSharp_Format.reduce1 _127_490))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _127_492 = (let _127_491 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _127_491 args))
in (FSharp_Format.parens _127_492))
in (let _127_498 = (let _127_497 = (FSharp_Format.text "exception")
in (let _127_496 = (let _127_495 = (FSharp_Format.text x)
in (let _127_494 = (let _127_493 = (FSharp_Format.text "of")
in (_127_493)::(args)::[])
in (_127_495)::_127_494))
in (_127_497)::_127_496))
in (FSharp_Format.reduce1 _127_498))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, true, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _127_506 = (let _127_505 = (FSharp_Format.text "let")
in (let _127_504 = (let _127_503 = (FSharp_Format.text "_")
in (let _127_502 = (let _127_501 = (FSharp_Format.text "=")
in (let _127_500 = (let _127_499 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_127_499)::[])
in (_127_501)::_127_500))
in (_127_503)::_127_502))
in (_127_505)::_127_504))
in (FSharp_Format.reduce1 _127_506))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _61_596 ) -> (match (_61_596) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _61_603 ) -> (match (_61_603) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _127_525 = (let _127_524 = (FSharp_Format.text "module")
in (let _127_523 = (let _127_522 = (FSharp_Format.text x)
in (let _127_521 = (let _127_520 = (FSharp_Format.text ":")
in (let _127_519 = (let _127_518 = (FSharp_Format.text "sig")
in (_127_518)::[])
in (_127_520)::_127_519))
in (_127_522)::_127_521))
in (_127_524)::_127_523))
in (FSharp_Format.reduce1 _127_525))
in (let tail = (let _127_527 = (let _127_526 = (FSharp_Format.text "end")
in (_127_526)::[])
in (FSharp_Format.reduce1 _127_527))
in (let doc = (Support.Option.map (fun ( _61_609 ) -> (match (_61_609) with
| (s, _61_608) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _127_537 = (let _127_536 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _127_535 = (let _127_534 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _127_533 = (let _127_532 = (FSharp_Format.reduce sub)
in (let _127_531 = (let _127_530 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_127_530)::[])
in (_127_532)::_127_531))
in (_127_534)::_127_533))
in (_127_536)::_127_535))
in (FSharp_Format.reduce _127_537)))))))
end))
and for1_mod = (fun ( istop ) ( _61_622 ) -> (match (_61_622) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _61_623 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _127_550 = (match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _127_542 = (FSharp_Format.text "module")
in (let _127_541 = (let _127_540 = (FSharp_Format.text x)
in (_127_540)::[])
in (_127_542)::_127_541))
end
| false -> begin
(match ((not (istop))) with
| true -> begin
(let _127_549 = (FSharp_Format.text "module")
in (let _127_548 = (let _127_547 = (FSharp_Format.text x)
in (let _127_546 = (let _127_545 = (FSharp_Format.text "=")
in (let _127_544 = (let _127_543 = (FSharp_Format.text "struct")
in (_127_543)::[])
in (_127_545)::_127_544))
in (_127_547)::_127_546))
in (_127_549)::_127_548))
end
| false -> begin
[]
end)
end)
in (FSharp_Format.reduce1 _127_550))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _127_552 = (let _127_551 = (FSharp_Format.text "end")
in (_127_551)::[])
in (FSharp_Format.reduce1 _127_552))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _61_630 ) -> (match (_61_630) with
| (_61_628, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let prefix = (match ((Microsoft_FStar_Extraction_ML_Util.codegen_fsharp ())) with
| true -> begin
(let _127_556 = (let _127_555 = (FSharp_Format.text "#light \"off\"")
in (FSharp_Format.cat _127_555 FSharp_Format.hardline))
in (_127_556)::[])
end
| false -> begin
[]
end)
in (let _127_565 = (let _127_564 = (let _127_563 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _127_562 = (let _127_561 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _127_560 = (let _127_559 = (FSharp_Format.reduce sub)
in (let _127_558 = (let _127_557 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_127_557)::[])
in (_127_559)::_127_558))
in (_127_561)::_127_560))
in (_127_563)::_127_562))
in (Support.List.append prefix _127_564))
in (Support.All.pipe_left FSharp_Format.reduce _127_565)))))))))
end))
in (let docs = (Support.List.map (fun ( _61_642 ) -> (match (_61_642) with
| (x, s, m) -> begin
(let _127_567 = (for1_mod true (x, s, m))
in (x, _127_567))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (let _127_574 = (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _127_574 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (let _127_579 = (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _127_579 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))





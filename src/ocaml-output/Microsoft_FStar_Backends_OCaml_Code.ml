
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
| Infix (_67_3) -> begin
_67_3
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

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "mod"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "!"))::(("exit", "exit"))::(("failwith", "failwith"))::(("raise", "raise"))::[]

let prim_types = (("char", "char"))::(("bool", "bool"))::(("string", "string"))::(("unit", "unit"))::(("ref", "ref"))::(("array", "array"))::(("option", "option"))::(("list", "list"))::(("int", "int"))::(("int64", "Int64.t"))::[]

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ( ns ) -> (ns = ("Support")::("Prims")::[]))

let as_bin_op = (fun ( _67_7 ) -> (match (_67_7) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_13 ) -> (match (_67_13) with
| (y, _67_10, _67_12) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _67_17 ) -> (match (_67_17) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_21 ) -> (match (_67_21) with
| (y, _67_20) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _67_25 ) -> (match (_67_25) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_29 ) -> (match (_67_29) with
| (y, _67_28) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _67_33 ) -> (match (_67_33) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _67_37 ) -> (match (_67_37) with
| (y, _67_36) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _67_41 ) ( inner ) ( doc ) -> (match (_67_41) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _67_50 = _inner
in (match (_67_50) with
| (pi, fi) -> begin
(let _67_53 = _outer
in (match (_67_53) with
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
| (_67_77, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_67_81, _67_83) -> begin
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
(Support.String.strcat "\\x" (Support.Microsoft.FStar.Util.hex_string_of_byte i))
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
| _67_101 -> begin
(ocaml_u8_codepoint (Support.Microsoft.FStar.Util.byte_of_char c))
end)
end))

let string_of_mlconstant = (fun ( sctt ) -> (match (sctt) with
| Microsoft_FStar_Backends_ML_Syntax.MLC_Unit -> begin
"()"
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (true) -> begin
"true"
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Bool (false) -> begin
"false"
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Char (c) -> begin
(let _138_63 = (let _138_62 = (encode_char c)
in (Support.String.strcat "\'" _138_62))
in (Support.String.strcat _138_63 "\'"))
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Byte (c) -> begin
(Support.String.strcat (Support.String.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Int32 (i) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 i)
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Int64 (i) -> begin
(Support.String.strcat (Support.Microsoft.FStar.Util.string_of_int64 i) "L")
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Float (d) -> begin
(Support.Microsoft.FStar.Util.string_of_float d)
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)
in (Support.String.strcat (Support.String.strcat "\"" bytes) "\""))
end
| Microsoft_FStar_Backends_ML_Syntax.MLC_String (chars) -> begin
(let chars = (Support.String.collect encode_char chars)
in (Support.String.strcat (Support.String.strcat "\"" chars) "\""))
end))

let rec doc_of_mltype = (fun ( outer ) ( ty ) -> (match (ty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x) -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let doc = (let _138_70 = (let _138_69 = (let _138_68 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _138_68 doc))
in (FSharp_Format.hbox _138_69))
in (FSharp_Format.parens _138_70))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, name)) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype (t_prio_name, Left) arg)
end
| _67_140 -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let _138_73 = (let _138_72 = (let _138_71 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_71 args))
in (FSharp_Format.hbox _138_72))
in (FSharp_Format.parens _138_73)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _138_75 = (let _138_74 = (as_standard_type name)
in (Support.Option.get _138_74))
in (Support.Prims.snd _138_75))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _138_79 = (let _138_78 = (let _138_77 = (let _138_76 = (FSharp_Format.text name)
in (_138_76)::[])
in (args)::_138_77)
in (FSharp_Format.reduce1 _138_78))
in (FSharp_Format.hbox _138_79))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _67_146, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _138_84 = (let _138_83 = (let _138_82 = (let _138_81 = (let _138_80 = (FSharp_Format.text " -> ")
in (_138_80)::(d2)::[])
in (d1)::_138_81)
in (FSharp_Format.reduce1 _138_82))
in (FSharp_Format.hbox _138_83))
in (maybe_paren outer t_prio_fun _138_84))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _138_89 = (let _138_88 = (let _138_87 = (let _138_86 = (let _138_85 = (FSharp_Format.text " ")
in (_138_85)::(d1)::[])
in (d2)::_138_86)
in (FSharp_Format.reduce1 _138_87))
in (FSharp_Format.hbox _138_88))
in (maybe_paren outer t_prio_fun _138_89))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _138_99 = (let _138_98 = (let _138_97 = (FSharp_Format.text "Obj.magic ")
in (_138_97)::(doc)::[])
in (FSharp_Format.reduce _138_98))
in (FSharp_Format.parens _138_99)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _138_103 = (let _138_102 = (let _138_101 = (FSharp_Format.text ";")
in (_138_101)::(FSharp_Format.hardline)::[])
in (d)::_138_102)
in (FSharp_Format.reduce _138_103))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _138_104 = (string_of_mlconstant c)
in (FSharp_Format.text _138_104))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _67_176)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _138_105 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _138_105))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_188 ) -> (match (_67_188) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _138_112 = (let _138_111 = (let _138_108 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _138_108))
in (let _138_110 = (let _138_109 = (FSharp_Format.text "=")
in (_138_109)::(doc)::[])
in (_138_111)::_138_110))
in (FSharp_Format.reduce1 _138_112)))
end))
in (let _138_115 = (let _138_114 = (FSharp_Format.text "; ")
in (let _138_113 = (Support.List.map for1 fields)
in (FSharp_Format.combine _138_114 _138_113)))
in (FSharp_Format.cbrackets _138_115)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _138_117 = (let _138_116 = (as_standard_constructor ctor)
in (Support.Option.get _138_116))
in (Support.Prims.snd _138_117))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _138_119 = (let _138_118 = (as_standard_constructor ctor)
in (Support.Option.get _138_118))
in (Support.Prims.snd _138_119))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _138_123 = (let _138_122 = (FSharp_Format.parens x)
in (let _138_121 = (let _138_120 = (FSharp_Format.text "::")
in (_138_120)::(xs)::[])
in (_138_122)::_138_121))
in (FSharp_Format.reduce _138_123))
end
| (_67_207, _67_209) -> begin
(let _138_129 = (let _138_128 = (FSharp_Format.text name)
in (let _138_127 = (let _138_126 = (let _138_125 = (let _138_124 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_124 args))
in (FSharp_Format.parens _138_125))
in (_138_126)::[])
in (_138_128)::_138_127))
in (FSharp_Format.reduce1 _138_129))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _138_131 = (let _138_130 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_130 docs))
in (FSharp_Format.parens _138_131))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _138_137 = (let _138_136 = (let _138_135 = (let _138_134 = (let _138_133 = (let _138_132 = (FSharp_Format.text "in")
in (_138_132)::(body)::[])
in (FSharp_Format.reduce1 _138_133))
in (_138_134)::[])
in (doc)::_138_135)
in (FSharp_Format.combine FSharp_Format.hardline _138_136))
in (FSharp_Format.parens _138_137))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _67_238 = (let _138_138 = (as_bin_op p)
in (Support.Option.get _138_138))
in (match (_67_238) with
| (_67_235, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _138_141 = (let _138_140 = (let _138_139 = (FSharp_Format.text txt)
in (_138_139)::(e2)::[])
in (e1)::_138_140)
in (FSharp_Format.reduce1 _138_141))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _67_250 = (let _138_142 = (as_uni_op p)
in (Support.Option.get _138_142))
in (match (_67_250) with
| (_67_248, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _138_146 = (let _138_145 = (FSharp_Format.text txt)
in (let _138_144 = (let _138_143 = (FSharp_Format.parens e1)
in (_138_143)::[])
in (_138_145)::_138_144))
in (FSharp_Format.reduce1 _138_146))
in (FSharp_Format.parens doc)))
end))
end
| _67_254 -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _138_147 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _138_147))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _138_153 = (let _138_152 = (let _138_151 = (FSharp_Format.text ".")
in (let _138_150 = (let _138_149 = (let _138_148 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _138_148))
in (_138_149)::[])
in (_138_151)::_138_150))
in (e)::_138_152)
in (FSharp_Format.reduce _138_153))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _67_272 ) -> (match (_67_272) with
| ((x, _67_269), xt) -> begin
(let _138_166 = (let _138_165 = (FSharp_Format.text "(")
in (let _138_164 = (let _138_163 = (FSharp_Format.text x)
in (let _138_162 = (let _138_161 = (match (xt) with
| Some (xxt) -> begin
(let _138_158 = (let _138_157 = (FSharp_Format.text " : ")
in (let _138_156 = (let _138_155 = (doc_of_mltype outer xxt)
in (_138_155)::[])
in (_138_157)::_138_156))
in (FSharp_Format.reduce1 _138_158))
end
| _67_276 -> begin
(FSharp_Format.text "")
end)
in (let _138_160 = (let _138_159 = (FSharp_Format.text ")")
in (_138_159)::[])
in (_138_161)::_138_160))
in (_138_163)::_138_162))
in (_138_165)::_138_164))
in (FSharp_Format.reduce1 _138_166))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _138_172 = (let _138_171 = (FSharp_Format.text "fun")
in (let _138_170 = (let _138_169 = (FSharp_Format.reduce1 ids)
in (let _138_168 = (let _138_167 = (FSharp_Format.text "->")
in (_138_167)::(body)::[])
in (_138_169)::_138_168))
in (_138_171)::_138_170))
in (FSharp_Format.reduce1 _138_172))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _138_185 = (let _138_184 = (let _138_179 = (let _138_178 = (FSharp_Format.text "if")
in (let _138_177 = (let _138_176 = (let _138_175 = (FSharp_Format.text "then")
in (let _138_174 = (let _138_173 = (FSharp_Format.text "begin")
in (_138_173)::[])
in (_138_175)::_138_174))
in (cond)::_138_176)
in (_138_178)::_138_177))
in (FSharp_Format.reduce1 _138_179))
in (let _138_183 = (let _138_182 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _138_181 = (let _138_180 = (FSharp_Format.text "end")
in (_138_180)::[])
in (_138_182)::_138_181))
in (_138_184)::_138_183))
in (FSharp_Format.combine FSharp_Format.hardline _138_185))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _138_208 = (let _138_207 = (let _138_192 = (let _138_191 = (FSharp_Format.text "if")
in (let _138_190 = (let _138_189 = (let _138_188 = (FSharp_Format.text "then")
in (let _138_187 = (let _138_186 = (FSharp_Format.text "begin")
in (_138_186)::[])
in (_138_188)::_138_187))
in (cond)::_138_189)
in (_138_191)::_138_190))
in (FSharp_Format.reduce1 _138_192))
in (let _138_206 = (let _138_205 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _138_204 = (let _138_203 = (let _138_198 = (let _138_197 = (FSharp_Format.text "end")
in (let _138_196 = (let _138_195 = (FSharp_Format.text "else")
in (let _138_194 = (let _138_193 = (FSharp_Format.text "begin")
in (_138_193)::[])
in (_138_195)::_138_194))
in (_138_197)::_138_196))
in (FSharp_Format.reduce1 _138_198))
in (let _138_202 = (let _138_201 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _138_200 = (let _138_199 = (FSharp_Format.text "end")
in (_138_199)::[])
in (_138_201)::_138_200))
in (_138_203)::_138_202))
in (_138_205)::_138_204))
in (_138_207)::_138_206))
in (FSharp_Format.combine FSharp_Format.hardline _138_208))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _138_215 = (let _138_214 = (let _138_213 = (FSharp_Format.text "match")
in (let _138_212 = (let _138_211 = (FSharp_Format.parens cond)
in (let _138_210 = (let _138_209 = (FSharp_Format.text "with")
in (_138_209)::[])
in (_138_211)::_138_210))
in (_138_213)::_138_212))
in (FSharp_Format.reduce1 _138_214))
in (_138_215)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _138_220 = (let _138_219 = (FSharp_Format.text "raise")
in (let _138_218 = (let _138_217 = (let _138_216 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _138_216))
in (_138_217)::[])
in (_138_219)::_138_218))
in (FSharp_Format.reduce1 _138_220))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _138_229 = (let _138_228 = (FSharp_Format.text "raise")
in (let _138_227 = (let _138_226 = (let _138_221 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _138_221))
in (let _138_225 = (let _138_224 = (let _138_223 = (let _138_222 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_222 args))
in (FSharp_Format.parens _138_223))
in (_138_224)::[])
in (_138_226)::_138_225))
in (_138_228)::_138_227))
in (FSharp_Format.reduce1 _138_229)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _138_246 = (let _138_245 = (let _138_233 = (let _138_232 = (FSharp_Format.text "try")
in (let _138_231 = (let _138_230 = (FSharp_Format.text "begin")
in (_138_230)::[])
in (_138_232)::_138_231))
in (FSharp_Format.reduce1 _138_233))
in (let _138_244 = (let _138_243 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _138_242 = (let _138_241 = (let _138_237 = (let _138_236 = (FSharp_Format.text "end")
in (let _138_235 = (let _138_234 = (FSharp_Format.text "with")
in (_138_234)::[])
in (_138_236)::_138_235))
in (FSharp_Format.reduce1 _138_237))
in (let _138_240 = (let _138_239 = (let _138_238 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _138_238))
in (_138_239)::[])
in (_138_241)::_138_240))
in (_138_243)::_138_242))
in (_138_245)::_138_244))
in (FSharp_Format.combine FSharp_Format.hardline _138_246))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _138_248 = (string_of_mlconstant c)
in (FSharp_Format.text _138_248))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_329 ) -> (match (_67_329) with
| (name, p) -> begin
(let _138_257 = (let _138_256 = (let _138_251 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _138_251))
in (let _138_255 = (let _138_254 = (FSharp_Format.text "=")
in (let _138_253 = (let _138_252 = (doc_of_pattern p)
in (_138_252)::[])
in (_138_254)::_138_253))
in (_138_256)::_138_255))
in (FSharp_Format.reduce1 _138_257))
end))
in (let _138_260 = (let _138_259 = (FSharp_Format.text "; ")
in (let _138_258 = (Support.List.map for1 fields)
in (FSharp_Format.combine _138_259 _138_258)))
in (FSharp_Format.cbrackets _138_260)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _138_262 = (let _138_261 = (as_standard_constructor ctor)
in (Support.Option.get _138_261))
in (Support.Prims.snd _138_262))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, ps)) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _138_264 = (let _138_263 = (as_standard_constructor ctor)
in (Support.Option.get _138_263))
in (Support.Prims.snd _138_264))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _138_267 = (let _138_266 = (let _138_265 = (FSharp_Format.text "::")
in (_138_265)::(xs)::[])
in (x)::_138_266)
in (FSharp_Format.reduce _138_267))
end
| (_67_347, _67_349) -> begin
(let _138_273 = (let _138_272 = (FSharp_Format.text name)
in (let _138_271 = (let _138_270 = (let _138_269 = (let _138_268 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_268 ps))
in (FSharp_Format.parens _138_269))
in (_138_270)::[])
in (_138_272)::_138_271))
in (FSharp_Format.reduce1 _138_273))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _138_275 = (let _138_274 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_274 ps))
in (FSharp_Format.parens _138_275)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _138_276 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _138_276 ps))))
end))
and doc_of_branch = (fun ( _67_362 ) -> (match (_67_362) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _138_281 = (let _138_280 = (FSharp_Format.text "|")
in (let _138_279 = (let _138_278 = (doc_of_pattern p)
in (_138_278)::[])
in (_138_280)::_138_279))
in (FSharp_Format.reduce1 _138_281))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _138_287 = (let _138_286 = (FSharp_Format.text "|")
in (let _138_285 = (let _138_284 = (doc_of_pattern p)
in (let _138_283 = (let _138_282 = (FSharp_Format.text "when")
in (_138_282)::(c)::[])
in (_138_284)::_138_283))
in (_138_286)::_138_285))
in (FSharp_Format.reduce1 _138_287)))
end)
in (let _138_298 = (let _138_297 = (let _138_292 = (let _138_291 = (let _138_290 = (FSharp_Format.text "->")
in (let _138_289 = (let _138_288 = (FSharp_Format.text "begin")
in (_138_288)::[])
in (_138_290)::_138_289))
in (case)::_138_291)
in (FSharp_Format.reduce1 _138_292))
in (let _138_296 = (let _138_295 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _138_294 = (let _138_293 = (FSharp_Format.text "end")
in (_138_293)::[])
in (_138_295)::_138_294))
in (_138_297)::_138_296))
in (FSharp_Format.combine FSharp_Format.hardline _138_298)))
end))
and doc_of_lets = (fun ( _67_370 ) -> (match (_67_370) with
| (rec_, lets) -> begin
(let for1 = (fun ( _67_376 ) -> (match (_67_376) with
| (name, tys, ids, e) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let ids = (Support.List.map (fun ( _67_381 ) -> (match (_67_381) with
| (x, _67_380) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _138_308 = (let _138_307 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _138_306 = (let _138_305 = (FSharp_Format.reduce1 ids)
in (let _138_304 = (let _138_303 = (FSharp_Format.text "=")
in (_138_303)::(e)::[])
in (_138_305)::_138_304))
in (_138_307)::_138_306))
in (FSharp_Format.reduce1 _138_308))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _138_312 = (let _138_311 = (FSharp_Format.text "let")
in (let _138_310 = (let _138_309 = (FSharp_Format.text "rec")
in (_138_309)::[])
in (_138_311)::_138_310))
in (FSharp_Format.reduce1 _138_312))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _138_316 = (let _138_315 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_138_315)::(doc)::[])
in (FSharp_Format.reduce1 _138_316))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( decls ) -> (let for1 = (fun ( _67_393 ) -> (match (_67_393) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))
end
| _67_398 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))) tparams)
in (let _138_323 = (let _138_322 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _138_322 doc))
in (FSharp_Format.parens _138_323)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _67_411 ) -> (match (_67_411) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _138_330 = (let _138_329 = (let _138_328 = (FSharp_Format.text ":")
in (_138_328)::(ty)::[])
in (name)::_138_329)
in (FSharp_Format.reduce1 _138_330))))
end))
in (let _138_333 = (let _138_332 = (FSharp_Format.text "; ")
in (let _138_331 = (Support.List.map forfield fields)
in (FSharp_Format.combine _138_332 _138_331)))
in (FSharp_Format.cbrackets _138_333)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _67_419 ) -> (match (_67_419) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _67_422 -> begin
(let tys = (Support.List.map (doc_of_mltype (t_prio_tpl, Left)) tys)
in (let tys = (let _138_336 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _138_336 tys))
in (let _138_340 = (let _138_339 = (FSharp_Format.text name)
in (let _138_338 = (let _138_337 = (FSharp_Format.text "of")
in (_138_337)::(tys)::[])
in (_138_339)::_138_338))
in (FSharp_Format.reduce1 _138_340))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _138_343 = (let _138_342 = (FSharp_Format.text "|")
in (_138_342)::(d)::[])
in (FSharp_Format.reduce1 _138_343))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _138_347 = (let _138_346 = (let _138_345 = (let _138_344 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _138_344))
in (_138_345)::[])
in (tparams)::_138_346)
in (FSharp_Format.reduce1 _138_347))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _138_352 = (let _138_351 = (let _138_350 = (let _138_349 = (let _138_348 = (FSharp_Format.text "=")
in (_138_348)::[])
in (doc)::_138_349)
in (FSharp_Format.reduce1 _138_350))
in (_138_351)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _138_352)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _138_357 = (let _138_356 = (FSharp_Format.text "type")
in (let _138_355 = (let _138_354 = (let _138_353 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _138_353 doc))
in (_138_354)::[])
in (_138_356)::_138_355))
in (FSharp_Format.reduce1 _138_357))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _138_374 = (let _138_373 = (let _138_366 = (let _138_365 = (FSharp_Format.text "module")
in (let _138_364 = (let _138_363 = (FSharp_Format.text x)
in (let _138_362 = (let _138_361 = (FSharp_Format.text "=")
in (_138_361)::[])
in (_138_363)::_138_362))
in (_138_365)::_138_364))
in (FSharp_Format.reduce1 _138_366))
in (let _138_372 = (let _138_371 = (doc_of_sig subsig)
in (let _138_370 = (let _138_369 = (let _138_368 = (let _138_367 = (FSharp_Format.text "end")
in (_138_367)::[])
in (FSharp_Format.reduce1 _138_368))
in (_138_369)::[])
in (_138_371)::_138_370))
in (_138_373)::_138_372))
in (FSharp_Format.combine FSharp_Format.hardline _138_374))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _138_378 = (let _138_377 = (FSharp_Format.text "exception")
in (let _138_376 = (let _138_375 = (FSharp_Format.text x)
in (_138_375)::[])
in (_138_377)::_138_376))
in (FSharp_Format.reduce1 _138_378))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _138_380 = (let _138_379 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _138_379 args))
in (FSharp_Format.parens _138_380))
in (let _138_386 = (let _138_385 = (FSharp_Format.text "exception")
in (let _138_384 = (let _138_383 = (FSharp_Format.text x)
in (let _138_382 = (let _138_381 = (FSharp_Format.text "of")
in (_138_381)::(args)::[])
in (_138_383)::_138_382))
in (_138_385)::_138_384))
in (FSharp_Format.reduce1 _138_386))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_67_452, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _138_392 = (let _138_391 = (FSharp_Format.text "val")
in (let _138_390 = (let _138_389 = (FSharp_Format.text x)
in (let _138_388 = (let _138_387 = (FSharp_Format.text ": ")
in (_138_387)::(ty)::[])
in (_138_389)::_138_388))
in (_138_391)::_138_390))
in (FSharp_Format.reduce1 _138_392)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _138_400 = (let _138_399 = (FSharp_Format.text "exception")
in (let _138_398 = (let _138_397 = (FSharp_Format.text x)
in (_138_397)::[])
in (_138_399)::_138_398))
in (FSharp_Format.reduce1 _138_400))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _138_402 = (let _138_401 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _138_401 args))
in (FSharp_Format.parens _138_402))
in (let _138_408 = (let _138_407 = (FSharp_Format.text "exception")
in (let _138_406 = (let _138_405 = (FSharp_Format.text x)
in (let _138_404 = (let _138_403 = (FSharp_Format.text "of")
in (_138_403)::(args)::[])
in (_138_405)::_138_404))
in (_138_407)::_138_406))
in (FSharp_Format.reduce1 _138_408))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _138_416 = (let _138_415 = (FSharp_Format.text "let")
in (let _138_414 = (let _138_413 = (FSharp_Format.text "_")
in (let _138_412 = (let _138_411 = (FSharp_Format.text "=")
in (let _138_410 = (let _138_409 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_138_409)::[])
in (_138_411)::_138_410))
in (_138_413)::_138_412))
in (_138_415)::_138_414))
in (FSharp_Format.reduce1 _138_416))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _67_488 ) -> (match (_67_488) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _67_495 ) -> (match (_67_495) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _138_433 = (let _138_432 = (FSharp_Format.text "module")
in (let _138_431 = (let _138_430 = (FSharp_Format.text x)
in (let _138_429 = (let _138_428 = (FSharp_Format.text ":")
in (let _138_427 = (let _138_426 = (FSharp_Format.text "sig")
in (_138_426)::[])
in (_138_428)::_138_427))
in (_138_430)::_138_429))
in (_138_432)::_138_431))
in (FSharp_Format.reduce1 _138_433))
in (let tail = (let _138_435 = (let _138_434 = (FSharp_Format.text "end")
in (_138_434)::[])
in (FSharp_Format.reduce1 _138_435))
in (let doc = (Support.Option.map (fun ( _67_501 ) -> (match (_67_501) with
| (s, _67_500) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _138_445 = (let _138_444 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _138_443 = (let _138_442 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _138_441 = (let _138_440 = (FSharp_Format.reduce sub)
in (let _138_439 = (let _138_438 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_138_438)::[])
in (_138_440)::_138_439))
in (_138_442)::_138_441))
in (_138_444)::_138_443))
in (FSharp_Format.reduce _138_445)))))))
end))
and for1_mod = (fun ( istop ) ( _67_514 ) -> (match (_67_514) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _67_515 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _138_455 = (match ((not (istop))) with
| true -> begin
(let _138_454 = (FSharp_Format.text "module")
in (let _138_453 = (let _138_452 = (FSharp_Format.text x)
in (let _138_451 = (let _138_450 = (FSharp_Format.text "=")
in (let _138_449 = (let _138_448 = (FSharp_Format.text "struct")
in (_138_448)::[])
in (_138_450)::_138_449))
in (_138_452)::_138_451))
in (_138_454)::_138_453))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _138_455))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _138_457 = (let _138_456 = (FSharp_Format.text "end")
in (_138_456)::[])
in (FSharp_Format.reduce1 _138_457))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _67_522 ) -> (match (_67_522) with
| (_67_520, m) -> begin
(doc_of_mod m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _138_467 = (let _138_466 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _138_465 = (let _138_464 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _138_463 = (let _138_462 = (FSharp_Format.reduce sub)
in (let _138_461 = (let _138_460 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_138_460)::[])
in (_138_462)::_138_461))
in (_138_464)::_138_463))
in (_138_466)::_138_465))
in (FSharp_Format.reduce _138_467))))))))
end))
in (let docs = (Support.List.map (fun ( _67_533 ) -> (match (_67_533) with
| (x, s, m) -> begin
(let _138_469 = (for1_mod true (x, s, m))
in (x, _138_469))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))






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
| Infix (_59_3) -> begin
_59_3
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

let max_op_prec = (Microsoft_FStar_Util.max_int, Infix (NonAssoc))

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("All")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Map")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let rec in_ns = (fun x -> (match (x) with
| ([], _59_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_59_18, _59_20) -> begin
false
end))

let path_of_ns = (fun currentModule ns -> (let outsupport = (fun ns -> (let ns' = (Microsoft_FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| false -> begin
(ns')::[]
end)))
in (let chkin = (fun sns -> (match ((in_ns (sns, ns))) with
| true -> begin
Some (sns)
end
| false -> begin
None
end))
in (match ((Microsoft_FStar_List.tryPick chkin outmod)) with
| None -> begin
(match ((let _125_32 = (ST.read Microsoft_FStar_Options.codegen_libs)
in (Microsoft_FStar_List.tryPick chkin _125_32))) with
| None -> begin
(outsupport ns)
end
| _59_32 -> begin
ns
end)
end
| Some (sns) -> begin
("Support")::ns
end))))

let mlpath_of_mlpath = (fun currentModule x -> (match ((Microsoft_FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
| "Prims.Some" -> begin
([], "Some")
end
| "Prims.None" -> begin
([], "None")
end
| "Prims.failwith" -> begin
([], "failwith")
end
| "ST.alloc" -> begin
([], "ref")
end
| "ST.read" -> begin
(("Support")::("ST")::[], "read")
end
| "ST.op_ColonEquals" -> begin
(("Support")::("ST")::[], "op_ColonEquals")
end
| _59_44 -> begin
(let _59_47 = x
in (match (_59_47) with
| (ns, x) -> begin
(let _125_37 = (path_of_ns currentModule ns)
in (_125_37, x))
end))
end))

let ptsym_of_symbol = (fun s -> (match (((let _125_40 = (Microsoft_FStar_String.get s 0)
in (Microsoft_FStar_Char.lowercase _125_40)) <> (Microsoft_FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "l__" s)
end
| false -> begin
s
end))

let ptsym = (fun currentModule mlp -> (match ((Microsoft_FStar_List.isEmpty (Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Prims.snd mlp))
end
| false -> begin
(let _59_53 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_53) with
| (p, s) -> begin
(let _125_47 = (let _125_46 = (let _125_45 = (ptsym_of_symbol s)
in (_125_45)::[])
in (Microsoft_FStar_List.append p _125_46))
in (Microsoft_FStar_String.concat "." _125_47))
end))
end))

let ptctor = (fun currentModule mlp -> (let _59_58 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_58) with
| (p, s) -> begin
(let s = (match (((let _125_52 = (Microsoft_FStar_String.get s 0)
in (Microsoft_FStar_Char.uppercase _125_52)) <> (Microsoft_FStar_String.get s 0))) with
| true -> begin
(Prims.strcat "U__" s)
end
| false -> begin
s
end)
in (Microsoft_FStar_String.concat "." (Microsoft_FStar_List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "mod"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::(("exit", "exit"))::(("failwith", "failwith"))::(("raise", "raise"))::[]

let prim_types = (("char", "char"))::(("bool", "bool"))::(("string", "string"))::(("unit", "unit"))::(("ref", "ref"))::(("array", "array"))::(("option", "option"))::(("list", "list"))::(("int", "int"))::(("int64", "Int64.t"))::[]

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ns -> (ns = ("Prims")::[]))

let as_bin_op = (fun _59_63 -> (match (_59_63) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Microsoft_FStar_List.tryFind (fun _59_69 -> (match (_59_69) with
| (y, _59_66, _59_68) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun p -> ((as_bin_op p) <> None))

let as_uni_op = (fun _59_73 -> (match (_59_73) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Microsoft_FStar_List.tryFind (fun _59_77 -> (match (_59_77) with
| (y, _59_76) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun p -> ((as_uni_op p) <> None))

let as_standard_type = (fun _59_81 -> (match (_59_81) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Microsoft_FStar_List.tryFind (fun _59_85 -> (match (_59_85) with
| (y, _59_84) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun p -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun _59_89 -> (match (_59_89) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Microsoft_FStar_List.tryFind (fun _59_93 -> (match (_59_93) with
| (y, _59_92) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun p -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun _59_97 inner doc -> (match (_59_97) with
| (outer, side) -> begin
(let noparens = (fun _inner _outer side -> (let _59_106 = _inner
in (match (_59_106) with
| (pi, fi) -> begin
(let _59_109 = _outer
in (match (_59_109) with
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
| (_59_133, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_59_137, _59_139) -> begin
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

let ocaml_u8_codepoint = (fun i -> (match (((Microsoft_FStar_Util.int_of_byte i) = 0)) with
| true -> begin
"\\x00"
end
| false -> begin
(Prims.strcat "\\x" (Microsoft_FStar_Util.hex_string_of_byte i))
end))

let encode_char = (fun c -> (match (((Microsoft_FStar_Util.int_of_char c) > 127)) with
| true -> begin
(let bytes = (Microsoft_FStar_Util.string_of_char c)
in (let bytes = (Microsoft_FStar_Util.unicode_of_string bytes)
in (Microsoft_FStar_Bytes.f_encode ocaml_u8_codepoint bytes)))
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
| c when (Microsoft_FStar_Util.is_letter_or_digit c) -> begin
(Microsoft_FStar_Util.string_of_char c)
end
| c when (Microsoft_FStar_Util.is_punctuation c) -> begin
(Microsoft_FStar_Util.string_of_char c)
end
| c when (Microsoft_FStar_Util.is_symbol c) -> begin
(Microsoft_FStar_Util.string_of_char c)
end
| _59_157 -> begin
(ocaml_u8_codepoint (Microsoft_FStar_Util.byte_of_char c))
end)
end))

let string_of_mlconstant = (fun sctt -> (match (sctt) with
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
(let _125_94 = (let _125_93 = (encode_char c)
in (Prims.strcat "\'" _125_93))
in (Prims.strcat _125_94 "\'"))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Byte (c) -> begin
(Prims.strcat (Prims.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int32 (i) -> begin
(Microsoft_FStar_Util.string_of_int32 i)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int64 (i) -> begin
(Prims.strcat (Microsoft_FStar_Util.string_of_int64 i) "L")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(Microsoft_FStar_Util.string_of_float d)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (Microsoft_FStar_Bytes.f_encode ocaml_u8_codepoint bytes)
in (Prims.strcat (Prims.strcat "\"" bytes) "\""))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let chars = (Microsoft_FStar_String.collect encode_char chars)
in (Prims.strcat (Prims.strcat "\"" chars) "\""))
end))

let rec doc_of_mltype' = (fun currentModule outer ty -> (match (ty) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun s -> (match ((Microsoft_FStar_Util.starts_with s "\'_")) with
| true -> begin
(Microsoft_FStar_Util.replace_char s '_' 'u')
end
| false -> begin
s
end))
in (let _125_106 = (All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _125_106)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Microsoft_FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _125_109 = (let _125_108 = (let _125_107 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_107 doc))
in (FSharp_Format.hbox _125_108))
in (FSharp_Format.parens _125_109))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Named (args, name) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _59_199 -> begin
(let args = (Microsoft_FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _125_112 = (let _125_111 = (let _125_110 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_110 args))
in (FSharp_Format.hbox _125_111))
in (FSharp_Format.parens _125_112)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _125_114 = (let _125_113 = (as_standard_type name)
in (Option.get _125_113))
in (Prims.snd _125_114))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _125_118 = (let _125_117 = (let _125_116 = (let _125_115 = (FSharp_Format.text name)
in (_125_115)::[])
in (args)::_125_116)
in (FSharp_Format.reduce1 _125_117))
in (FSharp_Format.hbox _125_118))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun (t1, _59_205, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_123 = (let _125_122 = (let _125_121 = (let _125_120 = (let _125_119 = (FSharp_Format.text " -> ")
in (_125_119)::(d2)::[])
in (d1)::_125_120)
in (FSharp_Format.reduce1 _125_121))
in (FSharp_Format.hbox _125_122))
in (maybe_paren outer t_prio_fun _125_123))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App (t1, t2) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _125_128 = (let _125_127 = (let _125_126 = (let _125_125 = (let _125_124 = (FSharp_Format.text " ")
in (_125_124)::(d1)::[])
in (d2)::_125_125)
in (FSharp_Format.reduce1 _125_126))
in (FSharp_Format.hbox _125_127))
in (maybe_paren outer t_prio_fun _125_128))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun currentModule outer ty -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun currentModule outer e -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce (e, t, t') -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_153 = (let _125_152 = (let _125_151 = (FSharp_Format.text "Obj.magic ")
in (_125_151)::(doc)::[])
in (FSharp_Format.reduce _125_152))
in (FSharp_Format.parens _125_153)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Microsoft_FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Microsoft_FStar_List.map (fun d -> (let _125_157 = (let _125_156 = (let _125_155 = (FSharp_Format.text ";")
in (_125_155)::(FSharp_Format.hardline)::[])
in (d)::_125_156)
in (FSharp_Format.reduce _125_157))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _125_158 = (string_of_mlconstant c)
in (FSharp_Format.text _125_158))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var (x, _59_239) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _125_159 = (ptsym currentModule path)
in (FSharp_Format.text _125_159))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record (path, fields) -> begin
(let for1 = (fun _59_251 -> (match (_59_251) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_166 = (let _125_165 = (let _125_162 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_162))
in (let _125_164 = (let _125_163 = (FSharp_Format.text "=")
in (_125_163)::(doc)::[])
in (_125_165)::_125_164))
in (FSharp_Format.reduce1 _125_166)))
end))
in (let _125_169 = (let _125_168 = (FSharp_Format.text "; ")
in (let _125_167 = (Microsoft_FStar_List.map for1 fields)
in (FSharp_Format.combine _125_168 _125_167)))
in (FSharp_Format.cbrackets _125_169)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_171 = (let _125_170 = (as_standard_constructor ctor)
in (Option.get _125_170))
in (Prims.snd _125_171))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor (ctor, args) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_173 = (let _125_172 = (as_standard_constructor ctor)
in (Option.get _125_172))
in (Prims.snd _125_173))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Microsoft_FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _125_177 = (let _125_176 = (FSharp_Format.parens x)
in (let _125_175 = (let _125_174 = (FSharp_Format.text "::")
in (_125_174)::(xs)::[])
in (_125_176)::_125_175))
in (FSharp_Format.reduce _125_177))
end
| (_59_270, _59_272) -> begin
(let _125_183 = (let _125_182 = (FSharp_Format.text name)
in (let _125_181 = (let _125_180 = (let _125_179 = (let _125_178 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_178 args))
in (FSharp_Format.parens _125_179))
in (_125_180)::[])
in (_125_182)::_125_181))
in (FSharp_Format.reduce1 _125_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Microsoft_FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _125_185 = (let _125_184 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_184 docs))
in (FSharp_Format.parens _125_185))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let ((rec_, lets), body) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _125_191 = (let _125_190 = (let _125_189 = (let _125_188 = (let _125_187 = (let _125_186 = (FSharp_Format.text "in")
in (_125_186)::(body)::[])
in (FSharp_Format.reduce1 _125_187))
in (_125_188)::[])
in (doc)::_125_189)
in (FSharp_Format.combine FSharp_Format.hardline _125_190))
in (FSharp_Format.parens _125_191))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_App (e, args) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::e2::[]) when ((is_bin_op p) && (unitVal = Microsoft_FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (Microsoft_FStar_Extraction_ML_Syntax.MLE_App (Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (p), unitVal::[]), e1::[]) when ((is_uni_op p) && (unitVal = Microsoft_FStar_Extraction_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _59_322 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Microsoft_FStar_List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _125_192 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _125_192))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj (e, f) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _125_198 = (let _125_197 = (let _125_196 = (FSharp_Format.text ".")
in (let _125_195 = (let _125_194 = (let _125_193 = (ptsym currentModule f)
in (FSharp_Format.text _125_193))
in (_125_194)::[])
in (_125_196)::_125_195))
in (e)::_125_197)
in (FSharp_Format.reduce _125_198))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun (ids, body) -> begin
(let ids = (Microsoft_FStar_List.map (fun _59_340 -> (match (_59_340) with
| ((x, _59_337), xt) -> begin
(let _125_205 = (let _125_204 = (FSharp_Format.text "(")
in (let _125_203 = (let _125_202 = (FSharp_Format.text x)
in (let _125_201 = (let _125_200 = (FSharp_Format.text ")")
in (_125_200)::[])
in (_125_202)::_125_201))
in (_125_204)::_125_203))
in (FSharp_Format.reduce1 _125_205))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _125_211 = (let _125_210 = (FSharp_Format.text "fun")
in (let _125_209 = (let _125_208 = (FSharp_Format.reduce1 ids)
in (let _125_207 = (let _125_206 = (FSharp_Format.text "->")
in (_125_206)::(body)::[])
in (_125_208)::_125_207))
in (_125_210)::_125_209))
in (FSharp_Format.reduce1 _125_211))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If (cond, e1, None) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_224 = (let _125_223 = (let _125_218 = (let _125_217 = (FSharp_Format.text "if")
in (let _125_216 = (let _125_215 = (let _125_214 = (FSharp_Format.text "then")
in (let _125_213 = (let _125_212 = (FSharp_Format.text "begin")
in (_125_212)::[])
in (_125_214)::_125_213))
in (cond)::_125_215)
in (_125_217)::_125_216))
in (FSharp_Format.reduce1 _125_218))
in (let _125_222 = (let _125_221 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_220 = (let _125_219 = (FSharp_Format.text "end")
in (_125_219)::[])
in (_125_221)::_125_220))
in (_125_223)::_125_222))
in (FSharp_Format.combine FSharp_Format.hardline _125_224))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If (cond, e1, Some (e2)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _125_247 = (let _125_246 = (let _125_231 = (let _125_230 = (FSharp_Format.text "if")
in (let _125_229 = (let _125_228 = (let _125_227 = (FSharp_Format.text "then")
in (let _125_226 = (let _125_225 = (FSharp_Format.text "begin")
in (_125_225)::[])
in (_125_227)::_125_226))
in (cond)::_125_228)
in (_125_230)::_125_229))
in (FSharp_Format.reduce1 _125_231))
in (let _125_245 = (let _125_244 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _125_243 = (let _125_242 = (let _125_237 = (let _125_236 = (FSharp_Format.text "end")
in (let _125_235 = (let _125_234 = (FSharp_Format.text "else")
in (let _125_233 = (let _125_232 = (FSharp_Format.text "begin")
in (_125_232)::[])
in (_125_234)::_125_233))
in (_125_236)::_125_235))
in (FSharp_Format.reduce1 _125_237))
in (let _125_241 = (let _125_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _125_239 = (let _125_238 = (FSharp_Format.text "end")
in (_125_238)::[])
in (_125_240)::_125_239))
in (_125_242)::_125_241))
in (_125_244)::_125_243))
in (_125_246)::_125_245))
in (FSharp_Format.combine FSharp_Format.hardline _125_247))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match (cond, pats) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Microsoft_FStar_List.map (doc_of_branch currentModule) pats)
in (let doc = (let _125_254 = (let _125_253 = (let _125_252 = (FSharp_Format.text "match")
in (let _125_251 = (let _125_250 = (FSharp_Format.parens cond)
in (let _125_249 = (let _125_248 = (FSharp_Format.text "with")
in (_125_248)::[])
in (_125_250)::_125_249))
in (_125_252)::_125_251))
in (FSharp_Format.reduce1 _125_253))
in (_125_254)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise (exn, []) -> begin
(let _125_259 = (let _125_258 = (FSharp_Format.text "raise")
in (let _125_257 = (let _125_256 = (let _125_255 = (ptctor currentModule exn)
in (FSharp_Format.text _125_255))
in (_125_256)::[])
in (_125_258)::_125_257))
in (FSharp_Format.reduce1 _125_259))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise (exn, args) -> begin
(let args = (Microsoft_FStar_List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _125_268 = (let _125_267 = (FSharp_Format.text "raise")
in (let _125_266 = (let _125_265 = (let _125_260 = (ptctor currentModule exn)
in (FSharp_Format.text _125_260))
in (let _125_264 = (let _125_263 = (let _125_262 = (let _125_261 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_261 args))
in (FSharp_Format.parens _125_262))
in (_125_263)::[])
in (_125_265)::_125_264))
in (_125_267)::_125_266))
in (FSharp_Format.reduce1 _125_268)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try (e, pats) -> begin
(let _125_285 = (let _125_284 = (let _125_272 = (let _125_271 = (FSharp_Format.text "try")
in (let _125_270 = (let _125_269 = (FSharp_Format.text "begin")
in (_125_269)::[])
in (_125_271)::_125_270))
in (FSharp_Format.reduce1 _125_272))
in (let _125_283 = (let _125_282 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_281 = (let _125_280 = (let _125_276 = (let _125_275 = (FSharp_Format.text "end")
in (let _125_274 = (let _125_273 = (FSharp_Format.text "with")
in (_125_273)::[])
in (_125_275)::_125_274))
in (FSharp_Format.reduce1 _125_276))
in (let _125_279 = (let _125_278 = (let _125_277 = (Microsoft_FStar_List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _125_277))
in (_125_278)::[])
in (_125_280)::_125_279))
in (_125_282)::_125_281))
in (_125_284)::_125_283))
in (FSharp_Format.combine FSharp_Format.hardline _125_285))
end))
and doc_of_binop = (fun currentModule p e1 e2 -> (let _59_388 = (let _125_290 = (as_bin_op p)
in (Option.get _125_290))
in (match (_59_388) with
| (_59_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _125_293 = (let _125_292 = (let _125_291 = (FSharp_Format.text txt)
in (_125_291)::(e2)::[])
in (e1)::_125_292)
in (FSharp_Format.reduce1 _125_293))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun currentModule p e1 -> (let _59_398 = (let _125_297 = (as_uni_op p)
in (Option.get _125_297))
in (match (_59_398) with
| (_59_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _125_301 = (let _125_300 = (FSharp_Format.text txt)
in (let _125_299 = (let _125_298 = (FSharp_Format.parens e1)
in (_125_298)::[])
in (_125_300)::_125_299))
in (FSharp_Format.reduce1 _125_301))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun currentModule pattern -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _125_304 = (string_of_mlconstant c)
in (FSharp_Format.text _125_304))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record (path, fields) -> begin
(let for1 = (fun _59_415 -> (match (_59_415) with
| (name, p) -> begin
(let _125_313 = (let _125_312 = (let _125_307 = (ptsym currentModule (path, name))
in (FSharp_Format.text _125_307))
in (let _125_311 = (let _125_310 = (FSharp_Format.text "=")
in (let _125_309 = (let _125_308 = (doc_of_pattern currentModule p)
in (_125_308)::[])
in (_125_310)::_125_309))
in (_125_312)::_125_311))
in (FSharp_Format.reduce1 _125_313))
end))
in (let _125_316 = (let _125_315 = (FSharp_Format.text "; ")
in (let _125_314 = (Microsoft_FStar_List.map for1 fields)
in (FSharp_Format.combine _125_315 _125_314)))
in (FSharp_Format.cbrackets _125_316)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (ctor, []) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_318 = (let _125_317 = (as_standard_constructor ctor)
in (Option.get _125_317))
in (Prims.snd _125_318))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor (ctor, ps) -> begin
(let ps = (Microsoft_FStar_List.map (doc_of_pattern currentModule) ps)
in (let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _125_320 = (let _125_319 = (as_standard_constructor ctor)
in (Option.get _125_319))
in (Prims.snd _125_320))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _125_323 = (let _125_322 = (let _125_321 = (FSharp_Format.text "::")
in (_125_321)::(xs)::[])
in (x)::_125_322)
in (FSharp_Format.reduce _125_323))
end
| (_59_433, _59_435) -> begin
(let _125_329 = (let _125_328 = (FSharp_Format.text name)
in (let _125_327 = (let _125_326 = (let _125_325 = (let _125_324 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_324 ps))
in (FSharp_Format.parens _125_325))
in (_125_326)::[])
in (_125_328)::_125_327))
in (FSharp_Format.reduce1 _125_329))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Microsoft_FStar_List.map (doc_of_pattern currentModule) ps)
in (let _125_331 = (let _125_330 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_330 ps))
in (FSharp_Format.parens _125_331)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Microsoft_FStar_List.map (doc_of_pattern currentModule) ps)
in (let ps = (Microsoft_FStar_List.map FSharp_Format.parens ps)
in (let _125_332 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _125_332 ps))))
end))
and doc_of_branch = (fun currentModule _59_449 -> (match (_59_449) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _125_338 = (let _125_337 = (FSharp_Format.text "|")
in (let _125_336 = (let _125_335 = (doc_of_pattern currentModule p)
in (_125_335)::[])
in (_125_337)::_125_336))
in (FSharp_Format.reduce1 _125_338))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _125_344 = (let _125_343 = (FSharp_Format.text "|")
in (let _125_342 = (let _125_341 = (doc_of_pattern currentModule p)
in (let _125_340 = (let _125_339 = (FSharp_Format.text "when")
in (_125_339)::(c)::[])
in (_125_341)::_125_340))
in (_125_343)::_125_342))
in (FSharp_Format.reduce1 _125_344)))
end)
in (let _125_355 = (let _125_354 = (let _125_349 = (let _125_348 = (let _125_347 = (FSharp_Format.text "->")
in (let _125_346 = (let _125_345 = (FSharp_Format.text "begin")
in (_125_345)::[])
in (_125_347)::_125_346))
in (case)::_125_348)
in (FSharp_Format.reduce1 _125_349))
in (let _125_353 = (let _125_352 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _125_351 = (let _125_350 = (FSharp_Format.text "end")
in (_125_350)::[])
in (_125_352)::_125_351))
in (_125_354)::_125_353))
in (FSharp_Format.combine FSharp_Format.hardline _125_355)))
end))
and doc_of_lets = (fun currentModule _59_458 -> (match (_59_458) with
| (rec_, lets) -> begin
(let for1 = (fun _59_465 -> (match (_59_465) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _59_462; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Microsoft_FStar_List.map (fun _59_471 -> (match (_59_471) with
| (x, _59_470) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _125_366 = (let _125_365 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _125_364 = (let _125_363 = (FSharp_Format.reduce1 ids)
in (let _125_362 = (let _125_361 = (FSharp_Format.text "=")
in (_125_361)::(e)::[])
in (_125_363)::_125_362))
in (_125_365)::_125_364))
in (FSharp_Format.reduce1 _125_366)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _125_370 = (let _125_369 = (FSharp_Format.text "let")
in (let _125_368 = (let _125_367 = (FSharp_Format.text "rec")
in (_125_367)::[])
in (_125_369)::_125_368))
in (FSharp_Format.reduce1 _125_370))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Microsoft_FStar_List.map for1 lets)
in (let lets = (Microsoft_FStar_List.mapi (fun i doc -> (let _125_374 = (let _125_373 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_125_373)::(doc)::[])
in (FSharp_Format.reduce1 _125_374))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun currentModule decls -> (let for1 = (fun _59_484 -> (match (_59_484) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
end
| _59_489 -> begin
(let doc = (Microsoft_FStar_List.map (fun x -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _125_383 = (let _125_382 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _125_382 doc))
in (FSharp_Format.parens _125_383)))
end)
in (let forbody = (fun body -> (match (body) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun _59_502 -> (match (_59_502) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_390 = (let _125_389 = (let _125_388 = (FSharp_Format.text ":")
in (_125_388)::(ty)::[])
in (name)::_125_389)
in (FSharp_Format.reduce1 _125_390))))
end))
in (let _125_393 = (let _125_392 = (FSharp_Format.text "; ")
in (let _125_391 = (Microsoft_FStar_List.map forfield fields)
in (FSharp_Format.combine _125_392 _125_391)))
in (FSharp_Format.cbrackets _125_393)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun _59_510 -> (match (_59_510) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _59_513 -> begin
(let tys = (Microsoft_FStar_List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _125_396 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_396 tys))
in (let _125_400 = (let _125_399 = (FSharp_Format.text name)
in (let _125_398 = (let _125_397 = (FSharp_Format.text "of")
in (_125_397)::(tys)::[])
in (_125_399)::_125_398))
in (FSharp_Format.reduce1 _125_400))))
end)
end))
in (let ctors = (Microsoft_FStar_List.map forctor ctors)
in (let ctors = (Microsoft_FStar_List.map (fun d -> (let _125_403 = (let _125_402 = (FSharp_Format.text "|")
in (_125_402)::(d)::[])
in (FSharp_Format.reduce1 _125_403))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _125_407 = (let _125_406 = (let _125_405 = (let _125_404 = (ptsym currentModule ([], x))
in (FSharp_Format.text _125_404))
in (_125_405)::[])
in (tparams)::_125_406)
in (FSharp_Format.reduce1 _125_407))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _125_412 = (let _125_411 = (let _125_410 = (let _125_409 = (let _125_408 = (FSharp_Format.text "=")
in (_125_408)::[])
in (doc)::_125_409)
in (FSharp_Format.reduce1 _125_410))
in (_125_411)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _125_412)))
end))))
end))
in (let doc = (Microsoft_FStar_List.map for1 decls)
in (let doc = (match (((Microsoft_FStar_List.length doc) > 0)) with
| true -> begin
(let _125_417 = (let _125_416 = (FSharp_Format.text "type")
in (let _125_415 = (let _125_414 = (let _125_413 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _125_413 doc))
in (_125_414)::[])
in (_125_416)::_125_415))
in (FSharp_Format.reduce1 _125_417))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun currentModule s -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod (x, subsig) -> begin
(let _125_437 = (let _125_436 = (let _125_429 = (let _125_428 = (FSharp_Format.text "module")
in (let _125_427 = (let _125_426 = (FSharp_Format.text x)
in (let _125_425 = (let _125_424 = (FSharp_Format.text "=")
in (_125_424)::[])
in (_125_426)::_125_425))
in (_125_428)::_125_427))
in (FSharp_Format.reduce1 _125_429))
in (let _125_435 = (let _125_434 = (doc_of_sig currentModule subsig)
in (let _125_433 = (let _125_432 = (let _125_431 = (let _125_430 = (FSharp_Format.text "end")
in (_125_430)::[])
in (FSharp_Format.reduce1 _125_431))
in (_125_432)::[])
in (_125_434)::_125_433))
in (_125_436)::_125_435))
in (FSharp_Format.combine FSharp_Format.hardline _125_437))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn (x, []) -> begin
(let _125_441 = (let _125_440 = (FSharp_Format.text "exception")
in (let _125_439 = (let _125_438 = (FSharp_Format.text x)
in (_125_438)::[])
in (_125_440)::_125_439))
in (FSharp_Format.reduce1 _125_441))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn (x, args) -> begin
(let args = (Microsoft_FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_443 = (let _125_442 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_442 args))
in (FSharp_Format.parens _125_443))
in (let _125_449 = (let _125_448 = (FSharp_Format.text "exception")
in (let _125_447 = (let _125_446 = (FSharp_Format.text x)
in (let _125_445 = (let _125_444 = (FSharp_Format.text "of")
in (_125_444)::(args)::[])
in (_125_446)::_125_445))
in (_125_448)::_125_447))
in (FSharp_Format.reduce1 _125_449))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val (x, (_59_544, ty)) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _125_455 = (let _125_454 = (FSharp_Format.text "val")
in (let _125_453 = (let _125_452 = (FSharp_Format.text x)
in (let _125_451 = (let _125_450 = (FSharp_Format.text ": ")
in (_125_450)::(ty)::[])
in (_125_452)::_125_451))
in (_125_454)::_125_453))
in (FSharp_Format.reduce1 _125_455)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun currentModule s -> (let docs = (Microsoft_FStar_List.map (doc_of_sig1 currentModule) s)
in (let docs = (Microsoft_FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun currentModule m -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn (x, []) -> begin
(let _125_466 = (let _125_465 = (FSharp_Format.text "exception")
in (let _125_464 = (let _125_463 = (FSharp_Format.text x)
in (_125_463)::[])
in (_125_465)::_125_464))
in (FSharp_Format.reduce1 _125_466))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn (x, args) -> begin
(let args = (Microsoft_FStar_List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _125_468 = (let _125_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _125_467 args))
in (FSharp_Format.parens _125_468))
in (let _125_474 = (let _125_473 = (FSharp_Format.text "exception")
in (let _125_472 = (let _125_471 = (FSharp_Format.text x)
in (let _125_470 = (let _125_469 = (FSharp_Format.text "of")
in (_125_469)::(args)::[])
in (_125_471)::_125_470))
in (_125_473)::_125_472))
in (FSharp_Format.reduce1 _125_474))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let (rec_, lets) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _125_482 = (let _125_481 = (FSharp_Format.text "let")
in (let _125_480 = (let _125_479 = (FSharp_Format.text "_")
in (let _125_478 = (let _125_477 = (FSharp_Format.text "=")
in (let _125_476 = (let _125_475 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_125_475)::[])
in (_125_477)::_125_476))
in (_125_479)::_125_478))
in (_125_481)::_125_480))
in (FSharp_Format.reduce1 _125_482))
end))

let doc_of_mod = (fun currentModule m -> (let docs = (Microsoft_FStar_List.map (doc_of_mod1 currentModule) m)
in (let docs = (Microsoft_FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun _59_583 -> (match (_59_583) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun _59_590 -> (match (_59_590) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _125_501 = (let _125_500 = (FSharp_Format.text "module")
in (let _125_499 = (let _125_498 = (FSharp_Format.text x)
in (let _125_497 = (let _125_496 = (FSharp_Format.text ":")
in (let _125_495 = (let _125_494 = (FSharp_Format.text "sig")
in (_125_494)::[])
in (_125_496)::_125_495))
in (_125_498)::_125_497))
in (_125_500)::_125_499))
in (FSharp_Format.reduce1 _125_501))
in (let tail = (let _125_503 = (let _125_502 = (FSharp_Format.text "end")
in (_125_502)::[])
in (FSharp_Format.reduce1 _125_503))
in (let doc = (Option.map (fun _59_596 -> (match (_59_596) with
| (s, _59_595) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Microsoft_FStar_List.map for1_sig sub)
in (let sub = (Microsoft_FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _125_513 = (let _125_512 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_511 = (let _125_510 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_509 = (let _125_508 = (FSharp_Format.reduce sub)
in (let _125_507 = (let _125_506 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_506)::[])
in (_125_508)::_125_507))
in (_125_510)::_125_509))
in (_125_512)::_125_511))
in (FSharp_Format.reduce _125_513)))))))
end))
and for1_mod = (fun istop _59_609 -> (match (_59_609) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_610 = (Microsoft_FStar_Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _125_523 = (match ((not (istop))) with
| true -> begin
(let _125_522 = (FSharp_Format.text "module")
in (let _125_521 = (let _125_520 = (FSharp_Format.text x)
in (let _125_519 = (let _125_518 = (FSharp_Format.text "=")
in (let _125_517 = (let _125_516 = (FSharp_Format.text "struct")
in (_125_516)::[])
in (_125_518)::_125_517))
in (_125_520)::_125_519))
in (_125_522)::_125_521))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _125_523))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _125_525 = (let _125_524 = (FSharp_Format.text "end")
in (_125_524)::[])
in (FSharp_Format.reduce1 _125_525))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Option.map (fun _59_617 -> (match (_59_617) with
| (_59_615, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Microsoft_FStar_List.map (for1_mod false) sub)
in (let sub = (Microsoft_FStar_List.map (fun x -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _125_535 = (let _125_534 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _125_533 = (let _125_532 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _125_531 = (let _125_530 = (FSharp_Format.reduce sub)
in (let _125_529 = (let _125_528 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_125_528)::[])
in (_125_530)::_125_529))
in (_125_532)::_125_531))
in (_125_534)::_125_533))
in (FSharp_Format.reduce _125_535))))))))
end))
in (let docs = (Microsoft_FStar_List.map (fun _59_628 -> (match (_59_628) with
| (x, s, m) -> begin
(let _125_537 = (for1_mod true (x, s, m))
in (x, _125_537))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun mllib -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun env e -> (let doc = (let _125_544 = (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule)
in (doc_of_expr _125_544 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun env e -> (let doc = (let _125_549 = (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule)
in (doc_of_mltype _125_549 (min_op_prec, NonAssoc) e))
in (FSharp_Format.pretty 0 doc)))






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
| Infix (_59_3) -> begin
_59_3
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

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("All")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Map")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let rec in_ns = (fun ( x ) -> (match (x) with
| ([], _59_8) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_59_18, _59_20) -> begin
false
end))

let path_of_ns = (fun ( currentModule ) ( ns ) -> (let outsupport = (fun ( ns ) -> (let ns' = (Microsoft_FStar_Extraction_ML_Util.flatten_ns ns)
in (match ((ns' = currentModule)) with
| true -> begin
[]
end
| false -> begin
(ns')::[]
end)))
in (let chkin = (fun ( sns ) -> (match ((in_ns (sns, ns))) with
| true -> begin
Some (sns)
end
| false -> begin
None
end))
in (match ((Support.List.tryPick chkin outmod)) with
| None -> begin
(match ((let _123_32 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _123_32))) with
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

let mlpath_of_mlpath = (fun ( currentModule ) ( x ) -> (match ((Microsoft_FStar_Extraction_ML_Syntax.string_of_mlpath x)) with
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
(let _123_37 = (path_of_ns currentModule ns)
in (_123_37, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _123_40 = (Support.String.get s 0)
in (Support.Char.lowercase _123_40)) <> (Support.String.get s 0))) with
| true -> begin
(Support.String.strcat "l__" s)
end
| false -> begin
s
end))

let ptsym = (fun ( currentModule ) ( mlp ) -> (match ((Support.List.isEmpty (Support.Prims.fst mlp))) with
| true -> begin
(ptsym_of_symbol (Support.Prims.snd mlp))
end
| false -> begin
(let _59_53 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_53) with
| (p, s) -> begin
(let _123_47 = (let _123_46 = (let _123_45 = (ptsym_of_symbol s)
in (_123_45)::[])
in (Support.List.append p _123_46))
in (Support.String.concat "." _123_47))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_58 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_58) with
| (p, s) -> begin
(let s = (match (((let _123_52 = (Support.String.get s 0)
in (Support.Char.uppercase _123_52)) <> (Support.String.get s 0))) with
| true -> begin
(Support.String.strcat "U__" s)
end
| false -> begin
s
end)
in (Support.String.concat "." (Support.List.append p ((s)::[]))))
end)))

let infix_prim_ops = (("op_Addition", e_bin_prio_op1, "+"))::(("op_Subtraction", e_bin_prio_op1, "-"))::(("op_Multiply", e_bin_prio_op1, "*"))::(("op_Division", e_bin_prio_op1, "/"))::(("op_Equality", e_bin_prio_eq, "="))::(("op_ColonEquals", e_bin_prio_eq, ":="))::(("op_disEquality", e_bin_prio_eq, "<>"))::(("op_AmpAmp", e_bin_prio_and, "&&"))::(("op_BarBar", e_bin_prio_or, "||"))::(("op_LessThanOrEqual", e_bin_prio_order, "<="))::(("op_GreaterThanOrEqual", e_bin_prio_order, ">="))::(("op_LessThan", e_bin_prio_order, "<"))::(("op_GreaterThan", e_bin_prio_order, ">"))::(("op_Modulus", e_bin_prio_order, "mod"))::[]

let prim_uni_ops = (("op_Negation", "not"))::(("op_Minus", "-"))::(("op_Bang", "Support.ST.read"))::(("exit", "exit"))::(("failwith", "failwith"))::(("raise", "raise"))::[]

let prim_types = (("char", "char"))::(("bool", "bool"))::(("string", "string"))::(("unit", "unit"))::(("ref", "ref"))::(("array", "array"))::(("option", "option"))::(("list", "list"))::(("int", "int"))::(("int64", "Int64.t"))::[]

let prim_constructors = (("Some", "Some"))::(("None", "None"))::(("Nil", "[]"))::(("Cons", "::"))::[]

let is_prims_ns = (fun ( ns ) -> (ns = ("Prims")::[]))

let as_bin_op = (fun ( _59_63 ) -> (match (_59_63) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_69 ) -> (match (_59_69) with
| (y, _59_66, _59_68) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _59_73 ) -> (match (_59_73) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_77 ) -> (match (_59_77) with
| (y, _59_76) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _59_81 ) -> (match (_59_81) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_85 ) -> (match (_59_85) with
| (y, _59_84) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _59_89 ) -> (match (_59_89) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_93 ) -> (match (_59_93) with
| (y, _59_92) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _59_97 ) ( inner ) ( doc ) -> (match (_59_97) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _59_106 = _inner
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
| _59_157 -> begin
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
(let _123_94 = (let _123_93 = (encode_char c)
in (Support.String.strcat "\'" _123_93))
in (Support.String.strcat _123_94 "\'"))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Byte (c) -> begin
(Support.String.strcat (Support.String.strcat "\'" (ocaml_u8_codepoint c)) "\'")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int32 (i) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 i)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Int64 (i) -> begin
(Support.String.strcat (Support.Microsoft.FStar.Util.string_of_int64 i) "L")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Float (d) -> begin
(Support.Microsoft.FStar.Util.string_of_float d)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_Bytes (bytes) -> begin
(let bytes = (Support.Microsoft.FStar.Bytes.f_encode ocaml_u8_codepoint bytes)
in (Support.String.strcat (Support.String.strcat "\"" bytes) "\""))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLC_String (chars) -> begin
(let chars = (Support.String.collect encode_char chars)
in (Support.String.strcat (Support.String.strcat "\"" chars) "\""))
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
in (let _123_106 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _123_106)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _123_109 = (let _123_108 = (let _123_107 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _123_107 doc))
in (FSharp_Format.hbox _123_108))
in (FSharp_Format.parens _123_109))
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
| _59_199 -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _123_112 = (let _123_111 = (let _123_110 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_110 args))
in (FSharp_Format.hbox _123_111))
in (FSharp_Format.parens _123_112)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _123_114 = (let _123_113 = (as_standard_type name)
in (Support.Option.get _123_113))
in (Support.Prims.snd _123_114))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _123_118 = (let _123_117 = (let _123_116 = (let _123_115 = (FSharp_Format.text name)
in (_123_115)::[])
in (args)::_123_116)
in (FSharp_Format.reduce1 _123_117))
in (FSharp_Format.hbox _123_118))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _59_205, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _123_123 = (let _123_122 = (let _123_121 = (let _123_120 = (let _123_119 = (FSharp_Format.text " -> ")
in (_123_119)::(d2)::[])
in (d1)::_123_120)
in (FSharp_Format.reduce1 _123_121))
in (FSharp_Format.hbox _123_122))
in (maybe_paren outer t_prio_fun _123_123))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _123_128 = (let _123_127 = (let _123_126 = (let _123_125 = (let _123_124 = (FSharp_Format.text " ")
in (_123_124)::(d1)::[])
in (d2)::_123_125)
in (FSharp_Format.reduce1 _123_126))
in (FSharp_Format.hbox _123_127))
in (maybe_paren outer t_prio_fun _123_128))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _123_153 = (let _123_152 = (let _123_151 = (FSharp_Format.text "Obj.magic ")
in (_123_151)::(doc)::[])
in (FSharp_Format.reduce _123_152))
in (FSharp_Format.parens _123_153)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _123_157 = (let _123_156 = (let _123_155 = (FSharp_Format.text ";")
in (_123_155)::(FSharp_Format.hardline)::[])
in (d)::_123_156)
in (FSharp_Format.reduce _123_157))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _123_158 = (string_of_mlconstant c)
in (FSharp_Format.text _123_158))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _59_239)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _123_159 = (ptsym currentModule path)
in (FSharp_Format.text _123_159))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_251 ) -> (match (_59_251) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _123_166 = (let _123_165 = (let _123_162 = (ptsym currentModule (path, name))
in (FSharp_Format.text _123_162))
in (let _123_164 = (let _123_163 = (FSharp_Format.text "=")
in (_123_163)::(doc)::[])
in (_123_165)::_123_164))
in (FSharp_Format.reduce1 _123_166)))
end))
in (let _123_169 = (let _123_168 = (FSharp_Format.text "; ")
in (let _123_167 = (Support.List.map for1 fields)
in (FSharp_Format.combine _123_168 _123_167)))
in (FSharp_Format.cbrackets _123_169)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _123_171 = (let _123_170 = (as_standard_constructor ctor)
in (Support.Option.get _123_170))
in (Support.Prims.snd _123_171))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _123_173 = (let _123_172 = (as_standard_constructor ctor)
in (Support.Option.get _123_172))
in (Support.Prims.snd _123_173))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _123_177 = (let _123_176 = (FSharp_Format.parens x)
in (let _123_175 = (let _123_174 = (FSharp_Format.text "::")
in (_123_174)::(xs)::[])
in (_123_176)::_123_175))
in (FSharp_Format.reduce _123_177))
end
| (_59_270, _59_272) -> begin
(let _123_183 = (let _123_182 = (FSharp_Format.text name)
in (let _123_181 = (let _123_180 = (let _123_179 = (let _123_178 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_178 args))
in (FSharp_Format.parens _123_179))
in (_123_180)::[])
in (_123_182)::_123_181))
in (FSharp_Format.reduce1 _123_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _123_185 = (let _123_184 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_184 docs))
in (FSharp_Format.parens _123_185))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _123_191 = (let _123_190 = (let _123_189 = (let _123_188 = (let _123_187 = (let _123_186 = (FSharp_Format.text "in")
in (_123_186)::(body)::[])
in (FSharp_Format.reduce1 _123_187))
in (_123_188)::[])
in (doc)::_123_189)
in (FSharp_Format.combine FSharp_Format.hardline _123_190))
in (FSharp_Format.parens _123_191))))
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
| _59_322 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _123_192 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _123_192))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _123_198 = (let _123_197 = (let _123_196 = (FSharp_Format.text ".")
in (let _123_195 = (let _123_194 = (let _123_193 = (ptsym currentModule f)
in (FSharp_Format.text _123_193))
in (_123_194)::[])
in (_123_196)::_123_195))
in (e)::_123_197)
in (FSharp_Format.reduce _123_198))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_340 ) -> (match (_59_340) with
| ((x, _59_337), xt) -> begin
(let _123_205 = (let _123_204 = (FSharp_Format.text "(")
in (let _123_203 = (let _123_202 = (FSharp_Format.text x)
in (let _123_201 = (let _123_200 = (FSharp_Format.text ")")
in (_123_200)::[])
in (_123_202)::_123_201))
in (_123_204)::_123_203))
in (FSharp_Format.reduce1 _123_205))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _123_211 = (let _123_210 = (FSharp_Format.text "fun")
in (let _123_209 = (let _123_208 = (FSharp_Format.reduce1 ids)
in (let _123_207 = (let _123_206 = (FSharp_Format.text "->")
in (_123_206)::(body)::[])
in (_123_208)::_123_207))
in (_123_210)::_123_209))
in (FSharp_Format.reduce1 _123_211))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _123_224 = (let _123_223 = (let _123_218 = (let _123_217 = (FSharp_Format.text "if")
in (let _123_216 = (let _123_215 = (let _123_214 = (FSharp_Format.text "then")
in (let _123_213 = (let _123_212 = (FSharp_Format.text "begin")
in (_123_212)::[])
in (_123_214)::_123_213))
in (cond)::_123_215)
in (_123_217)::_123_216))
in (FSharp_Format.reduce1 _123_218))
in (let _123_222 = (let _123_221 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _123_220 = (let _123_219 = (FSharp_Format.text "end")
in (_123_219)::[])
in (_123_221)::_123_220))
in (_123_223)::_123_222))
in (FSharp_Format.combine FSharp_Format.hardline _123_224))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _123_247 = (let _123_246 = (let _123_231 = (let _123_230 = (FSharp_Format.text "if")
in (let _123_229 = (let _123_228 = (let _123_227 = (FSharp_Format.text "then")
in (let _123_226 = (let _123_225 = (FSharp_Format.text "begin")
in (_123_225)::[])
in (_123_227)::_123_226))
in (cond)::_123_228)
in (_123_230)::_123_229))
in (FSharp_Format.reduce1 _123_231))
in (let _123_245 = (let _123_244 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _123_243 = (let _123_242 = (let _123_237 = (let _123_236 = (FSharp_Format.text "end")
in (let _123_235 = (let _123_234 = (FSharp_Format.text "else")
in (let _123_233 = (let _123_232 = (FSharp_Format.text "begin")
in (_123_232)::[])
in (_123_234)::_123_233))
in (_123_236)::_123_235))
in (FSharp_Format.reduce1 _123_237))
in (let _123_241 = (let _123_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _123_239 = (let _123_238 = (FSharp_Format.text "end")
in (_123_238)::[])
in (_123_240)::_123_239))
in (_123_242)::_123_241))
in (_123_244)::_123_243))
in (_123_246)::_123_245))
in (FSharp_Format.combine FSharp_Format.hardline _123_247))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _123_254 = (let _123_253 = (let _123_252 = (FSharp_Format.text "match")
in (let _123_251 = (let _123_250 = (FSharp_Format.parens cond)
in (let _123_249 = (let _123_248 = (FSharp_Format.text "with")
in (_123_248)::[])
in (_123_250)::_123_249))
in (_123_252)::_123_251))
in (FSharp_Format.reduce1 _123_253))
in (_123_254)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _123_259 = (let _123_258 = (FSharp_Format.text "raise")
in (let _123_257 = (let _123_256 = (let _123_255 = (ptctor currentModule exn)
in (FSharp_Format.text _123_255))
in (_123_256)::[])
in (_123_258)::_123_257))
in (FSharp_Format.reduce1 _123_259))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _123_268 = (let _123_267 = (FSharp_Format.text "raise")
in (let _123_266 = (let _123_265 = (let _123_260 = (ptctor currentModule exn)
in (FSharp_Format.text _123_260))
in (let _123_264 = (let _123_263 = (let _123_262 = (let _123_261 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_261 args))
in (FSharp_Format.parens _123_262))
in (_123_263)::[])
in (_123_265)::_123_264))
in (_123_267)::_123_266))
in (FSharp_Format.reduce1 _123_268)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _123_285 = (let _123_284 = (let _123_272 = (let _123_271 = (FSharp_Format.text "try")
in (let _123_270 = (let _123_269 = (FSharp_Format.text "begin")
in (_123_269)::[])
in (_123_271)::_123_270))
in (FSharp_Format.reduce1 _123_272))
in (let _123_283 = (let _123_282 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _123_281 = (let _123_280 = (let _123_276 = (let _123_275 = (FSharp_Format.text "end")
in (let _123_274 = (let _123_273 = (FSharp_Format.text "with")
in (_123_273)::[])
in (_123_275)::_123_274))
in (FSharp_Format.reduce1 _123_276))
in (let _123_279 = (let _123_278 = (let _123_277 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _123_277))
in (_123_278)::[])
in (_123_280)::_123_279))
in (_123_282)::_123_281))
in (_123_284)::_123_283))
in (FSharp_Format.combine FSharp_Format.hardline _123_285))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_388 = (let _123_290 = (as_bin_op p)
in (Support.Option.get _123_290))
in (match (_59_388) with
| (_59_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _123_293 = (let _123_292 = (let _123_291 = (FSharp_Format.text txt)
in (_123_291)::(e2)::[])
in (e1)::_123_292)
in (FSharp_Format.reduce1 _123_293))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_398 = (let _123_297 = (as_uni_op p)
in (Support.Option.get _123_297))
in (match (_59_398) with
| (_59_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _123_301 = (let _123_300 = (FSharp_Format.text txt)
in (let _123_299 = (let _123_298 = (FSharp_Format.parens e1)
in (_123_298)::[])
in (_123_300)::_123_299))
in (FSharp_Format.reduce1 _123_301))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _123_304 = (string_of_mlconstant c)
in (FSharp_Format.text _123_304))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_415 ) -> (match (_59_415) with
| (name, p) -> begin
(let _123_313 = (let _123_312 = (let _123_307 = (ptsym currentModule (path, name))
in (FSharp_Format.text _123_307))
in (let _123_311 = (let _123_310 = (FSharp_Format.text "=")
in (let _123_309 = (let _123_308 = (doc_of_pattern currentModule p)
in (_123_308)::[])
in (_123_310)::_123_309))
in (_123_312)::_123_311))
in (FSharp_Format.reduce1 _123_313))
end))
in (let _123_316 = (let _123_315 = (FSharp_Format.text "; ")
in (let _123_314 = (Support.List.map for1 fields)
in (FSharp_Format.combine _123_315 _123_314)))
in (FSharp_Format.cbrackets _123_316)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _123_318 = (let _123_317 = (as_standard_constructor ctor)
in (Support.Option.get _123_317))
in (Support.Prims.snd _123_318))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, ps)) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _123_320 = (let _123_319 = (as_standard_constructor ctor)
in (Support.Option.get _123_319))
in (Support.Prims.snd _123_320))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _123_323 = (let _123_322 = (let _123_321 = (FSharp_Format.text "::")
in (_123_321)::(xs)::[])
in (x)::_123_322)
in (FSharp_Format.reduce _123_323))
end
| (_59_433, _59_435) -> begin
(let _123_329 = (let _123_328 = (FSharp_Format.text name)
in (let _123_327 = (let _123_326 = (let _123_325 = (let _123_324 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_324 ps))
in (FSharp_Format.parens _123_325))
in (_123_326)::[])
in (_123_328)::_123_327))
in (FSharp_Format.reduce1 _123_329))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _123_331 = (let _123_330 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_330 ps))
in (FSharp_Format.parens _123_331)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _123_332 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _123_332 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_449 ) -> (match (_59_449) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _123_338 = (let _123_337 = (FSharp_Format.text "|")
in (let _123_336 = (let _123_335 = (doc_of_pattern currentModule p)
in (_123_335)::[])
in (_123_337)::_123_336))
in (FSharp_Format.reduce1 _123_338))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _123_344 = (let _123_343 = (FSharp_Format.text "|")
in (let _123_342 = (let _123_341 = (doc_of_pattern currentModule p)
in (let _123_340 = (let _123_339 = (FSharp_Format.text "when")
in (_123_339)::(c)::[])
in (_123_341)::_123_340))
in (_123_343)::_123_342))
in (FSharp_Format.reduce1 _123_344)))
end)
in (let _123_355 = (let _123_354 = (let _123_349 = (let _123_348 = (let _123_347 = (FSharp_Format.text "->")
in (let _123_346 = (let _123_345 = (FSharp_Format.text "begin")
in (_123_345)::[])
in (_123_347)::_123_346))
in (case)::_123_348)
in (FSharp_Format.reduce1 _123_349))
in (let _123_353 = (let _123_352 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _123_351 = (let _123_350 = (FSharp_Format.text "end")
in (_123_350)::[])
in (_123_352)::_123_351))
in (_123_354)::_123_353))
in (FSharp_Format.combine FSharp_Format.hardline _123_355)))
end))
and doc_of_lets = (fun ( currentModule ) ( _59_458 ) -> (match (_59_458) with
| (rec_, lets) -> begin
(let for1 = (fun ( _59_465 ) -> (match (_59_465) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _59_462; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _59_471 ) -> (match (_59_471) with
| (x, _59_470) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _123_366 = (let _123_365 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _123_364 = (let _123_363 = (FSharp_Format.reduce1 ids)
in (let _123_362 = (let _123_361 = (FSharp_Format.text "=")
in (_123_361)::(e)::[])
in (_123_363)::_123_362))
in (_123_365)::_123_364))
in (FSharp_Format.reduce1 _123_366)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _123_370 = (let _123_369 = (FSharp_Format.text "let")
in (let _123_368 = (let _123_367 = (FSharp_Format.text "rec")
in (_123_367)::[])
in (_123_369)::_123_368))
in (FSharp_Format.reduce1 _123_370))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _123_374 = (let _123_373 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_123_373)::(doc)::[])
in (FSharp_Format.reduce1 _123_374))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _59_484 ) -> (match (_59_484) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
end
| _59_489 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _123_383 = (let _123_382 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _123_382 doc))
in (FSharp_Format.parens _123_383)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _59_502 ) -> (match (_59_502) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _123_390 = (let _123_389 = (let _123_388 = (FSharp_Format.text ":")
in (_123_388)::(ty)::[])
in (name)::_123_389)
in (FSharp_Format.reduce1 _123_390))))
end))
in (let _123_393 = (let _123_392 = (FSharp_Format.text "; ")
in (let _123_391 = (Support.List.map forfield fields)
in (FSharp_Format.combine _123_392 _123_391)))
in (FSharp_Format.cbrackets _123_393)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _59_510 ) -> (match (_59_510) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _59_513 -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _123_396 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _123_396 tys))
in (let _123_400 = (let _123_399 = (FSharp_Format.text name)
in (let _123_398 = (let _123_397 = (FSharp_Format.text "of")
in (_123_397)::(tys)::[])
in (_123_399)::_123_398))
in (FSharp_Format.reduce1 _123_400))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _123_403 = (let _123_402 = (FSharp_Format.text "|")
in (_123_402)::(d)::[])
in (FSharp_Format.reduce1 _123_403))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _123_407 = (let _123_406 = (let _123_405 = (let _123_404 = (ptsym currentModule ([], x))
in (FSharp_Format.text _123_404))
in (_123_405)::[])
in (tparams)::_123_406)
in (FSharp_Format.reduce1 _123_407))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _123_412 = (let _123_411 = (let _123_410 = (let _123_409 = (let _123_408 = (FSharp_Format.text "=")
in (_123_408)::[])
in (doc)::_123_409)
in (FSharp_Format.reduce1 _123_410))
in (_123_411)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _123_412)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _123_417 = (let _123_416 = (FSharp_Format.text "type")
in (let _123_415 = (let _123_414 = (let _123_413 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _123_413 doc))
in (_123_414)::[])
in (_123_416)::_123_415))
in (FSharp_Format.reduce1 _123_417))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _123_437 = (let _123_436 = (let _123_429 = (let _123_428 = (FSharp_Format.text "module")
in (let _123_427 = (let _123_426 = (FSharp_Format.text x)
in (let _123_425 = (let _123_424 = (FSharp_Format.text "=")
in (_123_424)::[])
in (_123_426)::_123_425))
in (_123_428)::_123_427))
in (FSharp_Format.reduce1 _123_429))
in (let _123_435 = (let _123_434 = (doc_of_sig currentModule subsig)
in (let _123_433 = (let _123_432 = (let _123_431 = (let _123_430 = (FSharp_Format.text "end")
in (_123_430)::[])
in (FSharp_Format.reduce1 _123_431))
in (_123_432)::[])
in (_123_434)::_123_433))
in (_123_436)::_123_435))
in (FSharp_Format.combine FSharp_Format.hardline _123_437))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _123_441 = (let _123_440 = (FSharp_Format.text "exception")
in (let _123_439 = (let _123_438 = (FSharp_Format.text x)
in (_123_438)::[])
in (_123_440)::_123_439))
in (FSharp_Format.reduce1 _123_441))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _123_443 = (let _123_442 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _123_442 args))
in (FSharp_Format.parens _123_443))
in (let _123_449 = (let _123_448 = (FSharp_Format.text "exception")
in (let _123_447 = (let _123_446 = (FSharp_Format.text x)
in (let _123_445 = (let _123_444 = (FSharp_Format.text "of")
in (_123_444)::(args)::[])
in (_123_446)::_123_445))
in (_123_448)::_123_447))
in (FSharp_Format.reduce1 _123_449))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_59_544, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _123_455 = (let _123_454 = (FSharp_Format.text "val")
in (let _123_453 = (let _123_452 = (FSharp_Format.text x)
in (let _123_451 = (let _123_450 = (FSharp_Format.text ": ")
in (_123_450)::(ty)::[])
in (_123_452)::_123_451))
in (_123_454)::_123_453))
in (FSharp_Format.reduce1 _123_455)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _123_466 = (let _123_465 = (FSharp_Format.text "exception")
in (let _123_464 = (let _123_463 = (FSharp_Format.text x)
in (_123_463)::[])
in (_123_465)::_123_464))
in (FSharp_Format.reduce1 _123_466))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _123_468 = (let _123_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _123_467 args))
in (FSharp_Format.parens _123_468))
in (let _123_474 = (let _123_473 = (FSharp_Format.text "exception")
in (let _123_472 = (let _123_471 = (FSharp_Format.text x)
in (let _123_470 = (let _123_469 = (FSharp_Format.text "of")
in (_123_469)::(args)::[])
in (_123_471)::_123_470))
in (_123_473)::_123_472))
in (FSharp_Format.reduce1 _123_474))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _123_482 = (let _123_481 = (FSharp_Format.text "let")
in (let _123_480 = (let _123_479 = (FSharp_Format.text "_")
in (let _123_478 = (let _123_477 = (FSharp_Format.text "=")
in (let _123_476 = (let _123_475 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_123_475)::[])
in (_123_477)::_123_476))
in (_123_479)::_123_478))
in (_123_481)::_123_480))
in (FSharp_Format.reduce1 _123_482))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_583 ) -> (match (_59_583) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_590 ) -> (match (_59_590) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _123_501 = (let _123_500 = (FSharp_Format.text "module")
in (let _123_499 = (let _123_498 = (FSharp_Format.text x)
in (let _123_497 = (let _123_496 = (FSharp_Format.text ":")
in (let _123_495 = (let _123_494 = (FSharp_Format.text "sig")
in (_123_494)::[])
in (_123_496)::_123_495))
in (_123_498)::_123_497))
in (_123_500)::_123_499))
in (FSharp_Format.reduce1 _123_501))
in (let tail = (let _123_503 = (let _123_502 = (FSharp_Format.text "end")
in (_123_502)::[])
in (FSharp_Format.reduce1 _123_503))
in (let doc = (Support.Option.map (fun ( _59_596 ) -> (match (_59_596) with
| (s, _59_595) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _123_513 = (let _123_512 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _123_511 = (let _123_510 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _123_509 = (let _123_508 = (FSharp_Format.reduce sub)
in (let _123_507 = (let _123_506 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_123_506)::[])
in (_123_508)::_123_507))
in (_123_510)::_123_509))
in (_123_512)::_123_511))
in (FSharp_Format.reduce _123_513)))))))
end))
and for1_mod = (fun ( istop ) ( _59_609 ) -> (match (_59_609) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_610 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _123_523 = (match ((not (istop))) with
| true -> begin
(let _123_522 = (FSharp_Format.text "module")
in (let _123_521 = (let _123_520 = (FSharp_Format.text x)
in (let _123_519 = (let _123_518 = (FSharp_Format.text "=")
in (let _123_517 = (let _123_516 = (FSharp_Format.text "struct")
in (_123_516)::[])
in (_123_518)::_123_517))
in (_123_520)::_123_519))
in (_123_522)::_123_521))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _123_523))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _123_525 = (let _123_524 = (FSharp_Format.text "end")
in (_123_524)::[])
in (FSharp_Format.reduce1 _123_525))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _59_617 ) -> (match (_59_617) with
| (_59_615, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _123_535 = (let _123_534 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _123_533 = (let _123_532 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _123_531 = (let _123_530 = (FSharp_Format.reduce sub)
in (let _123_529 = (let _123_528 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_123_528)::[])
in (_123_530)::_123_529))
in (_123_532)::_123_531))
in (_123_534)::_123_533))
in (FSharp_Format.reduce _123_535))))))))
end))
in (let docs = (Support.List.map (fun ( _59_628 ) -> (match (_59_628) with
| (x, s, m) -> begin
(let _123_537 = (for1_mod true (x, s, m))
in (x, _123_537))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





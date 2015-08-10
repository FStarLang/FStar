
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
(match ((let _130_32 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _130_32))) with
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
(let _130_37 = (path_of_ns currentModule ns)
in (_130_37, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _130_40 = (Support.String.get s 0)
in (Support.Char.lowercase _130_40)) <> (Support.String.get s 0))) with
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
(let _130_47 = (let _130_46 = (let _130_45 = (ptsym_of_symbol s)
in (_130_45)::[])
in (Support.List.append p _130_46))
in (Support.String.concat "." _130_47))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_58 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_58) with
| (p, s) -> begin
(let s = (match (((let _130_52 = (Support.String.get s 0)
in (Support.Char.uppercase _130_52)) <> (Support.String.get s 0))) with
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
(let _130_94 = (let _130_93 = (encode_char c)
in (Support.String.strcat "\'" _130_93))
in (Support.String.strcat _130_94 "\'"))
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
in (let _130_106 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _130_106)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _130_109 = (let _130_108 = (let _130_107 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _130_107 doc))
in (FSharp_Format.hbox _130_108))
in (FSharp_Format.parens _130_109))
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
in (let _130_112 = (let _130_111 = (let _130_110 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_110 args))
in (FSharp_Format.hbox _130_111))
in (FSharp_Format.parens _130_112)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _130_114 = (let _130_113 = (as_standard_type name)
in (Support.Option.get _130_113))
in (Support.Prims.snd _130_114))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _130_118 = (let _130_117 = (let _130_116 = (let _130_115 = (FSharp_Format.text name)
in (_130_115)::[])
in (args)::_130_116)
in (FSharp_Format.reduce1 _130_117))
in (FSharp_Format.hbox _130_118))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _59_205, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _130_123 = (let _130_122 = (let _130_121 = (let _130_120 = (let _130_119 = (FSharp_Format.text " -> ")
in (_130_119)::(d2)::[])
in (d1)::_130_120)
in (FSharp_Format.reduce1 _130_121))
in (FSharp_Format.hbox _130_122))
in (maybe_paren outer t_prio_fun _130_123))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _130_128 = (let _130_127 = (let _130_126 = (let _130_125 = (let _130_124 = (FSharp_Format.text " ")
in (_130_124)::(d1)::[])
in (d2)::_130_125)
in (FSharp_Format.reduce1 _130_126))
in (FSharp_Format.hbox _130_127))
in (maybe_paren outer t_prio_fun _130_128))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _130_153 = (let _130_152 = (let _130_151 = (FSharp_Format.text "Obj.magic ")
in (_130_151)::(doc)::[])
in (FSharp_Format.reduce _130_152))
in (FSharp_Format.parens _130_153)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _130_157 = (let _130_156 = (let _130_155 = (FSharp_Format.text ";")
in (_130_155)::(FSharp_Format.hardline)::[])
in (d)::_130_156)
in (FSharp_Format.reduce _130_157))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _130_158 = (string_of_mlconstant c)
in (FSharp_Format.text _130_158))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _59_239)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _130_159 = (ptsym currentModule path)
in (FSharp_Format.text _130_159))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_251 ) -> (match (_59_251) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _130_166 = (let _130_165 = (let _130_162 = (ptsym currentModule (path, name))
in (FSharp_Format.text _130_162))
in (let _130_164 = (let _130_163 = (FSharp_Format.text "=")
in (_130_163)::(doc)::[])
in (_130_165)::_130_164))
in (FSharp_Format.reduce1 _130_166)))
end))
in (let _130_169 = (let _130_168 = (FSharp_Format.text "; ")
in (let _130_167 = (Support.List.map for1 fields)
in (FSharp_Format.combine _130_168 _130_167)))
in (FSharp_Format.cbrackets _130_169)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _130_171 = (let _130_170 = (as_standard_constructor ctor)
in (Support.Option.get _130_170))
in (Support.Prims.snd _130_171))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _130_173 = (let _130_172 = (as_standard_constructor ctor)
in (Support.Option.get _130_172))
in (Support.Prims.snd _130_173))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _130_177 = (let _130_176 = (FSharp_Format.parens x)
in (let _130_175 = (let _130_174 = (FSharp_Format.text "::")
in (_130_174)::(xs)::[])
in (_130_176)::_130_175))
in (FSharp_Format.reduce _130_177))
end
| (_59_270, _59_272) -> begin
(let _130_183 = (let _130_182 = (FSharp_Format.text name)
in (let _130_181 = (let _130_180 = (let _130_179 = (let _130_178 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_178 args))
in (FSharp_Format.parens _130_179))
in (_130_180)::[])
in (_130_182)::_130_181))
in (FSharp_Format.reduce1 _130_183))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _130_185 = (let _130_184 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_184 docs))
in (FSharp_Format.parens _130_185))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _130_191 = (let _130_190 = (let _130_189 = (let _130_188 = (let _130_187 = (let _130_186 = (FSharp_Format.text "in")
in (_130_186)::(body)::[])
in (FSharp_Format.reduce1 _130_187))
in (_130_188)::[])
in (doc)::_130_189)
in (FSharp_Format.combine FSharp_Format.hardline _130_190))
in (FSharp_Format.parens _130_191))))
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
in (let _130_192 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _130_192))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _130_198 = (let _130_197 = (let _130_196 = (FSharp_Format.text ".")
in (let _130_195 = (let _130_194 = (let _130_193 = (ptsym currentModule f)
in (FSharp_Format.text _130_193))
in (_130_194)::[])
in (_130_196)::_130_195))
in (e)::_130_197)
in (FSharp_Format.reduce _130_198))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_340 ) -> (match (_59_340) with
| ((x, _59_337), xt) -> begin
(let _130_205 = (let _130_204 = (FSharp_Format.text "(")
in (let _130_203 = (let _130_202 = (FSharp_Format.text x)
in (let _130_201 = (let _130_200 = (FSharp_Format.text ")")
in (_130_200)::[])
in (_130_202)::_130_201))
in (_130_204)::_130_203))
in (FSharp_Format.reduce1 _130_205))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _130_211 = (let _130_210 = (FSharp_Format.text "fun")
in (let _130_209 = (let _130_208 = (FSharp_Format.reduce1 ids)
in (let _130_207 = (let _130_206 = (FSharp_Format.text "->")
in (_130_206)::(body)::[])
in (_130_208)::_130_207))
in (_130_210)::_130_209))
in (FSharp_Format.reduce1 _130_211))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _130_224 = (let _130_223 = (let _130_218 = (let _130_217 = (FSharp_Format.text "if")
in (let _130_216 = (let _130_215 = (let _130_214 = (FSharp_Format.text "then")
in (let _130_213 = (let _130_212 = (FSharp_Format.text "begin")
in (_130_212)::[])
in (_130_214)::_130_213))
in (cond)::_130_215)
in (_130_217)::_130_216))
in (FSharp_Format.reduce1 _130_218))
in (let _130_222 = (let _130_221 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _130_220 = (let _130_219 = (FSharp_Format.text "end")
in (_130_219)::[])
in (_130_221)::_130_220))
in (_130_223)::_130_222))
in (FSharp_Format.combine FSharp_Format.hardline _130_224))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _130_247 = (let _130_246 = (let _130_231 = (let _130_230 = (FSharp_Format.text "if")
in (let _130_229 = (let _130_228 = (let _130_227 = (FSharp_Format.text "then")
in (let _130_226 = (let _130_225 = (FSharp_Format.text "begin")
in (_130_225)::[])
in (_130_227)::_130_226))
in (cond)::_130_228)
in (_130_230)::_130_229))
in (FSharp_Format.reduce1 _130_231))
in (let _130_245 = (let _130_244 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _130_243 = (let _130_242 = (let _130_237 = (let _130_236 = (FSharp_Format.text "end")
in (let _130_235 = (let _130_234 = (FSharp_Format.text "else")
in (let _130_233 = (let _130_232 = (FSharp_Format.text "begin")
in (_130_232)::[])
in (_130_234)::_130_233))
in (_130_236)::_130_235))
in (FSharp_Format.reduce1 _130_237))
in (let _130_241 = (let _130_240 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _130_239 = (let _130_238 = (FSharp_Format.text "end")
in (_130_238)::[])
in (_130_240)::_130_239))
in (_130_242)::_130_241))
in (_130_244)::_130_243))
in (_130_246)::_130_245))
in (FSharp_Format.combine FSharp_Format.hardline _130_247))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _130_254 = (let _130_253 = (let _130_252 = (FSharp_Format.text "match")
in (let _130_251 = (let _130_250 = (FSharp_Format.parens cond)
in (let _130_249 = (let _130_248 = (FSharp_Format.text "with")
in (_130_248)::[])
in (_130_250)::_130_249))
in (_130_252)::_130_251))
in (FSharp_Format.reduce1 _130_253))
in (_130_254)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _130_259 = (let _130_258 = (FSharp_Format.text "raise")
in (let _130_257 = (let _130_256 = (let _130_255 = (ptctor currentModule exn)
in (FSharp_Format.text _130_255))
in (_130_256)::[])
in (_130_258)::_130_257))
in (FSharp_Format.reduce1 _130_259))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _130_268 = (let _130_267 = (FSharp_Format.text "raise")
in (let _130_266 = (let _130_265 = (let _130_260 = (ptctor currentModule exn)
in (FSharp_Format.text _130_260))
in (let _130_264 = (let _130_263 = (let _130_262 = (let _130_261 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_261 args))
in (FSharp_Format.parens _130_262))
in (_130_263)::[])
in (_130_265)::_130_264))
in (_130_267)::_130_266))
in (FSharp_Format.reduce1 _130_268)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _130_285 = (let _130_284 = (let _130_272 = (let _130_271 = (FSharp_Format.text "try")
in (let _130_270 = (let _130_269 = (FSharp_Format.text "begin")
in (_130_269)::[])
in (_130_271)::_130_270))
in (FSharp_Format.reduce1 _130_272))
in (let _130_283 = (let _130_282 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _130_281 = (let _130_280 = (let _130_276 = (let _130_275 = (FSharp_Format.text "end")
in (let _130_274 = (let _130_273 = (FSharp_Format.text "with")
in (_130_273)::[])
in (_130_275)::_130_274))
in (FSharp_Format.reduce1 _130_276))
in (let _130_279 = (let _130_278 = (let _130_277 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _130_277))
in (_130_278)::[])
in (_130_280)::_130_279))
in (_130_282)::_130_281))
in (_130_284)::_130_283))
in (FSharp_Format.combine FSharp_Format.hardline _130_285))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_388 = (let _130_290 = (as_bin_op p)
in (Support.Option.get _130_290))
in (match (_59_388) with
| (_59_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _130_293 = (let _130_292 = (let _130_291 = (FSharp_Format.text txt)
in (_130_291)::(e2)::[])
in (e1)::_130_292)
in (FSharp_Format.reduce1 _130_293))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_398 = (let _130_297 = (as_uni_op p)
in (Support.Option.get _130_297))
in (match (_59_398) with
| (_59_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _130_301 = (let _130_300 = (FSharp_Format.text txt)
in (let _130_299 = (let _130_298 = (FSharp_Format.parens e1)
in (_130_298)::[])
in (_130_300)::_130_299))
in (FSharp_Format.reduce1 _130_301))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _130_304 = (string_of_mlconstant c)
in (FSharp_Format.text _130_304))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_415 ) -> (match (_59_415) with
| (name, p) -> begin
(let _130_313 = (let _130_312 = (let _130_307 = (ptsym currentModule (path, name))
in (FSharp_Format.text _130_307))
in (let _130_311 = (let _130_310 = (FSharp_Format.text "=")
in (let _130_309 = (let _130_308 = (doc_of_pattern currentModule p)
in (_130_308)::[])
in (_130_310)::_130_309))
in (_130_312)::_130_311))
in (FSharp_Format.reduce1 _130_313))
end))
in (let _130_316 = (let _130_315 = (FSharp_Format.text "; ")
in (let _130_314 = (Support.List.map for1 fields)
in (FSharp_Format.combine _130_315 _130_314)))
in (FSharp_Format.cbrackets _130_316)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _130_318 = (let _130_317 = (as_standard_constructor ctor)
in (Support.Option.get _130_317))
in (Support.Prims.snd _130_318))
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
(let _130_320 = (let _130_319 = (as_standard_constructor ctor)
in (Support.Option.get _130_319))
in (Support.Prims.snd _130_320))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _130_323 = (let _130_322 = (let _130_321 = (FSharp_Format.text "::")
in (_130_321)::(xs)::[])
in (x)::_130_322)
in (FSharp_Format.reduce _130_323))
end
| (_59_433, _59_435) -> begin
(let _130_329 = (let _130_328 = (FSharp_Format.text name)
in (let _130_327 = (let _130_326 = (let _130_325 = (let _130_324 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_324 ps))
in (FSharp_Format.parens _130_325))
in (_130_326)::[])
in (_130_328)::_130_327))
in (FSharp_Format.reduce1 _130_329))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _130_331 = (let _130_330 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_330 ps))
in (FSharp_Format.parens _130_331)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _130_332 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _130_332 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_449 ) -> (match (_59_449) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _130_338 = (let _130_337 = (FSharp_Format.text "|")
in (let _130_336 = (let _130_335 = (doc_of_pattern currentModule p)
in (_130_335)::[])
in (_130_337)::_130_336))
in (FSharp_Format.reduce1 _130_338))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _130_344 = (let _130_343 = (FSharp_Format.text "|")
in (let _130_342 = (let _130_341 = (doc_of_pattern currentModule p)
in (let _130_340 = (let _130_339 = (FSharp_Format.text "when")
in (_130_339)::(c)::[])
in (_130_341)::_130_340))
in (_130_343)::_130_342))
in (FSharp_Format.reduce1 _130_344)))
end)
in (let _130_355 = (let _130_354 = (let _130_349 = (let _130_348 = (let _130_347 = (FSharp_Format.text "->")
in (let _130_346 = (let _130_345 = (FSharp_Format.text "begin")
in (_130_345)::[])
in (_130_347)::_130_346))
in (case)::_130_348)
in (FSharp_Format.reduce1 _130_349))
in (let _130_353 = (let _130_352 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _130_351 = (let _130_350 = (FSharp_Format.text "end")
in (_130_350)::[])
in (_130_352)::_130_351))
in (_130_354)::_130_353))
in (FSharp_Format.combine FSharp_Format.hardline _130_355)))
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
in (let _130_366 = (let _130_365 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _130_364 = (let _130_363 = (FSharp_Format.reduce1 ids)
in (let _130_362 = (let _130_361 = (FSharp_Format.text "=")
in (_130_361)::(e)::[])
in (_130_363)::_130_362))
in (_130_365)::_130_364))
in (FSharp_Format.reduce1 _130_366)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _130_370 = (let _130_369 = (FSharp_Format.text "let")
in (let _130_368 = (let _130_367 = (FSharp_Format.text "rec")
in (_130_367)::[])
in (_130_369)::_130_368))
in (FSharp_Format.reduce1 _130_370))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _130_374 = (let _130_373 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_130_373)::(doc)::[])
in (FSharp_Format.reduce1 _130_374))) lets)
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
in (let _130_383 = (let _130_382 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _130_382 doc))
in (FSharp_Format.parens _130_383)))
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
in (let _130_390 = (let _130_389 = (let _130_388 = (FSharp_Format.text ":")
in (_130_388)::(ty)::[])
in (name)::_130_389)
in (FSharp_Format.reduce1 _130_390))))
end))
in (let _130_393 = (let _130_392 = (FSharp_Format.text "; ")
in (let _130_391 = (Support.List.map forfield fields)
in (FSharp_Format.combine _130_392 _130_391)))
in (FSharp_Format.cbrackets _130_393)))
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
in (let tys = (let _130_396 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _130_396 tys))
in (let _130_400 = (let _130_399 = (FSharp_Format.text name)
in (let _130_398 = (let _130_397 = (FSharp_Format.text "of")
in (_130_397)::(tys)::[])
in (_130_399)::_130_398))
in (FSharp_Format.reduce1 _130_400))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _130_403 = (let _130_402 = (FSharp_Format.text "|")
in (_130_402)::(d)::[])
in (FSharp_Format.reduce1 _130_403))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _130_407 = (let _130_406 = (let _130_405 = (let _130_404 = (ptsym currentModule ([], x))
in (FSharp_Format.text _130_404))
in (_130_405)::[])
in (tparams)::_130_406)
in (FSharp_Format.reduce1 _130_407))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _130_412 = (let _130_411 = (let _130_410 = (let _130_409 = (let _130_408 = (FSharp_Format.text "=")
in (_130_408)::[])
in (doc)::_130_409)
in (FSharp_Format.reduce1 _130_410))
in (_130_411)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _130_412)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _130_417 = (let _130_416 = (FSharp_Format.text "type")
in (let _130_415 = (let _130_414 = (let _130_413 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _130_413 doc))
in (_130_414)::[])
in (_130_416)::_130_415))
in (FSharp_Format.reduce1 _130_417))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _130_437 = (let _130_436 = (let _130_429 = (let _130_428 = (FSharp_Format.text "module")
in (let _130_427 = (let _130_426 = (FSharp_Format.text x)
in (let _130_425 = (let _130_424 = (FSharp_Format.text "=")
in (_130_424)::[])
in (_130_426)::_130_425))
in (_130_428)::_130_427))
in (FSharp_Format.reduce1 _130_429))
in (let _130_435 = (let _130_434 = (doc_of_sig currentModule subsig)
in (let _130_433 = (let _130_432 = (let _130_431 = (let _130_430 = (FSharp_Format.text "end")
in (_130_430)::[])
in (FSharp_Format.reduce1 _130_431))
in (_130_432)::[])
in (_130_434)::_130_433))
in (_130_436)::_130_435))
in (FSharp_Format.combine FSharp_Format.hardline _130_437))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _130_441 = (let _130_440 = (FSharp_Format.text "exception")
in (let _130_439 = (let _130_438 = (FSharp_Format.text x)
in (_130_438)::[])
in (_130_440)::_130_439))
in (FSharp_Format.reduce1 _130_441))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _130_443 = (let _130_442 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _130_442 args))
in (FSharp_Format.parens _130_443))
in (let _130_449 = (let _130_448 = (FSharp_Format.text "exception")
in (let _130_447 = (let _130_446 = (FSharp_Format.text x)
in (let _130_445 = (let _130_444 = (FSharp_Format.text "of")
in (_130_444)::(args)::[])
in (_130_446)::_130_445))
in (_130_448)::_130_447))
in (FSharp_Format.reduce1 _130_449))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_59_544, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _130_455 = (let _130_454 = (FSharp_Format.text "val")
in (let _130_453 = (let _130_452 = (FSharp_Format.text x)
in (let _130_451 = (let _130_450 = (FSharp_Format.text ": ")
in (_130_450)::(ty)::[])
in (_130_452)::_130_451))
in (_130_454)::_130_453))
in (FSharp_Format.reduce1 _130_455)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _130_466 = (let _130_465 = (FSharp_Format.text "exception")
in (let _130_464 = (let _130_463 = (FSharp_Format.text x)
in (_130_463)::[])
in (_130_465)::_130_464))
in (FSharp_Format.reduce1 _130_466))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _130_468 = (let _130_467 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _130_467 args))
in (FSharp_Format.parens _130_468))
in (let _130_474 = (let _130_473 = (FSharp_Format.text "exception")
in (let _130_472 = (let _130_471 = (FSharp_Format.text x)
in (let _130_470 = (let _130_469 = (FSharp_Format.text "of")
in (_130_469)::(args)::[])
in (_130_471)::_130_470))
in (_130_473)::_130_472))
in (FSharp_Format.reduce1 _130_474))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _130_482 = (let _130_481 = (FSharp_Format.text "let")
in (let _130_480 = (let _130_479 = (FSharp_Format.text "_")
in (let _130_478 = (let _130_477 = (FSharp_Format.text "=")
in (let _130_476 = (let _130_475 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_130_475)::[])
in (_130_477)::_130_476))
in (_130_479)::_130_478))
in (_130_481)::_130_480))
in (FSharp_Format.reduce1 _130_482))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_583 ) -> (match (_59_583) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_590 ) -> (match (_59_590) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _130_501 = (let _130_500 = (FSharp_Format.text "module")
in (let _130_499 = (let _130_498 = (FSharp_Format.text x)
in (let _130_497 = (let _130_496 = (FSharp_Format.text ":")
in (let _130_495 = (let _130_494 = (FSharp_Format.text "sig")
in (_130_494)::[])
in (_130_496)::_130_495))
in (_130_498)::_130_497))
in (_130_500)::_130_499))
in (FSharp_Format.reduce1 _130_501))
in (let tail = (let _130_503 = (let _130_502 = (FSharp_Format.text "end")
in (_130_502)::[])
in (FSharp_Format.reduce1 _130_503))
in (let doc = (Support.Option.map (fun ( _59_596 ) -> (match (_59_596) with
| (s, _59_595) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _130_513 = (let _130_512 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _130_511 = (let _130_510 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _130_509 = (let _130_508 = (FSharp_Format.reduce sub)
in (let _130_507 = (let _130_506 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_130_506)::[])
in (_130_508)::_130_507))
in (_130_510)::_130_509))
in (_130_512)::_130_511))
in (FSharp_Format.reduce _130_513)))))))
end))
and for1_mod = (fun ( istop ) ( _59_609 ) -> (match (_59_609) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_610 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _130_523 = (match ((not (istop))) with
| true -> begin
(let _130_522 = (FSharp_Format.text "module")
in (let _130_521 = (let _130_520 = (FSharp_Format.text x)
in (let _130_519 = (let _130_518 = (FSharp_Format.text "=")
in (let _130_517 = (let _130_516 = (FSharp_Format.text "struct")
in (_130_516)::[])
in (_130_518)::_130_517))
in (_130_520)::_130_519))
in (_130_522)::_130_521))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _130_523))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _130_525 = (let _130_524 = (FSharp_Format.text "end")
in (_130_524)::[])
in (FSharp_Format.reduce1 _130_525))
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
in (let _130_535 = (let _130_534 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _130_533 = (let _130_532 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _130_531 = (let _130_530 = (FSharp_Format.reduce sub)
in (let _130_529 = (let _130_528 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_130_528)::[])
in (_130_530)::_130_529))
in (_130_532)::_130_531))
in (_130_534)::_130_533))
in (FSharp_Format.reduce _130_535))))))))
end))
in (let docs = (Support.List.map (fun ( _59_628 ) -> (match (_59_628) with
| (x, s, m) -> begin
(let _130_537 = (for1_mod true (x, s, m))
in (x, _130_537))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





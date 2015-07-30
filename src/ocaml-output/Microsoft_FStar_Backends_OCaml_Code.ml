
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

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Set")::[])::(("Map")::[])::(("Heap")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

let rec in_ns = (fun ( x ) -> (match (x) with
| ([], _) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_, _) -> begin
false
end))

let path_of_ns = (fun ( currentModule ) ( ns ) -> (let outsupport = (fun ( ns ) -> (let ns' = (Microsoft_FStar_Backends_ML_Util.flatten_ns ns)
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
(match ((let _65_25174 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _65_25174))) with
| None -> begin
(outsupport ns)
end
| _ -> begin
ns
end)
end
| Some (sns) -> begin
("Support")::ns
end))))

let mlpath_of_mlpath = (fun ( currentModule ) ( x ) -> (match ((Microsoft_FStar_Backends_ML_Syntax.string_of_mlpath x)) with
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
| _ -> begin
(let _64_46 = x
in (match (_64_46) with
| (ns, x) -> begin
(let _65_25179 = (path_of_ns currentModule ns)
in (_65_25179, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _65_25182 = (Support.String.get s 0)
in (Support.Char.lowercase _65_25182)) <> (Support.String.get s 0))) with
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
(let _64_52 = (mlpath_of_mlpath currentModule mlp)
in (match (_64_52) with
| (p, s) -> begin
(let _65_25189 = (let _65_25188 = (let _65_25187 = (ptsym_of_symbol s)
in (_65_25187)::[])
in (Support.List.append p _65_25188))
in (Support.String.concat "." _65_25189))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _64_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_64_57) with
| (p, s) -> begin
(let s = (match (((let _65_25194 = (Support.String.get s 0)
in (Support.Char.uppercase _65_25194)) <> (Support.String.get s 0))) with
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

let as_bin_op = (fun ( _64_62 ) -> (match (_64_62) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _64_68 ) -> (match (_64_68) with
| (y, _, _) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _64_72 ) -> (match (_64_72) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _64_76 ) -> (match (_64_76) with
| (y, _) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _64_80 ) -> (match (_64_80) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _64_84 ) -> (match (_64_84) with
| (y, _) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _64_88 ) -> (match (_64_88) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _64_92 ) -> (match (_64_92) with
| (y, _) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _64_96 ) ( inner ) ( doc ) -> (match (_64_96) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _64_105 = _inner
in (match (_64_105) with
| (pi, fi) -> begin
(let _64_108 = _outer
in (match (_64_108) with
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
| (_, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_, _) -> begin
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
| _ -> begin
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
(let _65_25236 = (let _65_25235 = (encode_char c)
in (Support.String.strcat "\'" _65_25235))
in (Support.String.strcat _65_25236 "\'"))
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

let rec doc_of_mltype' = (fun ( currentModule ) ( outer ) ( ty ) -> (match (ty) with
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Var (x) -> begin
(let escape_tyvar = (fun ( s ) -> (match ((Support.Microsoft.FStar.Util.starts_with s "\'_")) with
| true -> begin
(Support.Microsoft.FStar.Util.replace_char s '_' 'u')
end
| false -> begin
s
end))
in (let _65_25248 = (Support.Prims.pipe_left escape_tyvar (Microsoft_FStar_Backends_ML_Syntax.idsym x))
in (FSharp_Format.text _65_25248)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _65_25251 = (let _65_25250 = (let _65_25249 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_25249 doc))
in (FSharp_Format.hbox _65_25250))
in (FSharp_Format.parens _65_25251))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Named ((args, name)) -> begin
(let args = (match (args) with
| [] -> begin
FSharp_Format.empty
end
| arg::[] -> begin
(doc_of_mltype currentModule (t_prio_name, Left) arg)
end
| _ -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _65_25254 = (let _65_25253 = (let _65_25252 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25252 args))
in (FSharp_Format.hbox _65_25253))
in (FSharp_Format.parens _65_25254)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _65_25256 = (let _65_25255 = (as_standard_type name)
in (Support.Option.get _65_25255))
in (Support.Prims.snd _65_25256))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _65_25260 = (let _65_25259 = (let _65_25258 = (let _65_25257 = (FSharp_Format.text name)
in (_65_25257)::[])
in (args)::_65_25258)
in (FSharp_Format.reduce1 _65_25259))
in (FSharp_Format.hbox _65_25260))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_25265 = (let _65_25264 = (let _65_25263 = (let _65_25262 = (let _65_25261 = (FSharp_Format.text " -> ")
in (_65_25261)::(d2)::[])
in (d1)::_65_25262)
in (FSharp_Format.reduce1 _65_25263))
in (FSharp_Format.hbox _65_25264))
in (maybe_paren outer t_prio_fun _65_25265))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_25270 = (let _65_25269 = (let _65_25268 = (let _65_25267 = (let _65_25266 = (FSharp_Format.text " ")
in (_65_25266)::(d1)::[])
in (d2)::_65_25267)
in (FSharp_Format.reduce1 _65_25268))
in (FSharp_Format.hbox _65_25269))
in (maybe_paren outer t_prio_fun _65_25270))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Backends_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_25295 = (let _65_25294 = (let _65_25293 = (FSharp_Format.text "Obj.magic ")
in (_65_25293)::(doc)::[])
in (FSharp_Format.reduce _65_25294))
in (FSharp_Format.parens _65_25295)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _65_25299 = (let _65_25298 = (let _65_25297 = (FSharp_Format.text ";")
in (_65_25297)::(FSharp_Format.hardline)::[])
in (d)::_65_25298)
in (FSharp_Format.reduce _65_25299))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _65_25300 = (string_of_mlconstant c)
in (FSharp_Format.text _65_25300))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _65_25301 = (ptsym currentModule path)
in (FSharp_Format.text _65_25301))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _64_250 ) -> (match (_64_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_25308 = (let _65_25307 = (let _65_25304 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_25304))
in (let _65_25306 = (let _65_25305 = (FSharp_Format.text "=")
in (_65_25305)::(doc)::[])
in (_65_25307)::_65_25306))
in (FSharp_Format.reduce1 _65_25308)))
end))
in (let _65_25311 = (let _65_25310 = (FSharp_Format.text "; ")
in (let _65_25309 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_25310 _65_25309)))
in (FSharp_Format.cbrackets _65_25311)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_25313 = (let _65_25312 = (as_standard_constructor ctor)
in (Support.Option.get _65_25312))
in (Support.Prims.snd _65_25313))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_25315 = (let _65_25314 = (as_standard_constructor ctor)
in (Support.Option.get _65_25314))
in (Support.Prims.snd _65_25315))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _65_25319 = (let _65_25318 = (FSharp_Format.parens x)
in (let _65_25317 = (let _65_25316 = (FSharp_Format.text "::")
in (_65_25316)::(xs)::[])
in (_65_25318)::_65_25317))
in (FSharp_Format.reduce _65_25319))
end
| (_, _) -> begin
(let _65_25325 = (let _65_25324 = (FSharp_Format.text name)
in (let _65_25323 = (let _65_25322 = (let _65_25321 = (let _65_25320 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25320 args))
in (FSharp_Format.parens _65_25321))
in (_65_25322)::[])
in (_65_25324)::_65_25323))
in (FSharp_Format.reduce1 _65_25325))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _65_25327 = (let _65_25326 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25326 docs))
in (FSharp_Format.parens _65_25327))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _65_25333 = (let _65_25332 = (let _65_25331 = (let _65_25330 = (let _65_25329 = (let _65_25328 = (FSharp_Format.text "in")
in (_65_25328)::(body)::[])
in (FSharp_Format.reduce1 _65_25329))
in (_65_25330)::[])
in (doc)::_65_25331)
in (FSharp_Format.combine FSharp_Format.hardline _65_25332))
in (FSharp_Format.parens _65_25333))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_App ((Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), unitVal::[])), e1::e2::[]) when ((is_bin_op p) && (unitVal = Microsoft_FStar_Backends_ML_Syntax.ml_unit)) -> begin
(doc_of_binop currentModule p e1 e2)
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(doc_of_uniop currentModule p e1)
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_App ((Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), unitVal::[])), e1::[]) when ((is_uni_op p) && (unitVal = Microsoft_FStar_Backends_ML_Syntax.ml_unit)) -> begin
(doc_of_uniop currentModule p e1)
end
| _ -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _65_25334 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _65_25334))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _65_25340 = (let _65_25339 = (let _65_25338 = (FSharp_Format.text ".")
in (let _65_25337 = (let _65_25336 = (let _65_25335 = (ptsym currentModule f)
in (FSharp_Format.text _65_25335))
in (_65_25336)::[])
in (_65_25338)::_65_25337))
in (e)::_65_25339)
in (FSharp_Format.reduce _65_25340))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _64_339 ) -> (match (_64_339) with
| ((x, _), xt) -> begin
(let _65_25347 = (let _65_25346 = (FSharp_Format.text "(")
in (let _65_25345 = (let _65_25344 = (FSharp_Format.text x)
in (let _65_25343 = (let _65_25342 = (FSharp_Format.text ")")
in (_65_25342)::[])
in (_65_25344)::_65_25343))
in (_65_25346)::_65_25345))
in (FSharp_Format.reduce1 _65_25347))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _65_25353 = (let _65_25352 = (FSharp_Format.text "fun")
in (let _65_25351 = (let _65_25350 = (FSharp_Format.reduce1 ids)
in (let _65_25349 = (let _65_25348 = (FSharp_Format.text "->")
in (_65_25348)::(body)::[])
in (_65_25350)::_65_25349))
in (_65_25352)::_65_25351))
in (FSharp_Format.reduce1 _65_25353))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_25366 = (let _65_25365 = (let _65_25360 = (let _65_25359 = (FSharp_Format.text "if")
in (let _65_25358 = (let _65_25357 = (let _65_25356 = (FSharp_Format.text "then")
in (let _65_25355 = (let _65_25354 = (FSharp_Format.text "begin")
in (_65_25354)::[])
in (_65_25356)::_65_25355))
in (cond)::_65_25357)
in (_65_25359)::_65_25358))
in (FSharp_Format.reduce1 _65_25360))
in (let _65_25364 = (let _65_25363 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_25362 = (let _65_25361 = (FSharp_Format.text "end")
in (_65_25361)::[])
in (_65_25363)::_65_25362))
in (_65_25365)::_65_25364))
in (FSharp_Format.combine FSharp_Format.hardline _65_25366))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_25389 = (let _65_25388 = (let _65_25373 = (let _65_25372 = (FSharp_Format.text "if")
in (let _65_25371 = (let _65_25370 = (let _65_25369 = (FSharp_Format.text "then")
in (let _65_25368 = (let _65_25367 = (FSharp_Format.text "begin")
in (_65_25367)::[])
in (_65_25369)::_65_25368))
in (cond)::_65_25370)
in (_65_25372)::_65_25371))
in (FSharp_Format.reduce1 _65_25373))
in (let _65_25387 = (let _65_25386 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_25385 = (let _65_25384 = (let _65_25379 = (let _65_25378 = (FSharp_Format.text "end")
in (let _65_25377 = (let _65_25376 = (FSharp_Format.text "else")
in (let _65_25375 = (let _65_25374 = (FSharp_Format.text "begin")
in (_65_25374)::[])
in (_65_25376)::_65_25375))
in (_65_25378)::_65_25377))
in (FSharp_Format.reduce1 _65_25379))
in (let _65_25383 = (let _65_25382 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _65_25381 = (let _65_25380 = (FSharp_Format.text "end")
in (_65_25380)::[])
in (_65_25382)::_65_25381))
in (_65_25384)::_65_25383))
in (_65_25386)::_65_25385))
in (_65_25388)::_65_25387))
in (FSharp_Format.combine FSharp_Format.hardline _65_25389))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _65_25396 = (let _65_25395 = (let _65_25394 = (FSharp_Format.text "match")
in (let _65_25393 = (let _65_25392 = (FSharp_Format.parens cond)
in (let _65_25391 = (let _65_25390 = (FSharp_Format.text "with")
in (_65_25390)::[])
in (_65_25392)::_65_25391))
in (_65_25394)::_65_25393))
in (FSharp_Format.reduce1 _65_25395))
in (_65_25396)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _65_25401 = (let _65_25400 = (FSharp_Format.text "raise")
in (let _65_25399 = (let _65_25398 = (let _65_25397 = (ptctor currentModule exn)
in (FSharp_Format.text _65_25397))
in (_65_25398)::[])
in (_65_25400)::_65_25399))
in (FSharp_Format.reduce1 _65_25401))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _65_25410 = (let _65_25409 = (FSharp_Format.text "raise")
in (let _65_25408 = (let _65_25407 = (let _65_25402 = (ptctor currentModule exn)
in (FSharp_Format.text _65_25402))
in (let _65_25406 = (let _65_25405 = (let _65_25404 = (let _65_25403 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25403 args))
in (FSharp_Format.parens _65_25404))
in (_65_25405)::[])
in (_65_25407)::_65_25406))
in (_65_25409)::_65_25408))
in (FSharp_Format.reduce1 _65_25410)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _65_25427 = (let _65_25426 = (let _65_25414 = (let _65_25413 = (FSharp_Format.text "try")
in (let _65_25412 = (let _65_25411 = (FSharp_Format.text "begin")
in (_65_25411)::[])
in (_65_25413)::_65_25412))
in (FSharp_Format.reduce1 _65_25414))
in (let _65_25425 = (let _65_25424 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_25423 = (let _65_25422 = (let _65_25418 = (let _65_25417 = (FSharp_Format.text "end")
in (let _65_25416 = (let _65_25415 = (FSharp_Format.text "with")
in (_65_25415)::[])
in (_65_25417)::_65_25416))
in (FSharp_Format.reduce1 _65_25418))
in (let _65_25421 = (let _65_25420 = (let _65_25419 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _65_25419))
in (_65_25420)::[])
in (_65_25422)::_65_25421))
in (_65_25424)::_65_25423))
in (_65_25426)::_65_25425))
in (FSharp_Format.combine FSharp_Format.hardline _65_25427))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _64_387 = (let _65_25432 = (as_bin_op p)
in (Support.Option.get _65_25432))
in (match (_64_387) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _65_25435 = (let _65_25434 = (let _65_25433 = (FSharp_Format.text txt)
in (_65_25433)::(e2)::[])
in (e1)::_65_25434)
in (FSharp_Format.reduce1 _65_25435))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _64_397 = (let _65_25439 = (as_uni_op p)
in (Support.Option.get _65_25439))
in (match (_64_397) with
| (_, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _65_25443 = (let _65_25442 = (FSharp_Format.text txt)
in (let _65_25441 = (let _65_25440 = (FSharp_Format.parens e1)
in (_65_25440)::[])
in (_65_25442)::_65_25441))
in (FSharp_Format.reduce1 _65_25443))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _65_25446 = (string_of_mlconstant c)
in (FSharp_Format.text _65_25446))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _64_414 ) -> (match (_64_414) with
| (name, p) -> begin
(let _65_25455 = (let _65_25454 = (let _65_25449 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_25449))
in (let _65_25453 = (let _65_25452 = (FSharp_Format.text "=")
in (let _65_25451 = (let _65_25450 = (doc_of_pattern currentModule p)
in (_65_25450)::[])
in (_65_25452)::_65_25451))
in (_65_25454)::_65_25453))
in (FSharp_Format.reduce1 _65_25455))
end))
in (let _65_25458 = (let _65_25457 = (FSharp_Format.text "; ")
in (let _65_25456 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_25457 _65_25456)))
in (FSharp_Format.cbrackets _65_25458)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_25460 = (let _65_25459 = (as_standard_constructor ctor)
in (Support.Option.get _65_25459))
in (Support.Prims.snd _65_25460))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, ps)) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_25462 = (let _65_25461 = (as_standard_constructor ctor)
in (Support.Option.get _65_25461))
in (Support.Prims.snd _65_25462))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _65_25465 = (let _65_25464 = (let _65_25463 = (FSharp_Format.text "::")
in (_65_25463)::(xs)::[])
in (x)::_65_25464)
in (FSharp_Format.reduce _65_25465))
end
| (_, _) -> begin
(let _65_25471 = (let _65_25470 = (FSharp_Format.text name)
in (let _65_25469 = (let _65_25468 = (let _65_25467 = (let _65_25466 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25466 ps))
in (FSharp_Format.parens _65_25467))
in (_65_25468)::[])
in (_65_25470)::_65_25469))
in (FSharp_Format.reduce1 _65_25471))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _65_25473 = (let _65_25472 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25472 ps))
in (FSharp_Format.parens _65_25473)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _65_25474 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _65_25474 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _64_448 ) -> (match (_64_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _65_25480 = (let _65_25479 = (FSharp_Format.text "|")
in (let _65_25478 = (let _65_25477 = (doc_of_pattern currentModule p)
in (_65_25477)::[])
in (_65_25479)::_65_25478))
in (FSharp_Format.reduce1 _65_25480))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _65_25486 = (let _65_25485 = (FSharp_Format.text "|")
in (let _65_25484 = (let _65_25483 = (doc_of_pattern currentModule p)
in (let _65_25482 = (let _65_25481 = (FSharp_Format.text "when")
in (_65_25481)::(c)::[])
in (_65_25483)::_65_25482))
in (_65_25485)::_65_25484))
in (FSharp_Format.reduce1 _65_25486)))
end)
in (let _65_25497 = (let _65_25496 = (let _65_25491 = (let _65_25490 = (let _65_25489 = (FSharp_Format.text "->")
in (let _65_25488 = (let _65_25487 = (FSharp_Format.text "begin")
in (_65_25487)::[])
in (_65_25489)::_65_25488))
in (case)::_65_25490)
in (FSharp_Format.reduce1 _65_25491))
in (let _65_25495 = (let _65_25494 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_25493 = (let _65_25492 = (FSharp_Format.text "end")
in (_65_25492)::[])
in (_65_25494)::_65_25493))
in (_65_25496)::_65_25495))
in (FSharp_Format.combine FSharp_Format.hardline _65_25497)))
end))
and doc_of_lets = (fun ( currentModule ) ( _64_457 ) -> (match (_64_457) with
| (rec_, lets) -> begin
(let for1 = (fun ( _64_464 ) -> (match (_64_464) with
| {Microsoft_FStar_Backends_ML_Syntax.mllb_name = name; Microsoft_FStar_Backends_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Backends_ML_Syntax.mllb_add_unit = _; Microsoft_FStar_Backends_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _64_470 ) -> (match (_64_470) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _65_25508 = (let _65_25507 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _65_25506 = (let _65_25505 = (FSharp_Format.reduce1 ids)
in (let _65_25504 = (let _65_25503 = (FSharp_Format.text "=")
in (_65_25503)::(e)::[])
in (_65_25505)::_65_25504))
in (_65_25507)::_65_25506))
in (FSharp_Format.reduce1 _65_25508)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _65_25512 = (let _65_25511 = (FSharp_Format.text "let")
in (let _65_25510 = (let _65_25509 = (FSharp_Format.text "rec")
in (_65_25509)::[])
in (_65_25511)::_65_25510))
in (FSharp_Format.reduce1 _65_25512))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _65_25516 = (let _65_25515 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_65_25515)::(doc)::[])
in (FSharp_Format.reduce1 _65_25516))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _64_483 ) -> (match (_64_483) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))
end
| _ -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym x))) tparams)
in (let _65_25525 = (let _65_25524 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_25524 doc))
in (FSharp_Format.parens _65_25525)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _64_501 ) -> (match (_64_501) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _65_25532 = (let _65_25531 = (let _65_25530 = (FSharp_Format.text ":")
in (_65_25530)::(ty)::[])
in (name)::_65_25531)
in (FSharp_Format.reduce1 _65_25532))))
end))
in (let _65_25535 = (let _65_25534 = (FSharp_Format.text "; ")
in (let _65_25533 = (Support.List.map forfield fields)
in (FSharp_Format.combine _65_25534 _65_25533)))
in (FSharp_Format.cbrackets _65_25535)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _64_509 ) -> (match (_64_509) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _ -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _65_25538 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_25538 tys))
in (let _65_25542 = (let _65_25541 = (FSharp_Format.text name)
in (let _65_25540 = (let _65_25539 = (FSharp_Format.text "of")
in (_65_25539)::(tys)::[])
in (_65_25541)::_65_25540))
in (FSharp_Format.reduce1 _65_25542))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _65_25545 = (let _65_25544 = (FSharp_Format.text "|")
in (_65_25544)::(d)::[])
in (FSharp_Format.reduce1 _65_25545))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _65_25549 = (let _65_25548 = (let _65_25547 = (let _65_25546 = (ptsym currentModule ([], x))
in (FSharp_Format.text _65_25546))
in (_65_25547)::[])
in (tparams)::_65_25548)
in (FSharp_Format.reduce1 _65_25549))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _65_25554 = (let _65_25553 = (let _65_25552 = (let _65_25551 = (let _65_25550 = (FSharp_Format.text "=")
in (_65_25550)::[])
in (doc)::_65_25551)
in (FSharp_Format.reduce1 _65_25552))
in (_65_25553)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _65_25554)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _65_25559 = (let _65_25558 = (FSharp_Format.text "type")
in (let _65_25557 = (let _65_25556 = (let _65_25555 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _65_25555 doc))
in (_65_25556)::[])
in (_65_25558)::_65_25557))
in (FSharp_Format.reduce1 _65_25559))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _65_25579 = (let _65_25578 = (let _65_25571 = (let _65_25570 = (FSharp_Format.text "module")
in (let _65_25569 = (let _65_25568 = (FSharp_Format.text x)
in (let _65_25567 = (let _65_25566 = (FSharp_Format.text "=")
in (_65_25566)::[])
in (_65_25568)::_65_25567))
in (_65_25570)::_65_25569))
in (FSharp_Format.reduce1 _65_25571))
in (let _65_25577 = (let _65_25576 = (doc_of_sig currentModule subsig)
in (let _65_25575 = (let _65_25574 = (let _65_25573 = (let _65_25572 = (FSharp_Format.text "end")
in (_65_25572)::[])
in (FSharp_Format.reduce1 _65_25573))
in (_65_25574)::[])
in (_65_25576)::_65_25575))
in (_65_25578)::_65_25577))
in (FSharp_Format.combine FSharp_Format.hardline _65_25579))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _65_25583 = (let _65_25582 = (FSharp_Format.text "exception")
in (let _65_25581 = (let _65_25580 = (FSharp_Format.text x)
in (_65_25580)::[])
in (_65_25582)::_65_25581))
in (FSharp_Format.reduce1 _65_25583))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_25585 = (let _65_25584 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_25584 args))
in (FSharp_Format.parens _65_25585))
in (let _65_25591 = (let _65_25590 = (FSharp_Format.text "exception")
in (let _65_25589 = (let _65_25588 = (FSharp_Format.text x)
in (let _65_25587 = (let _65_25586 = (FSharp_Format.text "of")
in (_65_25586)::(args)::[])
in (_65_25588)::_65_25587))
in (_65_25590)::_65_25589))
in (FSharp_Format.reduce1 _65_25591))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _65_25597 = (let _65_25596 = (FSharp_Format.text "val")
in (let _65_25595 = (let _65_25594 = (FSharp_Format.text x)
in (let _65_25593 = (let _65_25592 = (FSharp_Format.text ": ")
in (_65_25592)::(ty)::[])
in (_65_25594)::_65_25593))
in (_65_25596)::_65_25595))
in (FSharp_Format.reduce1 _65_25597)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _65_25608 = (let _65_25607 = (FSharp_Format.text "exception")
in (let _65_25606 = (let _65_25605 = (FSharp_Format.text x)
in (_65_25605)::[])
in (_65_25607)::_65_25606))
in (FSharp_Format.reduce1 _65_25608))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_25610 = (let _65_25609 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_25609 args))
in (FSharp_Format.parens _65_25610))
in (let _65_25616 = (let _65_25615 = (FSharp_Format.text "exception")
in (let _65_25614 = (let _65_25613 = (FSharp_Format.text x)
in (let _65_25612 = (let _65_25611 = (FSharp_Format.text "of")
in (_65_25611)::(args)::[])
in (_65_25613)::_65_25612))
in (_65_25615)::_65_25614))
in (FSharp_Format.reduce1 _65_25616))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _65_25624 = (let _65_25623 = (FSharp_Format.text "let")
in (let _65_25622 = (let _65_25621 = (FSharp_Format.text "_")
in (let _65_25620 = (let _65_25619 = (FSharp_Format.text "=")
in (let _65_25618 = (let _65_25617 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_65_25617)::[])
in (_65_25619)::_65_25618))
in (_65_25621)::_65_25620))
in (_65_25623)::_65_25622))
in (FSharp_Format.reduce1 _65_25624))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _64_582 ) -> (match (_64_582) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _64_589 ) -> (match (_64_589) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _65_25643 = (let _65_25642 = (FSharp_Format.text "module")
in (let _65_25641 = (let _65_25640 = (FSharp_Format.text x)
in (let _65_25639 = (let _65_25638 = (FSharp_Format.text ":")
in (let _65_25637 = (let _65_25636 = (FSharp_Format.text "sig")
in (_65_25636)::[])
in (_65_25638)::_65_25637))
in (_65_25640)::_65_25639))
in (_65_25642)::_65_25641))
in (FSharp_Format.reduce1 _65_25643))
in (let tail = (let _65_25645 = (let _65_25644 = (FSharp_Format.text "end")
in (_65_25644)::[])
in (FSharp_Format.reduce1 _65_25645))
in (let doc = (Support.Option.map (fun ( _64_595 ) -> (match (_64_595) with
| (s, _) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _65_25655 = (let _65_25654 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_25653 = (let _65_25652 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_25651 = (let _65_25650 = (FSharp_Format.reduce sub)
in (let _65_25649 = (let _65_25648 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_25648)::[])
in (_65_25650)::_65_25649))
in (_65_25652)::_65_25651))
in (_65_25654)::_65_25653))
in (FSharp_Format.reduce _65_25655)))))))
end))
and for1_mod = (fun ( istop ) ( _64_608 ) -> (match (_64_608) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _64_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _65_25665 = (match ((not (istop))) with
| true -> begin
(let _65_25664 = (FSharp_Format.text "module")
in (let _65_25663 = (let _65_25662 = (FSharp_Format.text x)
in (let _65_25661 = (let _65_25660 = (FSharp_Format.text "=")
in (let _65_25659 = (let _65_25658 = (FSharp_Format.text "struct")
in (_65_25658)::[])
in (_65_25660)::_65_25659))
in (_65_25662)::_65_25661))
in (_65_25664)::_65_25663))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _65_25665))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _65_25667 = (let _65_25666 = (FSharp_Format.text "end")
in (_65_25666)::[])
in (FSharp_Format.reduce1 _65_25667))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _64_616 ) -> (match (_64_616) with
| (_, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _65_25677 = (let _65_25676 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_25675 = (let _65_25674 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_25673 = (let _65_25672 = (FSharp_Format.reduce sub)
in (let _65_25671 = (let _65_25670 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_25670)::[])
in (_65_25672)::_65_25671))
in (_65_25674)::_65_25673))
in (_65_25676)::_65_25675))
in (FSharp_Format.reduce _65_25677))))))))
end))
in (let docs = (Support.List.map (fun ( _64_627 ) -> (match (_64_627) with
| (x, s, m) -> begin
(let _65_25679 = (for1_mod true (x, s, m))
in (x, _65_25679))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))





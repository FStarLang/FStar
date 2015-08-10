
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
(let _70_29224 = (let _70_29223 = (encode_char c)
in (Support.String.strcat "\'" _70_29223))
in (Support.String.strcat _70_29224 "\'"))
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
in (let doc = (let _70_29231 = (let _70_29230 = (let _70_29229 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29229 doc))
in (FSharp_Format.hbox _70_29230))
in (FSharp_Format.parens _70_29231))
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
in (let _70_29234 = (let _70_29233 = (let _70_29232 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29232 args))
in (FSharp_Format.hbox _70_29233))
in (FSharp_Format.parens _70_29234)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_29236 = (let _70_29235 = (as_standard_type name)
in (Support.Option.get _70_29235))
in (Support.Prims.snd _70_29236))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _70_29240 = (let _70_29239 = (let _70_29238 = (let _70_29237 = (FSharp_Format.text name)
in (_70_29237)::[])
in (args)::_70_29238)
in (FSharp_Format.reduce1 _70_29239))
in (FSharp_Format.hbox _70_29240))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _67_146, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_29245 = (let _70_29244 = (let _70_29243 = (let _70_29242 = (let _70_29241 = (FSharp_Format.text " -> ")
in (_70_29241)::(d2)::[])
in (d1)::_70_29242)
in (FSharp_Format.reduce1 _70_29243))
in (FSharp_Format.hbox _70_29244))
in (maybe_paren outer t_prio_fun _70_29245))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_29250 = (let _70_29249 = (let _70_29248 = (let _70_29247 = (let _70_29246 = (FSharp_Format.text " ")
in (_70_29246)::(d1)::[])
in (d2)::_70_29247)
in (FSharp_Format.reduce1 _70_29248))
in (FSharp_Format.hbox _70_29249))
in (maybe_paren outer t_prio_fun _70_29250))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29260 = (let _70_29259 = (let _70_29258 = (FSharp_Format.text "Obj.magic ")
in (_70_29258)::(doc)::[])
in (FSharp_Format.reduce _70_29259))
in (FSharp_Format.parens _70_29260)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_29264 = (let _70_29263 = (let _70_29262 = (FSharp_Format.text ";")
in (_70_29262)::(FSharp_Format.hardline)::[])
in (d)::_70_29263)
in (FSharp_Format.reduce _70_29264))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _70_29265 = (string_of_mlconstant c)
in (FSharp_Format.text _70_29265))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _67_176)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _70_29266 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _70_29266))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_188 ) -> (match (_67_188) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29273 = (let _70_29272 = (let _70_29269 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_29269))
in (let _70_29271 = (let _70_29270 = (FSharp_Format.text "=")
in (_70_29270)::(doc)::[])
in (_70_29272)::_70_29271))
in (FSharp_Format.reduce1 _70_29273)))
end))
in (let _70_29276 = (let _70_29275 = (FSharp_Format.text "; ")
in (let _70_29274 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_29275 _70_29274)))
in (FSharp_Format.cbrackets _70_29276)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29278 = (let _70_29277 = (as_standard_constructor ctor)
in (Support.Option.get _70_29277))
in (Support.Prims.snd _70_29278))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29280 = (let _70_29279 = (as_standard_constructor ctor)
in (Support.Option.get _70_29279))
in (Support.Prims.snd _70_29280))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_29284 = (let _70_29283 = (FSharp_Format.parens x)
in (let _70_29282 = (let _70_29281 = (FSharp_Format.text "::")
in (_70_29281)::(xs)::[])
in (_70_29283)::_70_29282))
in (FSharp_Format.reduce _70_29284))
end
| (_67_207, _67_209) -> begin
(let _70_29290 = (let _70_29289 = (FSharp_Format.text name)
in (let _70_29288 = (let _70_29287 = (let _70_29286 = (let _70_29285 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29285 args))
in (FSharp_Format.parens _70_29286))
in (_70_29287)::[])
in (_70_29289)::_70_29288))
in (FSharp_Format.reduce1 _70_29290))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_29292 = (let _70_29291 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29291 docs))
in (FSharp_Format.parens _70_29292))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _70_29298 = (let _70_29297 = (let _70_29296 = (let _70_29295 = (let _70_29294 = (let _70_29293 = (FSharp_Format.text "in")
in (_70_29293)::(body)::[])
in (FSharp_Format.reduce1 _70_29294))
in (_70_29295)::[])
in (doc)::_70_29296)
in (FSharp_Format.combine FSharp_Format.hardline _70_29297))
in (FSharp_Format.parens _70_29298))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _67_238 = (let _70_29299 = (as_bin_op p)
in (Support.Option.get _70_29299))
in (match (_67_238) with
| (_67_235, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _70_29302 = (let _70_29301 = (let _70_29300 = (FSharp_Format.text txt)
in (_70_29300)::(e2)::[])
in (e1)::_70_29301)
in (FSharp_Format.reduce1 _70_29302))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _67_250 = (let _70_29303 = (as_uni_op p)
in (Support.Option.get _70_29303))
in (match (_67_250) with
| (_67_248, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_29307 = (let _70_29306 = (FSharp_Format.text txt)
in (let _70_29305 = (let _70_29304 = (FSharp_Format.parens e1)
in (_70_29304)::[])
in (_70_29306)::_70_29305))
in (FSharp_Format.reduce1 _70_29307))
in (FSharp_Format.parens doc)))
end))
end
| _67_254 -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _70_29308 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_29308))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _70_29314 = (let _70_29313 = (let _70_29312 = (FSharp_Format.text ".")
in (let _70_29311 = (let _70_29310 = (let _70_29309 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _70_29309))
in (_70_29310)::[])
in (_70_29312)::_70_29311))
in (e)::_70_29313)
in (FSharp_Format.reduce _70_29314))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _67_272 ) -> (match (_67_272) with
| ((x, _67_269), xt) -> begin
(let _70_29327 = (let _70_29326 = (FSharp_Format.text "(")
in (let _70_29325 = (let _70_29324 = (FSharp_Format.text x)
in (let _70_29323 = (let _70_29322 = (match (xt) with
| Some (xxt) -> begin
(let _70_29319 = (let _70_29318 = (FSharp_Format.text " : ")
in (let _70_29317 = (let _70_29316 = (doc_of_mltype outer xxt)
in (_70_29316)::[])
in (_70_29318)::_70_29317))
in (FSharp_Format.reduce1 _70_29319))
end
| _67_276 -> begin
(FSharp_Format.text "")
end)
in (let _70_29321 = (let _70_29320 = (FSharp_Format.text ")")
in (_70_29320)::[])
in (_70_29322)::_70_29321))
in (_70_29324)::_70_29323))
in (_70_29326)::_70_29325))
in (FSharp_Format.reduce1 _70_29327))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _70_29333 = (let _70_29332 = (FSharp_Format.text "fun")
in (let _70_29331 = (let _70_29330 = (FSharp_Format.reduce1 ids)
in (let _70_29329 = (let _70_29328 = (FSharp_Format.text "->")
in (_70_29328)::(body)::[])
in (_70_29330)::_70_29329))
in (_70_29332)::_70_29331))
in (FSharp_Format.reduce1 _70_29333))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_29346 = (let _70_29345 = (let _70_29340 = (let _70_29339 = (FSharp_Format.text "if")
in (let _70_29338 = (let _70_29337 = (let _70_29336 = (FSharp_Format.text "then")
in (let _70_29335 = (let _70_29334 = (FSharp_Format.text "begin")
in (_70_29334)::[])
in (_70_29336)::_70_29335))
in (cond)::_70_29337)
in (_70_29339)::_70_29338))
in (FSharp_Format.reduce1 _70_29340))
in (let _70_29344 = (let _70_29343 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_29342 = (let _70_29341 = (FSharp_Format.text "end")
in (_70_29341)::[])
in (_70_29343)::_70_29342))
in (_70_29345)::_70_29344))
in (FSharp_Format.combine FSharp_Format.hardline _70_29346))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_29369 = (let _70_29368 = (let _70_29353 = (let _70_29352 = (FSharp_Format.text "if")
in (let _70_29351 = (let _70_29350 = (let _70_29349 = (FSharp_Format.text "then")
in (let _70_29348 = (let _70_29347 = (FSharp_Format.text "begin")
in (_70_29347)::[])
in (_70_29349)::_70_29348))
in (cond)::_70_29350)
in (_70_29352)::_70_29351))
in (FSharp_Format.reduce1 _70_29353))
in (let _70_29367 = (let _70_29366 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_29365 = (let _70_29364 = (let _70_29359 = (let _70_29358 = (FSharp_Format.text "end")
in (let _70_29357 = (let _70_29356 = (FSharp_Format.text "else")
in (let _70_29355 = (let _70_29354 = (FSharp_Format.text "begin")
in (_70_29354)::[])
in (_70_29356)::_70_29355))
in (_70_29358)::_70_29357))
in (FSharp_Format.reduce1 _70_29359))
in (let _70_29363 = (let _70_29362 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _70_29361 = (let _70_29360 = (FSharp_Format.text "end")
in (_70_29360)::[])
in (_70_29362)::_70_29361))
in (_70_29364)::_70_29363))
in (_70_29366)::_70_29365))
in (_70_29368)::_70_29367))
in (FSharp_Format.combine FSharp_Format.hardline _70_29369))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _70_29376 = (let _70_29375 = (let _70_29374 = (FSharp_Format.text "match")
in (let _70_29373 = (let _70_29372 = (FSharp_Format.parens cond)
in (let _70_29371 = (let _70_29370 = (FSharp_Format.text "with")
in (_70_29370)::[])
in (_70_29372)::_70_29371))
in (_70_29374)::_70_29373))
in (FSharp_Format.reduce1 _70_29375))
in (_70_29376)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_29381 = (let _70_29380 = (FSharp_Format.text "raise")
in (let _70_29379 = (let _70_29378 = (let _70_29377 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_29377))
in (_70_29378)::[])
in (_70_29380)::_70_29379))
in (FSharp_Format.reduce1 _70_29381))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _70_29390 = (let _70_29389 = (FSharp_Format.text "raise")
in (let _70_29388 = (let _70_29387 = (let _70_29382 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_29382))
in (let _70_29386 = (let _70_29385 = (let _70_29384 = (let _70_29383 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29383 args))
in (FSharp_Format.parens _70_29384))
in (_70_29385)::[])
in (_70_29387)::_70_29386))
in (_70_29389)::_70_29388))
in (FSharp_Format.reduce1 _70_29390)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_29407 = (let _70_29406 = (let _70_29394 = (let _70_29393 = (FSharp_Format.text "try")
in (let _70_29392 = (let _70_29391 = (FSharp_Format.text "begin")
in (_70_29391)::[])
in (_70_29393)::_70_29392))
in (FSharp_Format.reduce1 _70_29394))
in (let _70_29405 = (let _70_29404 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29403 = (let _70_29402 = (let _70_29398 = (let _70_29397 = (FSharp_Format.text "end")
in (let _70_29396 = (let _70_29395 = (FSharp_Format.text "with")
in (_70_29395)::[])
in (_70_29397)::_70_29396))
in (FSharp_Format.reduce1 _70_29398))
in (let _70_29401 = (let _70_29400 = (let _70_29399 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_29399))
in (_70_29400)::[])
in (_70_29402)::_70_29401))
in (_70_29404)::_70_29403))
in (_70_29406)::_70_29405))
in (FSharp_Format.combine FSharp_Format.hardline _70_29407))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _70_29409 = (string_of_mlconstant c)
in (FSharp_Format.text _70_29409))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_329 ) -> (match (_67_329) with
| (name, p) -> begin
(let _70_29418 = (let _70_29417 = (let _70_29412 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_29412))
in (let _70_29416 = (let _70_29415 = (FSharp_Format.text "=")
in (let _70_29414 = (let _70_29413 = (doc_of_pattern p)
in (_70_29413)::[])
in (_70_29415)::_70_29414))
in (_70_29417)::_70_29416))
in (FSharp_Format.reduce1 _70_29418))
end))
in (let _70_29421 = (let _70_29420 = (FSharp_Format.text "; ")
in (let _70_29419 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_29420 _70_29419)))
in (FSharp_Format.cbrackets _70_29421)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29423 = (let _70_29422 = (as_standard_constructor ctor)
in (Support.Option.get _70_29422))
in (Support.Prims.snd _70_29423))
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
(let _70_29425 = (let _70_29424 = (as_standard_constructor ctor)
in (Support.Option.get _70_29424))
in (Support.Prims.snd _70_29425))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_29428 = (let _70_29427 = (let _70_29426 = (FSharp_Format.text "::")
in (_70_29426)::(xs)::[])
in (x)::_70_29427)
in (FSharp_Format.reduce _70_29428))
end
| (_67_347, _67_349) -> begin
(let _70_29434 = (let _70_29433 = (FSharp_Format.text name)
in (let _70_29432 = (let _70_29431 = (let _70_29430 = (let _70_29429 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29429 ps))
in (FSharp_Format.parens _70_29430))
in (_70_29431)::[])
in (_70_29433)::_70_29432))
in (FSharp_Format.reduce1 _70_29434))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _70_29436 = (let _70_29435 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29435 ps))
in (FSharp_Format.parens _70_29436)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_29437 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_29437 ps))))
end))
and doc_of_branch = (fun ( _67_362 ) -> (match (_67_362) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_29442 = (let _70_29441 = (FSharp_Format.text "|")
in (let _70_29440 = (let _70_29439 = (doc_of_pattern p)
in (_70_29439)::[])
in (_70_29441)::_70_29440))
in (FSharp_Format.reduce1 _70_29442))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _70_29448 = (let _70_29447 = (FSharp_Format.text "|")
in (let _70_29446 = (let _70_29445 = (doc_of_pattern p)
in (let _70_29444 = (let _70_29443 = (FSharp_Format.text "when")
in (_70_29443)::(c)::[])
in (_70_29445)::_70_29444))
in (_70_29447)::_70_29446))
in (FSharp_Format.reduce1 _70_29448)))
end)
in (let _70_29459 = (let _70_29458 = (let _70_29453 = (let _70_29452 = (let _70_29451 = (FSharp_Format.text "->")
in (let _70_29450 = (let _70_29449 = (FSharp_Format.text "begin")
in (_70_29449)::[])
in (_70_29451)::_70_29450))
in (case)::_70_29452)
in (FSharp_Format.reduce1 _70_29453))
in (let _70_29457 = (let _70_29456 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29455 = (let _70_29454 = (FSharp_Format.text "end")
in (_70_29454)::[])
in (_70_29456)::_70_29455))
in (_70_29458)::_70_29457))
in (FSharp_Format.combine FSharp_Format.hardline _70_29459)))
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
in (let _70_29469 = (let _70_29468 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _70_29467 = (let _70_29466 = (FSharp_Format.reduce1 ids)
in (let _70_29465 = (let _70_29464 = (FSharp_Format.text "=")
in (_70_29464)::(e)::[])
in (_70_29466)::_70_29465))
in (_70_29468)::_70_29467))
in (FSharp_Format.reduce1 _70_29469))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_29473 = (let _70_29472 = (FSharp_Format.text "let")
in (let _70_29471 = (let _70_29470 = (FSharp_Format.text "rec")
in (_70_29470)::[])
in (_70_29472)::_70_29471))
in (FSharp_Format.reduce1 _70_29473))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_29477 = (let _70_29476 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_29476)::(doc)::[])
in (FSharp_Format.reduce1 _70_29477))) lets)
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
in (let _70_29484 = (let _70_29483 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29483 doc))
in (FSharp_Format.parens _70_29484)))
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
in (let _70_29491 = (let _70_29490 = (let _70_29489 = (FSharp_Format.text ":")
in (_70_29489)::(ty)::[])
in (name)::_70_29490)
in (FSharp_Format.reduce1 _70_29491))))
end))
in (let _70_29494 = (let _70_29493 = (FSharp_Format.text "; ")
in (let _70_29492 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_29493 _70_29492)))
in (FSharp_Format.cbrackets _70_29494)))
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
in (let tys = (let _70_29497 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29497 tys))
in (let _70_29501 = (let _70_29500 = (FSharp_Format.text name)
in (let _70_29499 = (let _70_29498 = (FSharp_Format.text "of")
in (_70_29498)::(tys)::[])
in (_70_29500)::_70_29499))
in (FSharp_Format.reduce1 _70_29501))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_29504 = (let _70_29503 = (FSharp_Format.text "|")
in (_70_29503)::(d)::[])
in (FSharp_Format.reduce1 _70_29504))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_29508 = (let _70_29507 = (let _70_29506 = (let _70_29505 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _70_29505))
in (_70_29506)::[])
in (tparams)::_70_29507)
in (FSharp_Format.reduce1 _70_29508))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_29513 = (let _70_29512 = (let _70_29511 = (let _70_29510 = (let _70_29509 = (FSharp_Format.text "=")
in (_70_29509)::[])
in (doc)::_70_29510)
in (FSharp_Format.reduce1 _70_29511))
in (_70_29512)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_29513)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_29518 = (let _70_29517 = (FSharp_Format.text "type")
in (let _70_29516 = (let _70_29515 = (let _70_29514 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_29514 doc))
in (_70_29515)::[])
in (_70_29517)::_70_29516))
in (FSharp_Format.reduce1 _70_29518))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_29535 = (let _70_29534 = (let _70_29527 = (let _70_29526 = (FSharp_Format.text "module")
in (let _70_29525 = (let _70_29524 = (FSharp_Format.text x)
in (let _70_29523 = (let _70_29522 = (FSharp_Format.text "=")
in (_70_29522)::[])
in (_70_29524)::_70_29523))
in (_70_29526)::_70_29525))
in (FSharp_Format.reduce1 _70_29527))
in (let _70_29533 = (let _70_29532 = (doc_of_sig subsig)
in (let _70_29531 = (let _70_29530 = (let _70_29529 = (let _70_29528 = (FSharp_Format.text "end")
in (_70_29528)::[])
in (FSharp_Format.reduce1 _70_29529))
in (_70_29530)::[])
in (_70_29532)::_70_29531))
in (_70_29534)::_70_29533))
in (FSharp_Format.combine FSharp_Format.hardline _70_29535))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_29539 = (let _70_29538 = (FSharp_Format.text "exception")
in (let _70_29537 = (let _70_29536 = (FSharp_Format.text x)
in (_70_29536)::[])
in (_70_29538)::_70_29537))
in (FSharp_Format.reduce1 _70_29539))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_29541 = (let _70_29540 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29540 args))
in (FSharp_Format.parens _70_29541))
in (let _70_29547 = (let _70_29546 = (FSharp_Format.text "exception")
in (let _70_29545 = (let _70_29544 = (FSharp_Format.text x)
in (let _70_29543 = (let _70_29542 = (FSharp_Format.text "of")
in (_70_29542)::(args)::[])
in (_70_29544)::_70_29543))
in (_70_29546)::_70_29545))
in (FSharp_Format.reduce1 _70_29547))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_67_452, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _70_29553 = (let _70_29552 = (FSharp_Format.text "val")
in (let _70_29551 = (let _70_29550 = (FSharp_Format.text x)
in (let _70_29549 = (let _70_29548 = (FSharp_Format.text ": ")
in (_70_29548)::(ty)::[])
in (_70_29550)::_70_29549))
in (_70_29552)::_70_29551))
in (FSharp_Format.reduce1 _70_29553)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_29561 = (let _70_29560 = (FSharp_Format.text "exception")
in (let _70_29559 = (let _70_29558 = (FSharp_Format.text x)
in (_70_29558)::[])
in (_70_29560)::_70_29559))
in (FSharp_Format.reduce1 _70_29561))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_29563 = (let _70_29562 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29562 args))
in (FSharp_Format.parens _70_29563))
in (let _70_29569 = (let _70_29568 = (FSharp_Format.text "exception")
in (let _70_29567 = (let _70_29566 = (FSharp_Format.text x)
in (let _70_29565 = (let _70_29564 = (FSharp_Format.text "of")
in (_70_29564)::(args)::[])
in (_70_29566)::_70_29565))
in (_70_29568)::_70_29567))
in (FSharp_Format.reduce1 _70_29569))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _70_29577 = (let _70_29576 = (FSharp_Format.text "let")
in (let _70_29575 = (let _70_29574 = (FSharp_Format.text "_")
in (let _70_29573 = (let _70_29572 = (FSharp_Format.text "=")
in (let _70_29571 = (let _70_29570 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_70_29570)::[])
in (_70_29572)::_70_29571))
in (_70_29574)::_70_29573))
in (_70_29576)::_70_29575))
in (FSharp_Format.reduce1 _70_29577))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _67_488 ) -> (match (_67_488) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _67_495 ) -> (match (_67_495) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_29594 = (let _70_29593 = (FSharp_Format.text "module")
in (let _70_29592 = (let _70_29591 = (FSharp_Format.text x)
in (let _70_29590 = (let _70_29589 = (FSharp_Format.text ":")
in (let _70_29588 = (let _70_29587 = (FSharp_Format.text "sig")
in (_70_29587)::[])
in (_70_29589)::_70_29588))
in (_70_29591)::_70_29590))
in (_70_29593)::_70_29592))
in (FSharp_Format.reduce1 _70_29594))
in (let tail = (let _70_29596 = (let _70_29595 = (FSharp_Format.text "end")
in (_70_29595)::[])
in (FSharp_Format.reduce1 _70_29596))
in (let doc = (Support.Option.map (fun ( _67_501 ) -> (match (_67_501) with
| (s, _67_500) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_29606 = (let _70_29605 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_29604 = (let _70_29603 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_29602 = (let _70_29601 = (FSharp_Format.reduce sub)
in (let _70_29600 = (let _70_29599 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_29599)::[])
in (_70_29601)::_70_29600))
in (_70_29603)::_70_29602))
in (_70_29605)::_70_29604))
in (FSharp_Format.reduce _70_29606)))))))
end))
and for1_mod = (fun ( istop ) ( _67_514 ) -> (match (_67_514) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _67_515 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_29616 = (match ((not (istop))) with
| true -> begin
(let _70_29615 = (FSharp_Format.text "module")
in (let _70_29614 = (let _70_29613 = (FSharp_Format.text x)
in (let _70_29612 = (let _70_29611 = (FSharp_Format.text "=")
in (let _70_29610 = (let _70_29609 = (FSharp_Format.text "struct")
in (_70_29609)::[])
in (_70_29611)::_70_29610))
in (_70_29613)::_70_29612))
in (_70_29615)::_70_29614))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_29616))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_29618 = (let _70_29617 = (FSharp_Format.text "end")
in (_70_29617)::[])
in (FSharp_Format.reduce1 _70_29618))
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
in (let _70_29628 = (let _70_29627 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_29626 = (let _70_29625 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_29624 = (let _70_29623 = (FSharp_Format.reduce sub)
in (let _70_29622 = (let _70_29621 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_29621)::[])
in (_70_29623)::_70_29622))
in (_70_29625)::_70_29624))
in (_70_29627)::_70_29626))
in (FSharp_Format.reduce _70_29628))))))))
end))
in (let docs = (Support.List.map (fun ( _67_533 ) -> (match (_67_533) with
| (x, s, m) -> begin
(let _70_29630 = (for1_mod true (x, s, m))
in (x, _70_29630))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))






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
(let _70_29219 = (let _70_29218 = (encode_char c)
in (Support.String.strcat "\'" _70_29218))
in (Support.String.strcat _70_29219 "\'"))
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
in (let doc = (let _70_29226 = (let _70_29225 = (let _70_29224 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29224 doc))
in (FSharp_Format.hbox _70_29225))
in (FSharp_Format.parens _70_29226))
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
in (let _70_29229 = (let _70_29228 = (let _70_29227 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29227 args))
in (FSharp_Format.hbox _70_29228))
in (FSharp_Format.parens _70_29229)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_29231 = (let _70_29230 = (as_standard_type name)
in (Support.Option.get _70_29230))
in (Support.Prims.snd _70_29231))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptsym name)
end)
in (let _70_29235 = (let _70_29234 = (let _70_29233 = (let _70_29232 = (FSharp_Format.text name)
in (_70_29232)::[])
in (args)::_70_29233)
in (FSharp_Format.reduce1 _70_29234))
in (FSharp_Format.hbox _70_29235))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _67_146, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_29240 = (let _70_29239 = (let _70_29238 = (let _70_29237 = (let _70_29236 = (FSharp_Format.text " -> ")
in (_70_29236)::(d2)::[])
in (d1)::_70_29237)
in (FSharp_Format.reduce1 _70_29238))
in (FSharp_Format.hbox _70_29239))
in (maybe_paren outer t_prio_fun _70_29240))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype (t_prio_fun, Right) t2)
in (let _70_29245 = (let _70_29244 = (let _70_29243 = (let _70_29242 = (let _70_29241 = (FSharp_Format.text " ")
in (_70_29241)::(d1)::[])
in (d2)::_70_29242)
in (FSharp_Format.reduce1 _70_29243))
in (FSharp_Format.hbox _70_29244))
in (maybe_paren outer t_prio_fun _70_29245))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))

let rec doc_of_expr = (fun ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29255 = (let _70_29254 = (let _70_29253 = (FSharp_Format.text "Obj.magic ")
in (_70_29253)::(doc)::[])
in (FSharp_Format.reduce _70_29254))
in (FSharp_Format.parens _70_29255)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_29259 = (let _70_29258 = (let _70_29257 = (FSharp_Format.text ";")
in (_70_29257)::(FSharp_Format.hardline)::[])
in (d)::_70_29258)
in (FSharp_Format.reduce _70_29259))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _70_29260 = (string_of_mlconstant c)
in (FSharp_Format.text _70_29260))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _67_176)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _70_29261 = (Microsoft_FStar_Backends_ML_Syntax.ptsym path)
in (FSharp_Format.text _70_29261))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_188 ) -> (match (_67_188) with
| (name, e) -> begin
(let doc = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29268 = (let _70_29267 = (let _70_29264 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_29264))
in (let _70_29266 = (let _70_29265 = (FSharp_Format.text "=")
in (_70_29265)::(doc)::[])
in (_70_29267)::_70_29266))
in (FSharp_Format.reduce1 _70_29268)))
end))
in (let _70_29271 = (let _70_29270 = (FSharp_Format.text "; ")
in (let _70_29269 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_29270 _70_29269)))
in (FSharp_Format.cbrackets _70_29271)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29273 = (let _70_29272 = (as_standard_constructor ctor)
in (Support.Option.get _70_29272))
in (Support.Prims.snd _70_29273))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29275 = (let _70_29274 = (as_standard_constructor ctor)
in (Support.Option.get _70_29274))
in (Support.Prims.snd _70_29275))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_29279 = (let _70_29278 = (FSharp_Format.parens x)
in (let _70_29277 = (let _70_29276 = (FSharp_Format.text "::")
in (_70_29276)::(xs)::[])
in (_70_29278)::_70_29277))
in (FSharp_Format.reduce _70_29279))
end
| (_67_207, _67_209) -> begin
(let _70_29285 = (let _70_29284 = (FSharp_Format.text name)
in (let _70_29283 = (let _70_29282 = (let _70_29281 = (let _70_29280 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29280 args))
in (FSharp_Format.parens _70_29281))
in (_70_29282)::[])
in (_70_29284)::_70_29283))
in (FSharp_Format.reduce1 _70_29285))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_29287 = (let _70_29286 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29286 docs))
in (FSharp_Format.parens _70_29287))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets (rec_, lets))
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let _70_29293 = (let _70_29292 = (let _70_29291 = (let _70_29290 = (let _70_29289 = (let _70_29288 = (FSharp_Format.text "in")
in (_70_29288)::(body)::[])
in (FSharp_Format.reduce1 _70_29289))
in (_70_29290)::[])
in (doc)::_70_29291)
in (FSharp_Format.combine FSharp_Format.hardline _70_29292))
in (FSharp_Format.parens _70_29293))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_App ((e, args)) -> begin
(match ((e, args)) with
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::e2::[]) when (is_bin_op p) -> begin
(let _67_238 = (let _70_29294 = (as_bin_op p)
in (Support.Option.get _70_29294))
in (match (_67_238) with
| (_67_235, prio, txt) -> begin
(let e1 = (doc_of_expr (prio, Left) e1)
in (let e2 = (doc_of_expr (prio, Right) e2)
in (let doc = (let _70_29297 = (let _70_29296 = (let _70_29295 = (FSharp_Format.text txt)
in (_70_29295)::(e2)::[])
in (e1)::_70_29296)
in (FSharp_Format.reduce1 _70_29297))
in (FSharp_Format.parens doc))))
end))
end
| (Microsoft_FStar_Backends_ML_Syntax.MLE_Name (p), e1::[]) when (is_uni_op p) -> begin
(let _67_250 = (let _70_29298 = (as_uni_op p)
in (Support.Option.get _70_29298))
in (match (_67_250) with
| (_67_248, txt) -> begin
(let e1 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_29302 = (let _70_29301 = (FSharp_Format.text txt)
in (let _70_29300 = (let _70_29299 = (FSharp_Format.parens e1)
in (_70_29299)::[])
in (_70_29301)::_70_29300))
in (FSharp_Format.reduce1 _70_29302))
in (FSharp_Format.parens doc)))
end))
end
| _67_254 -> begin
(let e = (doc_of_expr (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr (e_app_prio, IRight)) args)
in (let _70_29303 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_29303))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let doc = (let _70_29309 = (let _70_29308 = (let _70_29307 = (FSharp_Format.text ".")
in (let _70_29306 = (let _70_29305 = (let _70_29304 = (Microsoft_FStar_Backends_ML_Syntax.ptsym f)
in (FSharp_Format.text _70_29304))
in (_70_29305)::[])
in (_70_29307)::_70_29306))
in (e)::_70_29308)
in (FSharp_Format.reduce _70_29309))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _67_272 ) -> (match (_67_272) with
| ((x, _67_269), xt) -> begin
(let _70_29322 = (let _70_29321 = (FSharp_Format.text "(")
in (let _70_29320 = (let _70_29319 = (FSharp_Format.text x)
in (let _70_29318 = (let _70_29317 = (match (xt) with
| Some (xxt) -> begin
(let _70_29314 = (let _70_29313 = (FSharp_Format.text " : ")
in (let _70_29312 = (let _70_29311 = (doc_of_mltype outer xxt)
in (_70_29311)::[])
in (_70_29313)::_70_29312))
in (FSharp_Format.reduce1 _70_29314))
end
| _67_276 -> begin
(FSharp_Format.text "")
end)
in (let _70_29316 = (let _70_29315 = (FSharp_Format.text ")")
in (_70_29315)::[])
in (_70_29317)::_70_29316))
in (_70_29319)::_70_29318))
in (_70_29321)::_70_29320))
in (FSharp_Format.reduce1 _70_29322))
end)) ids)
in (let body = (doc_of_expr (min_op_prec, NonAssoc) body)
in (let doc = (let _70_29328 = (let _70_29327 = (FSharp_Format.text "fun")
in (let _70_29326 = (let _70_29325 = (FSharp_Format.reduce1 ids)
in (let _70_29324 = (let _70_29323 = (FSharp_Format.text "->")
in (_70_29323)::(body)::[])
in (_70_29325)::_70_29324))
in (_70_29327)::_70_29326))
in (FSharp_Format.reduce1 _70_29328))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_29341 = (let _70_29340 = (let _70_29335 = (let _70_29334 = (FSharp_Format.text "if")
in (let _70_29333 = (let _70_29332 = (let _70_29331 = (FSharp_Format.text "then")
in (let _70_29330 = (let _70_29329 = (FSharp_Format.text "begin")
in (_70_29329)::[])
in (_70_29331)::_70_29330))
in (cond)::_70_29332)
in (_70_29334)::_70_29333))
in (FSharp_Format.reduce1 _70_29335))
in (let _70_29339 = (let _70_29338 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_29337 = (let _70_29336 = (FSharp_Format.text "end")
in (_70_29336)::[])
in (_70_29338)::_70_29337))
in (_70_29340)::_70_29339))
in (FSharp_Format.combine FSharp_Format.hardline _70_29341))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_29364 = (let _70_29363 = (let _70_29348 = (let _70_29347 = (FSharp_Format.text "if")
in (let _70_29346 = (let _70_29345 = (let _70_29344 = (FSharp_Format.text "then")
in (let _70_29343 = (let _70_29342 = (FSharp_Format.text "begin")
in (_70_29342)::[])
in (_70_29344)::_70_29343))
in (cond)::_70_29345)
in (_70_29347)::_70_29346))
in (FSharp_Format.reduce1 _70_29348))
in (let _70_29362 = (let _70_29361 = (doc_of_expr (min_op_prec, NonAssoc) e1)
in (let _70_29360 = (let _70_29359 = (let _70_29354 = (let _70_29353 = (FSharp_Format.text "end")
in (let _70_29352 = (let _70_29351 = (FSharp_Format.text "else")
in (let _70_29350 = (let _70_29349 = (FSharp_Format.text "begin")
in (_70_29349)::[])
in (_70_29351)::_70_29350))
in (_70_29353)::_70_29352))
in (FSharp_Format.reduce1 _70_29354))
in (let _70_29358 = (let _70_29357 = (doc_of_expr (min_op_prec, NonAssoc) e2)
in (let _70_29356 = (let _70_29355 = (FSharp_Format.text "end")
in (_70_29355)::[])
in (_70_29357)::_70_29356))
in (_70_29359)::_70_29358))
in (_70_29361)::_70_29360))
in (_70_29363)::_70_29362))
in (FSharp_Format.combine FSharp_Format.hardline _70_29364))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map doc_of_branch pats)
in (let doc = (let _70_29371 = (let _70_29370 = (let _70_29369 = (FSharp_Format.text "match")
in (let _70_29368 = (let _70_29367 = (FSharp_Format.parens cond)
in (let _70_29366 = (let _70_29365 = (FSharp_Format.text "with")
in (_70_29365)::[])
in (_70_29367)::_70_29366))
in (_70_29369)::_70_29368))
in (FSharp_Format.reduce1 _70_29370))
in (_70_29371)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_29376 = (let _70_29375 = (FSharp_Format.text "raise")
in (let _70_29374 = (let _70_29373 = (let _70_29372 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_29372))
in (_70_29373)::[])
in (_70_29375)::_70_29374))
in (FSharp_Format.reduce1 _70_29376))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr (min_op_prec, NonAssoc)) args)
in (let _70_29385 = (let _70_29384 = (FSharp_Format.text "raise")
in (let _70_29383 = (let _70_29382 = (let _70_29377 = (Microsoft_FStar_Backends_ML_Syntax.ptctor exn)
in (FSharp_Format.text _70_29377))
in (let _70_29381 = (let _70_29380 = (let _70_29379 = (let _70_29378 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29378 args))
in (FSharp_Format.parens _70_29379))
in (_70_29380)::[])
in (_70_29382)::_70_29381))
in (_70_29384)::_70_29383))
in (FSharp_Format.reduce1 _70_29385)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_29402 = (let _70_29401 = (let _70_29389 = (let _70_29388 = (FSharp_Format.text "try")
in (let _70_29387 = (let _70_29386 = (FSharp_Format.text "begin")
in (_70_29386)::[])
in (_70_29388)::_70_29387))
in (FSharp_Format.reduce1 _70_29389))
in (let _70_29400 = (let _70_29399 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29398 = (let _70_29397 = (let _70_29393 = (let _70_29392 = (FSharp_Format.text "end")
in (let _70_29391 = (let _70_29390 = (FSharp_Format.text "with")
in (_70_29390)::[])
in (_70_29392)::_70_29391))
in (FSharp_Format.reduce1 _70_29393))
in (let _70_29396 = (let _70_29395 = (let _70_29394 = (Support.List.map doc_of_branch pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_29394))
in (_70_29395)::[])
in (_70_29397)::_70_29396))
in (_70_29399)::_70_29398))
in (_70_29401)::_70_29400))
in (FSharp_Format.combine FSharp_Format.hardline _70_29402))
end))
and doc_of_pattern = (fun ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _70_29404 = (string_of_mlconstant c)
in (FSharp_Format.text _70_29404))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _67_329 ) -> (match (_67_329) with
| (name, p) -> begin
(let _70_29413 = (let _70_29412 = (let _70_29407 = (Microsoft_FStar_Backends_ML_Syntax.ptsym (path, name))
in (FSharp_Format.text _70_29407))
in (let _70_29411 = (let _70_29410 = (FSharp_Format.text "=")
in (let _70_29409 = (let _70_29408 = (doc_of_pattern p)
in (_70_29408)::[])
in (_70_29410)::_70_29409))
in (_70_29412)::_70_29411))
in (FSharp_Format.reduce1 _70_29413))
end))
in (let _70_29416 = (let _70_29415 = (FSharp_Format.text "; ")
in (let _70_29414 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_29415 _70_29414)))
in (FSharp_Format.cbrackets _70_29416)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_29418 = (let _70_29417 = (as_standard_constructor ctor)
in (Support.Option.get _70_29417))
in (Support.Prims.snd _70_29418))
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
(let _70_29420 = (let _70_29419 = (as_standard_constructor ctor)
in (Support.Option.get _70_29419))
in (Support.Prims.snd _70_29420))
end
| false -> begin
(Microsoft_FStar_Backends_ML_Syntax.ptctor ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_29423 = (let _70_29422 = (let _70_29421 = (FSharp_Format.text "::")
in (_70_29421)::(xs)::[])
in (x)::_70_29422)
in (FSharp_Format.reduce _70_29423))
end
| (_67_347, _67_349) -> begin
(let _70_29429 = (let _70_29428 = (FSharp_Format.text name)
in (let _70_29427 = (let _70_29426 = (let _70_29425 = (let _70_29424 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29424 ps))
in (FSharp_Format.parens _70_29425))
in (_70_29426)::[])
in (_70_29428)::_70_29427))
in (FSharp_Format.reduce1 _70_29429))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let _70_29431 = (let _70_29430 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29430 ps))
in (FSharp_Format.parens _70_29431)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map doc_of_pattern ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_29432 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_29432 ps))))
end))
and doc_of_branch = (fun ( _67_362 ) -> (match (_67_362) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_29437 = (let _70_29436 = (FSharp_Format.text "|")
in (let _70_29435 = (let _70_29434 = (doc_of_pattern p)
in (_70_29434)::[])
in (_70_29436)::_70_29435))
in (FSharp_Format.reduce1 _70_29437))
end
| Some (c) -> begin
(let c = (doc_of_expr (min_op_prec, NonAssoc) c)
in (let _70_29443 = (let _70_29442 = (FSharp_Format.text "|")
in (let _70_29441 = (let _70_29440 = (doc_of_pattern p)
in (let _70_29439 = (let _70_29438 = (FSharp_Format.text "when")
in (_70_29438)::(c)::[])
in (_70_29440)::_70_29439))
in (_70_29442)::_70_29441))
in (FSharp_Format.reduce1 _70_29443)))
end)
in (let _70_29454 = (let _70_29453 = (let _70_29448 = (let _70_29447 = (let _70_29446 = (FSharp_Format.text "->")
in (let _70_29445 = (let _70_29444 = (FSharp_Format.text "begin")
in (_70_29444)::[])
in (_70_29446)::_70_29445))
in (case)::_70_29447)
in (FSharp_Format.reduce1 _70_29448))
in (let _70_29452 = (let _70_29451 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (let _70_29450 = (let _70_29449 = (FSharp_Format.text "end")
in (_70_29449)::[])
in (_70_29451)::_70_29450))
in (_70_29453)::_70_29452))
in (FSharp_Format.combine FSharp_Format.hardline _70_29454)))
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
in (let _70_29464 = (let _70_29463 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _70_29462 = (let _70_29461 = (FSharp_Format.reduce1 ids)
in (let _70_29460 = (let _70_29459 = (FSharp_Format.text "=")
in (_70_29459)::(e)::[])
in (_70_29461)::_70_29460))
in (_70_29463)::_70_29462))
in (FSharp_Format.reduce1 _70_29464))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_29468 = (let _70_29467 = (FSharp_Format.text "let")
in (let _70_29466 = (let _70_29465 = (FSharp_Format.text "rec")
in (_70_29465)::[])
in (_70_29467)::_70_29466))
in (FSharp_Format.reduce1 _70_29468))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_29472 = (let _70_29471 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_29471)::(doc)::[])
in (FSharp_Format.reduce1 _70_29472))) lets)
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
in (let _70_29479 = (let _70_29478 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_29478 doc))
in (FSharp_Format.parens _70_29479)))
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
in (let _70_29486 = (let _70_29485 = (let _70_29484 = (FSharp_Format.text ":")
in (_70_29484)::(ty)::[])
in (name)::_70_29485)
in (FSharp_Format.reduce1 _70_29486))))
end))
in (let _70_29489 = (let _70_29488 = (FSharp_Format.text "; ")
in (let _70_29487 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_29488 _70_29487)))
in (FSharp_Format.cbrackets _70_29489)))
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
in (let tys = (let _70_29492 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29492 tys))
in (let _70_29496 = (let _70_29495 = (FSharp_Format.text name)
in (let _70_29494 = (let _70_29493 = (FSharp_Format.text "of")
in (_70_29493)::(tys)::[])
in (_70_29495)::_70_29494))
in (FSharp_Format.reduce1 _70_29496))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_29499 = (let _70_29498 = (FSharp_Format.text "|")
in (_70_29498)::(d)::[])
in (FSharp_Format.reduce1 _70_29499))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_29503 = (let _70_29502 = (let _70_29501 = (let _70_29500 = (Microsoft_FStar_Backends_ML_Syntax.ptsym ([], x))
in (FSharp_Format.text _70_29500))
in (_70_29501)::[])
in (tparams)::_70_29502)
in (FSharp_Format.reduce1 _70_29503))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_29508 = (let _70_29507 = (let _70_29506 = (let _70_29505 = (let _70_29504 = (FSharp_Format.text "=")
in (_70_29504)::[])
in (doc)::_70_29505)
in (FSharp_Format.reduce1 _70_29506))
in (_70_29507)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_29508)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_29513 = (let _70_29512 = (FSharp_Format.text "type")
in (let _70_29511 = (let _70_29510 = (let _70_29509 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_29509 doc))
in (_70_29510)::[])
in (_70_29512)::_70_29511))
in (FSharp_Format.reduce1 _70_29513))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_29530 = (let _70_29529 = (let _70_29522 = (let _70_29521 = (FSharp_Format.text "module")
in (let _70_29520 = (let _70_29519 = (FSharp_Format.text x)
in (let _70_29518 = (let _70_29517 = (FSharp_Format.text "=")
in (_70_29517)::[])
in (_70_29519)::_70_29518))
in (_70_29521)::_70_29520))
in (FSharp_Format.reduce1 _70_29522))
in (let _70_29528 = (let _70_29527 = (doc_of_sig subsig)
in (let _70_29526 = (let _70_29525 = (let _70_29524 = (let _70_29523 = (FSharp_Format.text "end")
in (_70_29523)::[])
in (FSharp_Format.reduce1 _70_29524))
in (_70_29525)::[])
in (_70_29527)::_70_29526))
in (_70_29529)::_70_29528))
in (FSharp_Format.combine FSharp_Format.hardline _70_29530))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_29534 = (let _70_29533 = (FSharp_Format.text "exception")
in (let _70_29532 = (let _70_29531 = (FSharp_Format.text x)
in (_70_29531)::[])
in (_70_29533)::_70_29532))
in (FSharp_Format.reduce1 _70_29534))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_29536 = (let _70_29535 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29535 args))
in (FSharp_Format.parens _70_29536))
in (let _70_29542 = (let _70_29541 = (FSharp_Format.text "exception")
in (let _70_29540 = (let _70_29539 = (FSharp_Format.text x)
in (let _70_29538 = (let _70_29537 = (FSharp_Format.text "of")
in (_70_29537)::(args)::[])
in (_70_29539)::_70_29538))
in (_70_29541)::_70_29540))
in (FSharp_Format.reduce1 _70_29542))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_67_452, ty))) -> begin
(let ty = (doc_of_mltype (min_op_prec, NonAssoc) ty)
in (let _70_29548 = (let _70_29547 = (FSharp_Format.text "val")
in (let _70_29546 = (let _70_29545 = (FSharp_Format.text x)
in (let _70_29544 = (let _70_29543 = (FSharp_Format.text ": ")
in (_70_29543)::(ty)::[])
in (_70_29545)::_70_29544))
in (_70_29547)::_70_29546))
in (FSharp_Format.reduce1 _70_29548)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl decls)
end))
and doc_of_sig = (fun ( s ) -> (let docs = (Support.List.map doc_of_sig1 s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_29556 = (let _70_29555 = (FSharp_Format.text "exception")
in (let _70_29554 = (let _70_29553 = (FSharp_Format.text x)
in (_70_29553)::[])
in (_70_29555)::_70_29554))
in (FSharp_Format.reduce1 _70_29556))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype (min_op_prec, NonAssoc)) args)
in (let args = (let _70_29558 = (let _70_29557 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_29557 args))
in (FSharp_Format.parens _70_29558))
in (let _70_29564 = (let _70_29563 = (FSharp_Format.text "exception")
in (let _70_29562 = (let _70_29561 = (FSharp_Format.text x)
in (let _70_29560 = (let _70_29559 = (FSharp_Format.text "of")
in (_70_29559)::(args)::[])
in (_70_29561)::_70_29560))
in (_70_29563)::_70_29562))
in (FSharp_Format.reduce1 _70_29564))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _70_29572 = (let _70_29571 = (FSharp_Format.text "let")
in (let _70_29570 = (let _70_29569 = (FSharp_Format.text "_")
in (let _70_29568 = (let _70_29567 = (FSharp_Format.text "=")
in (let _70_29566 = (let _70_29565 = (doc_of_expr (min_op_prec, NonAssoc) e)
in (_70_29565)::[])
in (_70_29567)::_70_29566))
in (_70_29569)::_70_29568))
in (_70_29571)::_70_29570))
in (FSharp_Format.reduce1 _70_29572))
end))

let doc_of_mod = (fun ( m ) -> (let docs = (Support.List.map doc_of_mod1 m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _67_488 ) -> (match (_67_488) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _67_495 ) -> (match (_67_495) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_29589 = (let _70_29588 = (FSharp_Format.text "module")
in (let _70_29587 = (let _70_29586 = (FSharp_Format.text x)
in (let _70_29585 = (let _70_29584 = (FSharp_Format.text ":")
in (let _70_29583 = (let _70_29582 = (FSharp_Format.text "sig")
in (_70_29582)::[])
in (_70_29584)::_70_29583))
in (_70_29586)::_70_29585))
in (_70_29588)::_70_29587))
in (FSharp_Format.reduce1 _70_29589))
in (let tail = (let _70_29591 = (let _70_29590 = (FSharp_Format.text "end")
in (_70_29590)::[])
in (FSharp_Format.reduce1 _70_29591))
in (let doc = (Support.Option.map (fun ( _67_501 ) -> (match (_67_501) with
| (s, _67_500) -> begin
(doc_of_sig s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_29601 = (let _70_29600 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_29599 = (let _70_29598 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_29597 = (let _70_29596 = (FSharp_Format.reduce sub)
in (let _70_29595 = (let _70_29594 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_29594)::[])
in (_70_29596)::_70_29595))
in (_70_29598)::_70_29597))
in (_70_29600)::_70_29599))
in (FSharp_Format.reduce _70_29601)))))))
end))
and for1_mod = (fun ( istop ) ( _67_514 ) -> (match (_67_514) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _67_515 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_29611 = (match ((not (istop))) with
| true -> begin
(let _70_29610 = (FSharp_Format.text "module")
in (let _70_29609 = (let _70_29608 = (FSharp_Format.text x)
in (let _70_29607 = (let _70_29606 = (FSharp_Format.text "=")
in (let _70_29605 = (let _70_29604 = (FSharp_Format.text "struct")
in (_70_29604)::[])
in (_70_29606)::_70_29605))
in (_70_29608)::_70_29607))
in (_70_29610)::_70_29609))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_29611))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_29613 = (let _70_29612 = (FSharp_Format.text "end")
in (_70_29612)::[])
in (FSharp_Format.reduce1 _70_29613))
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
in (let _70_29623 = (let _70_29622 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_29621 = (let _70_29620 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_29619 = (let _70_29618 = (FSharp_Format.reduce sub)
in (let _70_29617 = (let _70_29616 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_29616)::[])
in (_70_29618)::_70_29617))
in (_70_29620)::_70_29619))
in (_70_29622)::_70_29621))
in (FSharp_Format.reduce _70_29623))))))))
end))
in (let docs = (Support.List.map (fun ( _67_533 ) -> (match (_67_533) with
| (x, s, m) -> begin
(let _70_29625 = (for1_mod true (x, s, m))
in (x, _70_29625))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))





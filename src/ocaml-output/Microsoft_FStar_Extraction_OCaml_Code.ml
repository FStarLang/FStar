
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

let outmod = (("Prims")::[])::(("System")::[])::(("ST")::[])::(("Option")::[])::(("String")::[])::(("Char")::[])::(("Bytes")::[])::(("List")::[])::(("Array")::[])::(("Map")::[])::(("DST")::[])::(("IO")::[])::(("Tcp")::[])::(("Crypto")::[])::(("Collections")::[])::(("Microsoft")::("FStar")::("Bytes")::[])::(("Microsoft")::("FStar")::("Platform")::[])::(("Microsoft")::("FStar")::("Util")::[])::(("Microsoft")::("FStar")::("Getopt")::[])::(("Microsoft")::("FStar")::("Unionfind")::[])::(("Microsoft")::("FStar")::("Range")::[])::(("Microsoft")::("FStar")::("Parser")::("Util")::[])::[]

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
(match ((let _68_24321 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _68_24321))) with
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
| _ -> begin
(let _57_46 = x
in (match (_57_46) with
| (ns, x) -> begin
(let _68_24326 = (path_of_ns currentModule ns)
in (_68_24326, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _68_24329 = (Support.String.get s 0)
in (Support.Char.lowercase _68_24329)) <> (Support.String.get s 0))) with
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
(let _57_52 = (mlpath_of_mlpath currentModule mlp)
in (match (_57_52) with
| (p, s) -> begin
(let _68_24336 = (let _68_24335 = (let _68_24334 = (ptsym_of_symbol s)
in (_68_24334)::[])
in (Support.List.append p _68_24335))
in (Support.String.concat "." _68_24336))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _57_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_57_57) with
| (p, s) -> begin
(let s = (match (((let _68_24341 = (Support.String.get s 0)
in (Support.Char.uppercase _68_24341)) <> (Support.String.get s 0))) with
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

let as_bin_op = (fun ( _57_62 ) -> (match (_57_62) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _57_68 ) -> (match (_57_68) with
| (y, _, _) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _57_72 ) -> (match (_57_72) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _57_76 ) -> (match (_57_76) with
| (y, _) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _57_80 ) -> (match (_57_80) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _57_84 ) -> (match (_57_84) with
| (y, _) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _57_88 ) -> (match (_57_88) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _57_92 ) -> (match (_57_92) with
| (y, _) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _57_96 ) ( inner ) ( doc ) -> (match (_57_96) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _57_105 = _inner
in (match (_57_105) with
| (pi, fi) -> begin
(let _57_108 = _outer
in (match (_57_108) with
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
(let _68_24383 = (let _68_24382 = (encode_char c)
in (Support.String.strcat "\'" _68_24382))
in (Support.String.strcat _68_24383 "\'"))
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
in (let _68_24395 = (Support.Prims.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _68_24395)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _68_24398 = (let _68_24397 = (let _68_24396 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24396 doc))
in (FSharp_Format.hbox _68_24397))
in (FSharp_Format.parens _68_24398))
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
| _ -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _68_24401 = (let _68_24400 = (let _68_24399 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24399 args))
in (FSharp_Format.hbox _68_24400))
in (FSharp_Format.parens _68_24401)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _68_24403 = (let _68_24402 = (as_standard_type name)
in (Support.Option.get _68_24402))
in (Support.Prims.snd _68_24403))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _68_24407 = (let _68_24406 = (let _68_24405 = (let _68_24404 = (FSharp_Format.text name)
in (_68_24404)::[])
in (args)::_68_24405)
in (FSharp_Format.reduce1 _68_24406))
in (FSharp_Format.hbox _68_24407))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _68_24412 = (let _68_24411 = (let _68_24410 = (let _68_24409 = (let _68_24408 = (FSharp_Format.text " -> ")
in (_68_24408)::(d2)::[])
in (d1)::_68_24409)
in (FSharp_Format.reduce1 _68_24410))
in (FSharp_Format.hbox _68_24411))
in (maybe_paren outer t_prio_fun _68_24412))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _68_24417 = (let _68_24416 = (let _68_24415 = (let _68_24414 = (let _68_24413 = (FSharp_Format.text " ")
in (_68_24413)::(d1)::[])
in (d2)::_68_24414)
in (FSharp_Format.reduce1 _68_24415))
in (FSharp_Format.hbox _68_24416))
in (maybe_paren outer t_prio_fun _68_24417))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24442 = (let _68_24441 = (let _68_24440 = (FSharp_Format.text "Obj.magic ")
in (_68_24440)::(doc)::[])
in (FSharp_Format.reduce _68_24441))
in (FSharp_Format.parens _68_24442)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _68_24446 = (let _68_24445 = (let _68_24444 = (FSharp_Format.text ";")
in (_68_24444)::(FSharp_Format.hardline)::[])
in (d)::_68_24445)
in (FSharp_Format.reduce _68_24446))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _68_24447 = (string_of_mlconstant c)
in (FSharp_Format.text _68_24447))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _68_24448 = (ptsym currentModule path)
in (FSharp_Format.text _68_24448))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _57_250 ) -> (match (_57_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24455 = (let _68_24454 = (let _68_24451 = (ptsym currentModule (path, name))
in (FSharp_Format.text _68_24451))
in (let _68_24453 = (let _68_24452 = (FSharp_Format.text "=")
in (_68_24452)::(doc)::[])
in (_68_24454)::_68_24453))
in (FSharp_Format.reduce1 _68_24455)))
end))
in (let _68_24458 = (let _68_24457 = (FSharp_Format.text "; ")
in (let _68_24456 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_24457 _68_24456)))
in (FSharp_Format.cbrackets _68_24458)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24460 = (let _68_24459 = (as_standard_constructor ctor)
in (Support.Option.get _68_24459))
in (Support.Prims.snd _68_24460))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24462 = (let _68_24461 = (as_standard_constructor ctor)
in (Support.Option.get _68_24461))
in (Support.Prims.snd _68_24462))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _68_24466 = (let _68_24465 = (FSharp_Format.parens x)
in (let _68_24464 = (let _68_24463 = (FSharp_Format.text "::")
in (_68_24463)::(xs)::[])
in (_68_24465)::_68_24464))
in (FSharp_Format.reduce _68_24466))
end
| (_, _) -> begin
(let _68_24472 = (let _68_24471 = (FSharp_Format.text name)
in (let _68_24470 = (let _68_24469 = (let _68_24468 = (let _68_24467 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24467 args))
in (FSharp_Format.parens _68_24468))
in (_68_24469)::[])
in (_68_24471)::_68_24470))
in (FSharp_Format.reduce1 _68_24472))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _68_24474 = (let _68_24473 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24473 docs))
in (FSharp_Format.parens _68_24474))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _68_24480 = (let _68_24479 = (let _68_24478 = (let _68_24477 = (let _68_24476 = (let _68_24475 = (FSharp_Format.text "in")
in (_68_24475)::(body)::[])
in (FSharp_Format.reduce1 _68_24476))
in (_68_24477)::[])
in (doc)::_68_24478)
in (FSharp_Format.combine FSharp_Format.hardline _68_24479))
in (FSharp_Format.parens _68_24480))))
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
| _ -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _68_24481 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _68_24481))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _68_24487 = (let _68_24486 = (let _68_24485 = (FSharp_Format.text ".")
in (let _68_24484 = (let _68_24483 = (let _68_24482 = (ptsym currentModule f)
in (FSharp_Format.text _68_24482))
in (_68_24483)::[])
in (_68_24485)::_68_24484))
in (e)::_68_24486)
in (FSharp_Format.reduce _68_24487))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _57_339 ) -> (match (_57_339) with
| ((x, _), xt) -> begin
(let _68_24494 = (let _68_24493 = (FSharp_Format.text "(")
in (let _68_24492 = (let _68_24491 = (FSharp_Format.text x)
in (let _68_24490 = (let _68_24489 = (FSharp_Format.text ")")
in (_68_24489)::[])
in (_68_24491)::_68_24490))
in (_68_24493)::_68_24492))
in (FSharp_Format.reduce1 _68_24494))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _68_24500 = (let _68_24499 = (FSharp_Format.text "fun")
in (let _68_24498 = (let _68_24497 = (FSharp_Format.reduce1 ids)
in (let _68_24496 = (let _68_24495 = (FSharp_Format.text "->")
in (_68_24495)::(body)::[])
in (_68_24497)::_68_24496))
in (_68_24499)::_68_24498))
in (FSharp_Format.reduce1 _68_24500))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_24513 = (let _68_24512 = (let _68_24507 = (let _68_24506 = (FSharp_Format.text "if")
in (let _68_24505 = (let _68_24504 = (let _68_24503 = (FSharp_Format.text "then")
in (let _68_24502 = (let _68_24501 = (FSharp_Format.text "begin")
in (_68_24501)::[])
in (_68_24503)::_68_24502))
in (cond)::_68_24504)
in (_68_24506)::_68_24505))
in (FSharp_Format.reduce1 _68_24507))
in (let _68_24511 = (let _68_24510 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _68_24509 = (let _68_24508 = (FSharp_Format.text "end")
in (_68_24508)::[])
in (_68_24510)::_68_24509))
in (_68_24512)::_68_24511))
in (FSharp_Format.combine FSharp_Format.hardline _68_24513))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_24536 = (let _68_24535 = (let _68_24520 = (let _68_24519 = (FSharp_Format.text "if")
in (let _68_24518 = (let _68_24517 = (let _68_24516 = (FSharp_Format.text "then")
in (let _68_24515 = (let _68_24514 = (FSharp_Format.text "begin")
in (_68_24514)::[])
in (_68_24516)::_68_24515))
in (cond)::_68_24517)
in (_68_24519)::_68_24518))
in (FSharp_Format.reduce1 _68_24520))
in (let _68_24534 = (let _68_24533 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _68_24532 = (let _68_24531 = (let _68_24526 = (let _68_24525 = (FSharp_Format.text "end")
in (let _68_24524 = (let _68_24523 = (FSharp_Format.text "else")
in (let _68_24522 = (let _68_24521 = (FSharp_Format.text "begin")
in (_68_24521)::[])
in (_68_24523)::_68_24522))
in (_68_24525)::_68_24524))
in (FSharp_Format.reduce1 _68_24526))
in (let _68_24530 = (let _68_24529 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _68_24528 = (let _68_24527 = (FSharp_Format.text "end")
in (_68_24527)::[])
in (_68_24529)::_68_24528))
in (_68_24531)::_68_24530))
in (_68_24533)::_68_24532))
in (_68_24535)::_68_24534))
in (FSharp_Format.combine FSharp_Format.hardline _68_24536))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _68_24543 = (let _68_24542 = (let _68_24541 = (FSharp_Format.text "match")
in (let _68_24540 = (let _68_24539 = (FSharp_Format.parens cond)
in (let _68_24538 = (let _68_24537 = (FSharp_Format.text "with")
in (_68_24537)::[])
in (_68_24539)::_68_24538))
in (_68_24541)::_68_24540))
in (FSharp_Format.reduce1 _68_24542))
in (_68_24543)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _68_24548 = (let _68_24547 = (FSharp_Format.text "raise")
in (let _68_24546 = (let _68_24545 = (let _68_24544 = (ptctor currentModule exn)
in (FSharp_Format.text _68_24544))
in (_68_24545)::[])
in (_68_24547)::_68_24546))
in (FSharp_Format.reduce1 _68_24548))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _68_24557 = (let _68_24556 = (FSharp_Format.text "raise")
in (let _68_24555 = (let _68_24554 = (let _68_24549 = (ptctor currentModule exn)
in (FSharp_Format.text _68_24549))
in (let _68_24553 = (let _68_24552 = (let _68_24551 = (let _68_24550 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24550 args))
in (FSharp_Format.parens _68_24551))
in (_68_24552)::[])
in (_68_24554)::_68_24553))
in (_68_24556)::_68_24555))
in (FSharp_Format.reduce1 _68_24557)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _68_24574 = (let _68_24573 = (let _68_24561 = (let _68_24560 = (FSharp_Format.text "try")
in (let _68_24559 = (let _68_24558 = (FSharp_Format.text "begin")
in (_68_24558)::[])
in (_68_24560)::_68_24559))
in (FSharp_Format.reduce1 _68_24561))
in (let _68_24572 = (let _68_24571 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24570 = (let _68_24569 = (let _68_24565 = (let _68_24564 = (FSharp_Format.text "end")
in (let _68_24563 = (let _68_24562 = (FSharp_Format.text "with")
in (_68_24562)::[])
in (_68_24564)::_68_24563))
in (FSharp_Format.reduce1 _68_24565))
in (let _68_24568 = (let _68_24567 = (let _68_24566 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _68_24566))
in (_68_24567)::[])
in (_68_24569)::_68_24568))
in (_68_24571)::_68_24570))
in (_68_24573)::_68_24572))
in (FSharp_Format.combine FSharp_Format.hardline _68_24574))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _57_387 = (let _68_24579 = (as_bin_op p)
in (Support.Option.get _68_24579))
in (match (_57_387) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _68_24582 = (let _68_24581 = (let _68_24580 = (FSharp_Format.text txt)
in (_68_24580)::(e2)::[])
in (e1)::_68_24581)
in (FSharp_Format.reduce1 _68_24582))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _57_397 = (let _68_24586 = (as_uni_op p)
in (Support.Option.get _68_24586))
in (match (_57_397) with
| (_, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _68_24590 = (let _68_24589 = (FSharp_Format.text txt)
in (let _68_24588 = (let _68_24587 = (FSharp_Format.parens e1)
in (_68_24587)::[])
in (_68_24589)::_68_24588))
in (FSharp_Format.reduce1 _68_24590))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _68_24593 = (string_of_mlconstant c)
in (FSharp_Format.text _68_24593))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _57_414 ) -> (match (_57_414) with
| (name, p) -> begin
(let _68_24602 = (let _68_24601 = (let _68_24596 = (ptsym currentModule (path, name))
in (FSharp_Format.text _68_24596))
in (let _68_24600 = (let _68_24599 = (FSharp_Format.text "=")
in (let _68_24598 = (let _68_24597 = (doc_of_pattern currentModule p)
in (_68_24597)::[])
in (_68_24599)::_68_24598))
in (_68_24601)::_68_24600))
in (FSharp_Format.reduce1 _68_24602))
end))
in (let _68_24605 = (let _68_24604 = (FSharp_Format.text "; ")
in (let _68_24603 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_24604 _68_24603)))
in (FSharp_Format.cbrackets _68_24605)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24607 = (let _68_24606 = (as_standard_constructor ctor)
in (Support.Option.get _68_24606))
in (Support.Prims.snd _68_24607))
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
(let _68_24609 = (let _68_24608 = (as_standard_constructor ctor)
in (Support.Option.get _68_24608))
in (Support.Prims.snd _68_24609))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _68_24612 = (let _68_24611 = (let _68_24610 = (FSharp_Format.text "::")
in (_68_24610)::(xs)::[])
in (x)::_68_24611)
in (FSharp_Format.reduce _68_24612))
end
| (_, _) -> begin
(let _68_24618 = (let _68_24617 = (FSharp_Format.text name)
in (let _68_24616 = (let _68_24615 = (let _68_24614 = (let _68_24613 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24613 ps))
in (FSharp_Format.parens _68_24614))
in (_68_24615)::[])
in (_68_24617)::_68_24616))
in (FSharp_Format.reduce1 _68_24618))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _68_24620 = (let _68_24619 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24619 ps))
in (FSharp_Format.parens _68_24620)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _68_24621 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _68_24621 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _57_448 ) -> (match (_57_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _68_24627 = (let _68_24626 = (FSharp_Format.text "|")
in (let _68_24625 = (let _68_24624 = (doc_of_pattern currentModule p)
in (_68_24624)::[])
in (_68_24626)::_68_24625))
in (FSharp_Format.reduce1 _68_24627))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _68_24633 = (let _68_24632 = (FSharp_Format.text "|")
in (let _68_24631 = (let _68_24630 = (doc_of_pattern currentModule p)
in (let _68_24629 = (let _68_24628 = (FSharp_Format.text "when")
in (_68_24628)::(c)::[])
in (_68_24630)::_68_24629))
in (_68_24632)::_68_24631))
in (FSharp_Format.reduce1 _68_24633)))
end)
in (let _68_24644 = (let _68_24643 = (let _68_24638 = (let _68_24637 = (let _68_24636 = (FSharp_Format.text "->")
in (let _68_24635 = (let _68_24634 = (FSharp_Format.text "begin")
in (_68_24634)::[])
in (_68_24636)::_68_24635))
in (case)::_68_24637)
in (FSharp_Format.reduce1 _68_24638))
in (let _68_24642 = (let _68_24641 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24640 = (let _68_24639 = (FSharp_Format.text "end")
in (_68_24639)::[])
in (_68_24641)::_68_24640))
in (_68_24643)::_68_24642))
in (FSharp_Format.combine FSharp_Format.hardline _68_24644)))
end))
and doc_of_lets = (fun ( currentModule ) ( _57_457 ) -> (match (_57_457) with
| (rec_, lets) -> begin
(let for1 = (fun ( _57_464 ) -> (match (_57_464) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _57_470 ) -> (match (_57_470) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _68_24655 = (let _68_24654 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _68_24653 = (let _68_24652 = (FSharp_Format.reduce1 ids)
in (let _68_24651 = (let _68_24650 = (FSharp_Format.text "=")
in (_68_24650)::(e)::[])
in (_68_24652)::_68_24651))
in (_68_24654)::_68_24653))
in (FSharp_Format.reduce1 _68_24655)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _68_24659 = (let _68_24658 = (FSharp_Format.text "let")
in (let _68_24657 = (let _68_24656 = (FSharp_Format.text "rec")
in (_68_24656)::[])
in (_68_24658)::_68_24657))
in (FSharp_Format.reduce1 _68_24659))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _68_24663 = (let _68_24662 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_68_24662)::(doc)::[])
in (FSharp_Format.reduce1 _68_24663))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _57_483 ) -> (match (_57_483) with
| (x, tparams, body) -> begin
(let tparams = (match (tparams) with
| [] -> begin
FSharp_Format.empty
end
| x::[] -> begin
(FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
end
| _ -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _68_24672 = (let _68_24671 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24671 doc))
in (FSharp_Format.parens _68_24672)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _57_501 ) -> (match (_57_501) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _68_24679 = (let _68_24678 = (let _68_24677 = (FSharp_Format.text ":")
in (_68_24677)::(ty)::[])
in (name)::_68_24678)
in (FSharp_Format.reduce1 _68_24679))))
end))
in (let _68_24682 = (let _68_24681 = (FSharp_Format.text "; ")
in (let _68_24680 = (Support.List.map forfield fields)
in (FSharp_Format.combine _68_24681 _68_24680)))
in (FSharp_Format.cbrackets _68_24682)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _57_509 ) -> (match (_57_509) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _ -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _68_24685 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24685 tys))
in (let _68_24689 = (let _68_24688 = (FSharp_Format.text name)
in (let _68_24687 = (let _68_24686 = (FSharp_Format.text "of")
in (_68_24686)::(tys)::[])
in (_68_24688)::_68_24687))
in (FSharp_Format.reduce1 _68_24689))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _68_24692 = (let _68_24691 = (FSharp_Format.text "|")
in (_68_24691)::(d)::[])
in (FSharp_Format.reduce1 _68_24692))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _68_24696 = (let _68_24695 = (let _68_24694 = (let _68_24693 = (ptsym currentModule ([], x))
in (FSharp_Format.text _68_24693))
in (_68_24694)::[])
in (tparams)::_68_24695)
in (FSharp_Format.reduce1 _68_24696))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _68_24701 = (let _68_24700 = (let _68_24699 = (let _68_24698 = (let _68_24697 = (FSharp_Format.text "=")
in (_68_24697)::[])
in (doc)::_68_24698)
in (FSharp_Format.reduce1 _68_24699))
in (_68_24700)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _68_24701)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _68_24706 = (let _68_24705 = (FSharp_Format.text "type")
in (let _68_24704 = (let _68_24703 = (let _68_24702 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _68_24702 doc))
in (_68_24703)::[])
in (_68_24705)::_68_24704))
in (FSharp_Format.reduce1 _68_24706))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _68_24726 = (let _68_24725 = (let _68_24718 = (let _68_24717 = (FSharp_Format.text "module")
in (let _68_24716 = (let _68_24715 = (FSharp_Format.text x)
in (let _68_24714 = (let _68_24713 = (FSharp_Format.text "=")
in (_68_24713)::[])
in (_68_24715)::_68_24714))
in (_68_24717)::_68_24716))
in (FSharp_Format.reduce1 _68_24718))
in (let _68_24724 = (let _68_24723 = (doc_of_sig currentModule subsig)
in (let _68_24722 = (let _68_24721 = (let _68_24720 = (let _68_24719 = (FSharp_Format.text "end")
in (_68_24719)::[])
in (FSharp_Format.reduce1 _68_24720))
in (_68_24721)::[])
in (_68_24723)::_68_24722))
in (_68_24725)::_68_24724))
in (FSharp_Format.combine FSharp_Format.hardline _68_24726))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _68_24730 = (let _68_24729 = (FSharp_Format.text "exception")
in (let _68_24728 = (let _68_24727 = (FSharp_Format.text x)
in (_68_24727)::[])
in (_68_24729)::_68_24728))
in (FSharp_Format.reduce1 _68_24730))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _68_24732 = (let _68_24731 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24731 args))
in (FSharp_Format.parens _68_24732))
in (let _68_24738 = (let _68_24737 = (FSharp_Format.text "exception")
in (let _68_24736 = (let _68_24735 = (FSharp_Format.text x)
in (let _68_24734 = (let _68_24733 = (FSharp_Format.text "of")
in (_68_24733)::(args)::[])
in (_68_24735)::_68_24734))
in (_68_24737)::_68_24736))
in (FSharp_Format.reduce1 _68_24738))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _68_24744 = (let _68_24743 = (FSharp_Format.text "val")
in (let _68_24742 = (let _68_24741 = (FSharp_Format.text x)
in (let _68_24740 = (let _68_24739 = (FSharp_Format.text ": ")
in (_68_24739)::(ty)::[])
in (_68_24741)::_68_24740))
in (_68_24743)::_68_24742))
in (FSharp_Format.reduce1 _68_24744)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _68_24755 = (let _68_24754 = (FSharp_Format.text "exception")
in (let _68_24753 = (let _68_24752 = (FSharp_Format.text x)
in (_68_24752)::[])
in (_68_24754)::_68_24753))
in (FSharp_Format.reduce1 _68_24755))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _68_24757 = (let _68_24756 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24756 args))
in (FSharp_Format.parens _68_24757))
in (let _68_24763 = (let _68_24762 = (FSharp_Format.text "exception")
in (let _68_24761 = (let _68_24760 = (FSharp_Format.text x)
in (let _68_24759 = (let _68_24758 = (FSharp_Format.text "of")
in (_68_24758)::(args)::[])
in (_68_24760)::_68_24759))
in (_68_24762)::_68_24761))
in (FSharp_Format.reduce1 _68_24763))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _68_24771 = (let _68_24770 = (FSharp_Format.text "let")
in (let _68_24769 = (let _68_24768 = (FSharp_Format.text "_")
in (let _68_24767 = (let _68_24766 = (FSharp_Format.text "=")
in (let _68_24765 = (let _68_24764 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_68_24764)::[])
in (_68_24766)::_68_24765))
in (_68_24768)::_68_24767))
in (_68_24770)::_68_24769))
in (FSharp_Format.reduce1 _68_24771))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _57_582 ) -> (match (_57_582) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _57_589 ) -> (match (_57_589) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _68_24790 = (let _68_24789 = (FSharp_Format.text "module")
in (let _68_24788 = (let _68_24787 = (FSharp_Format.text x)
in (let _68_24786 = (let _68_24785 = (FSharp_Format.text ":")
in (let _68_24784 = (let _68_24783 = (FSharp_Format.text "sig")
in (_68_24783)::[])
in (_68_24785)::_68_24784))
in (_68_24787)::_68_24786))
in (_68_24789)::_68_24788))
in (FSharp_Format.reduce1 _68_24790))
in (let tail = (let _68_24792 = (let _68_24791 = (FSharp_Format.text "end")
in (_68_24791)::[])
in (FSharp_Format.reduce1 _68_24792))
in (let doc = (Support.Option.map (fun ( _57_595 ) -> (match (_57_595) with
| (s, _) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_24802 = (let _68_24801 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_24800 = (let _68_24799 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_24798 = (let _68_24797 = (FSharp_Format.reduce sub)
in (let _68_24796 = (let _68_24795 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_24795)::[])
in (_68_24797)::_68_24796))
in (_68_24799)::_68_24798))
in (_68_24801)::_68_24800))
in (FSharp_Format.reduce _68_24802)))))))
end))
and for1_mod = (fun ( istop ) ( _57_608 ) -> (match (_57_608) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _57_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _68_24812 = (match ((not (istop))) with
| true -> begin
(let _68_24811 = (FSharp_Format.text "module")
in (let _68_24810 = (let _68_24809 = (FSharp_Format.text x)
in (let _68_24808 = (let _68_24807 = (FSharp_Format.text "=")
in (let _68_24806 = (let _68_24805 = (FSharp_Format.text "struct")
in (_68_24805)::[])
in (_68_24807)::_68_24806))
in (_68_24809)::_68_24808))
in (_68_24811)::_68_24810))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _68_24812))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _68_24814 = (let _68_24813 = (FSharp_Format.text "end")
in (_68_24813)::[])
in (FSharp_Format.reduce1 _68_24814))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _57_616 ) -> (match (_57_616) with
| (_, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_24824 = (let _68_24823 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_24822 = (let _68_24821 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_24820 = (let _68_24819 = (FSharp_Format.reduce sub)
in (let _68_24818 = (let _68_24817 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_24817)::[])
in (_68_24819)::_68_24818))
in (_68_24821)::_68_24820))
in (_68_24823)::_68_24822))
in (FSharp_Format.reduce _68_24824))))))))
end))
in (let docs = (Support.List.map (fun ( _57_627 ) -> (match (_57_627) with
| (x, s, m) -> begin
(let _68_24826 = (for1_mod true (x, s, m))
in (x, _68_24826))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))






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
(match ((let _70_27380 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _70_27380))) with
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
(let _70_27385 = (path_of_ns currentModule ns)
in (_70_27385, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _70_27388 = (Support.String.get s 0)
in (Support.Char.lowercase _70_27388)) <> (Support.String.get s 0))) with
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
(let _70_27395 = (let _70_27394 = (let _70_27393 = (ptsym_of_symbol s)
in (_70_27393)::[])
in (Support.List.append p _70_27394))
in (Support.String.concat "." _70_27395))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_58 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_58) with
| (p, s) -> begin
(let s = (match (((let _70_27400 = (Support.String.get s 0)
in (Support.Char.uppercase _70_27400)) <> (Support.String.get s 0))) with
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
(let _70_27442 = (let _70_27441 = (encode_char c)
in (Support.String.strcat "\'" _70_27441))
in (Support.String.strcat _70_27442 "\'"))
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
in (let _70_27454 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _70_27454)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _70_27457 = (let _70_27456 = (let _70_27455 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27455 doc))
in (FSharp_Format.hbox _70_27456))
in (FSharp_Format.parens _70_27457))
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
in (let _70_27460 = (let _70_27459 = (let _70_27458 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27458 args))
in (FSharp_Format.hbox _70_27459))
in (FSharp_Format.parens _70_27460)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_27462 = (let _70_27461 = (as_standard_type name)
in (Support.Option.get _70_27461))
in (Support.Prims.snd _70_27462))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _70_27466 = (let _70_27465 = (let _70_27464 = (let _70_27463 = (FSharp_Format.text name)
in (_70_27463)::[])
in (args)::_70_27464)
in (FSharp_Format.reduce1 _70_27465))
in (FSharp_Format.hbox _70_27466))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _59_205, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_27471 = (let _70_27470 = (let _70_27469 = (let _70_27468 = (let _70_27467 = (FSharp_Format.text " -> ")
in (_70_27467)::(d2)::[])
in (d1)::_70_27468)
in (FSharp_Format.reduce1 _70_27469))
in (FSharp_Format.hbox _70_27470))
in (maybe_paren outer t_prio_fun _70_27471))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_27476 = (let _70_27475 = (let _70_27474 = (let _70_27473 = (let _70_27472 = (FSharp_Format.text " ")
in (_70_27472)::(d1)::[])
in (d2)::_70_27473)
in (FSharp_Format.reduce1 _70_27474))
in (FSharp_Format.hbox _70_27475))
in (maybe_paren outer t_prio_fun _70_27476))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27501 = (let _70_27500 = (let _70_27499 = (FSharp_Format.text "Obj.magic ")
in (_70_27499)::(doc)::[])
in (FSharp_Format.reduce _70_27500))
in (FSharp_Format.parens _70_27501)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_27505 = (let _70_27504 = (let _70_27503 = (FSharp_Format.text ";")
in (_70_27503)::(FSharp_Format.hardline)::[])
in (d)::_70_27504)
in (FSharp_Format.reduce _70_27505))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _70_27506 = (string_of_mlconstant c)
in (FSharp_Format.text _70_27506))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _59_239)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _70_27507 = (ptsym currentModule path)
in (FSharp_Format.text _70_27507))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_251 ) -> (match (_59_251) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27514 = (let _70_27513 = (let _70_27510 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_27510))
in (let _70_27512 = (let _70_27511 = (FSharp_Format.text "=")
in (_70_27511)::(doc)::[])
in (_70_27513)::_70_27512))
in (FSharp_Format.reduce1 _70_27514)))
end))
in (let _70_27517 = (let _70_27516 = (FSharp_Format.text "; ")
in (let _70_27515 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_27516 _70_27515)))
in (FSharp_Format.cbrackets _70_27517)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27519 = (let _70_27518 = (as_standard_constructor ctor)
in (Support.Option.get _70_27518))
in (Support.Prims.snd _70_27519))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27521 = (let _70_27520 = (as_standard_constructor ctor)
in (Support.Option.get _70_27520))
in (Support.Prims.snd _70_27521))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_27525 = (let _70_27524 = (FSharp_Format.parens x)
in (let _70_27523 = (let _70_27522 = (FSharp_Format.text "::")
in (_70_27522)::(xs)::[])
in (_70_27524)::_70_27523))
in (FSharp_Format.reduce _70_27525))
end
| (_59_270, _59_272) -> begin
(let _70_27531 = (let _70_27530 = (FSharp_Format.text name)
in (let _70_27529 = (let _70_27528 = (let _70_27527 = (let _70_27526 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27526 args))
in (FSharp_Format.parens _70_27527))
in (_70_27528)::[])
in (_70_27530)::_70_27529))
in (FSharp_Format.reduce1 _70_27531))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_27533 = (let _70_27532 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27532 docs))
in (FSharp_Format.parens _70_27533))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _70_27539 = (let _70_27538 = (let _70_27537 = (let _70_27536 = (let _70_27535 = (let _70_27534 = (FSharp_Format.text "in")
in (_70_27534)::(body)::[])
in (FSharp_Format.reduce1 _70_27535))
in (_70_27536)::[])
in (doc)::_70_27537)
in (FSharp_Format.combine FSharp_Format.hardline _70_27538))
in (FSharp_Format.parens _70_27539))))
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
in (let _70_27540 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_27540))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _70_27546 = (let _70_27545 = (let _70_27544 = (FSharp_Format.text ".")
in (let _70_27543 = (let _70_27542 = (let _70_27541 = (ptsym currentModule f)
in (FSharp_Format.text _70_27541))
in (_70_27542)::[])
in (_70_27544)::_70_27543))
in (e)::_70_27545)
in (FSharp_Format.reduce _70_27546))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_340 ) -> (match (_59_340) with
| ((x, _59_337), xt) -> begin
(let _70_27553 = (let _70_27552 = (FSharp_Format.text "(")
in (let _70_27551 = (let _70_27550 = (FSharp_Format.text x)
in (let _70_27549 = (let _70_27548 = (FSharp_Format.text ")")
in (_70_27548)::[])
in (_70_27550)::_70_27549))
in (_70_27552)::_70_27551))
in (FSharp_Format.reduce1 _70_27553))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _70_27559 = (let _70_27558 = (FSharp_Format.text "fun")
in (let _70_27557 = (let _70_27556 = (FSharp_Format.reduce1 ids)
in (let _70_27555 = (let _70_27554 = (FSharp_Format.text "->")
in (_70_27554)::(body)::[])
in (_70_27556)::_70_27555))
in (_70_27558)::_70_27557))
in (FSharp_Format.reduce1 _70_27559))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_27572 = (let _70_27571 = (let _70_27566 = (let _70_27565 = (FSharp_Format.text "if")
in (let _70_27564 = (let _70_27563 = (let _70_27562 = (FSharp_Format.text "then")
in (let _70_27561 = (let _70_27560 = (FSharp_Format.text "begin")
in (_70_27560)::[])
in (_70_27562)::_70_27561))
in (cond)::_70_27563)
in (_70_27565)::_70_27564))
in (FSharp_Format.reduce1 _70_27566))
in (let _70_27570 = (let _70_27569 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_27568 = (let _70_27567 = (FSharp_Format.text "end")
in (_70_27567)::[])
in (_70_27569)::_70_27568))
in (_70_27571)::_70_27570))
in (FSharp_Format.combine FSharp_Format.hardline _70_27572))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_27595 = (let _70_27594 = (let _70_27579 = (let _70_27578 = (FSharp_Format.text "if")
in (let _70_27577 = (let _70_27576 = (let _70_27575 = (FSharp_Format.text "then")
in (let _70_27574 = (let _70_27573 = (FSharp_Format.text "begin")
in (_70_27573)::[])
in (_70_27575)::_70_27574))
in (cond)::_70_27576)
in (_70_27578)::_70_27577))
in (FSharp_Format.reduce1 _70_27579))
in (let _70_27593 = (let _70_27592 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_27591 = (let _70_27590 = (let _70_27585 = (let _70_27584 = (FSharp_Format.text "end")
in (let _70_27583 = (let _70_27582 = (FSharp_Format.text "else")
in (let _70_27581 = (let _70_27580 = (FSharp_Format.text "begin")
in (_70_27580)::[])
in (_70_27582)::_70_27581))
in (_70_27584)::_70_27583))
in (FSharp_Format.reduce1 _70_27585))
in (let _70_27589 = (let _70_27588 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _70_27587 = (let _70_27586 = (FSharp_Format.text "end")
in (_70_27586)::[])
in (_70_27588)::_70_27587))
in (_70_27590)::_70_27589))
in (_70_27592)::_70_27591))
in (_70_27594)::_70_27593))
in (FSharp_Format.combine FSharp_Format.hardline _70_27595))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _70_27602 = (let _70_27601 = (let _70_27600 = (FSharp_Format.text "match")
in (let _70_27599 = (let _70_27598 = (FSharp_Format.parens cond)
in (let _70_27597 = (let _70_27596 = (FSharp_Format.text "with")
in (_70_27596)::[])
in (_70_27598)::_70_27597))
in (_70_27600)::_70_27599))
in (FSharp_Format.reduce1 _70_27601))
in (_70_27602)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_27607 = (let _70_27606 = (FSharp_Format.text "raise")
in (let _70_27605 = (let _70_27604 = (let _70_27603 = (ptctor currentModule exn)
in (FSharp_Format.text _70_27603))
in (_70_27604)::[])
in (_70_27606)::_70_27605))
in (FSharp_Format.reduce1 _70_27607))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _70_27616 = (let _70_27615 = (FSharp_Format.text "raise")
in (let _70_27614 = (let _70_27613 = (let _70_27608 = (ptctor currentModule exn)
in (FSharp_Format.text _70_27608))
in (let _70_27612 = (let _70_27611 = (let _70_27610 = (let _70_27609 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27609 args))
in (FSharp_Format.parens _70_27610))
in (_70_27611)::[])
in (_70_27613)::_70_27612))
in (_70_27615)::_70_27614))
in (FSharp_Format.reduce1 _70_27616)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_27633 = (let _70_27632 = (let _70_27620 = (let _70_27619 = (FSharp_Format.text "try")
in (let _70_27618 = (let _70_27617 = (FSharp_Format.text "begin")
in (_70_27617)::[])
in (_70_27619)::_70_27618))
in (FSharp_Format.reduce1 _70_27620))
in (let _70_27631 = (let _70_27630 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27629 = (let _70_27628 = (let _70_27624 = (let _70_27623 = (FSharp_Format.text "end")
in (let _70_27622 = (let _70_27621 = (FSharp_Format.text "with")
in (_70_27621)::[])
in (_70_27623)::_70_27622))
in (FSharp_Format.reduce1 _70_27624))
in (let _70_27627 = (let _70_27626 = (let _70_27625 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_27625))
in (_70_27626)::[])
in (_70_27628)::_70_27627))
in (_70_27630)::_70_27629))
in (_70_27632)::_70_27631))
in (FSharp_Format.combine FSharp_Format.hardline _70_27633))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_388 = (let _70_27638 = (as_bin_op p)
in (Support.Option.get _70_27638))
in (match (_59_388) with
| (_59_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _70_27641 = (let _70_27640 = (let _70_27639 = (FSharp_Format.text txt)
in (_70_27639)::(e2)::[])
in (e1)::_70_27640)
in (FSharp_Format.reduce1 _70_27641))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_398 = (let _70_27645 = (as_uni_op p)
in (Support.Option.get _70_27645))
in (match (_59_398) with
| (_59_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_27649 = (let _70_27648 = (FSharp_Format.text txt)
in (let _70_27647 = (let _70_27646 = (FSharp_Format.parens e1)
in (_70_27646)::[])
in (_70_27648)::_70_27647))
in (FSharp_Format.reduce1 _70_27649))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _70_27652 = (string_of_mlconstant c)
in (FSharp_Format.text _70_27652))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_415 ) -> (match (_59_415) with
| (name, p) -> begin
(let _70_27661 = (let _70_27660 = (let _70_27655 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_27655))
in (let _70_27659 = (let _70_27658 = (FSharp_Format.text "=")
in (let _70_27657 = (let _70_27656 = (doc_of_pattern currentModule p)
in (_70_27656)::[])
in (_70_27658)::_70_27657))
in (_70_27660)::_70_27659))
in (FSharp_Format.reduce1 _70_27661))
end))
in (let _70_27664 = (let _70_27663 = (FSharp_Format.text "; ")
in (let _70_27662 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_27663 _70_27662)))
in (FSharp_Format.cbrackets _70_27664)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27666 = (let _70_27665 = (as_standard_constructor ctor)
in (Support.Option.get _70_27665))
in (Support.Prims.snd _70_27666))
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
(let _70_27668 = (let _70_27667 = (as_standard_constructor ctor)
in (Support.Option.get _70_27667))
in (Support.Prims.snd _70_27668))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_27671 = (let _70_27670 = (let _70_27669 = (FSharp_Format.text "::")
in (_70_27669)::(xs)::[])
in (x)::_70_27670)
in (FSharp_Format.reduce _70_27671))
end
| (_59_433, _59_435) -> begin
(let _70_27677 = (let _70_27676 = (FSharp_Format.text name)
in (let _70_27675 = (let _70_27674 = (let _70_27673 = (let _70_27672 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27672 ps))
in (FSharp_Format.parens _70_27673))
in (_70_27674)::[])
in (_70_27676)::_70_27675))
in (FSharp_Format.reduce1 _70_27677))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _70_27679 = (let _70_27678 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27678 ps))
in (FSharp_Format.parens _70_27679)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_27680 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_27680 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_449 ) -> (match (_59_449) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_27686 = (let _70_27685 = (FSharp_Format.text "|")
in (let _70_27684 = (let _70_27683 = (doc_of_pattern currentModule p)
in (_70_27683)::[])
in (_70_27685)::_70_27684))
in (FSharp_Format.reduce1 _70_27686))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _70_27692 = (let _70_27691 = (FSharp_Format.text "|")
in (let _70_27690 = (let _70_27689 = (doc_of_pattern currentModule p)
in (let _70_27688 = (let _70_27687 = (FSharp_Format.text "when")
in (_70_27687)::(c)::[])
in (_70_27689)::_70_27688))
in (_70_27691)::_70_27690))
in (FSharp_Format.reduce1 _70_27692)))
end)
in (let _70_27703 = (let _70_27702 = (let _70_27697 = (let _70_27696 = (let _70_27695 = (FSharp_Format.text "->")
in (let _70_27694 = (let _70_27693 = (FSharp_Format.text "begin")
in (_70_27693)::[])
in (_70_27695)::_70_27694))
in (case)::_70_27696)
in (FSharp_Format.reduce1 _70_27697))
in (let _70_27701 = (let _70_27700 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27699 = (let _70_27698 = (FSharp_Format.text "end")
in (_70_27698)::[])
in (_70_27700)::_70_27699))
in (_70_27702)::_70_27701))
in (FSharp_Format.combine FSharp_Format.hardline _70_27703)))
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
in (let _70_27714 = (let _70_27713 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _70_27712 = (let _70_27711 = (FSharp_Format.reduce1 ids)
in (let _70_27710 = (let _70_27709 = (FSharp_Format.text "=")
in (_70_27709)::(e)::[])
in (_70_27711)::_70_27710))
in (_70_27713)::_70_27712))
in (FSharp_Format.reduce1 _70_27714)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_27718 = (let _70_27717 = (FSharp_Format.text "let")
in (let _70_27716 = (let _70_27715 = (FSharp_Format.text "rec")
in (_70_27715)::[])
in (_70_27717)::_70_27716))
in (FSharp_Format.reduce1 _70_27718))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_27722 = (let _70_27721 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_27721)::(doc)::[])
in (FSharp_Format.reduce1 _70_27722))) lets)
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
in (let _70_27731 = (let _70_27730 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27730 doc))
in (FSharp_Format.parens _70_27731)))
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
in (let _70_27738 = (let _70_27737 = (let _70_27736 = (FSharp_Format.text ":")
in (_70_27736)::(ty)::[])
in (name)::_70_27737)
in (FSharp_Format.reduce1 _70_27738))))
end))
in (let _70_27741 = (let _70_27740 = (FSharp_Format.text "; ")
in (let _70_27739 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_27740 _70_27739)))
in (FSharp_Format.cbrackets _70_27741)))
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
in (let tys = (let _70_27744 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27744 tys))
in (let _70_27748 = (let _70_27747 = (FSharp_Format.text name)
in (let _70_27746 = (let _70_27745 = (FSharp_Format.text "of")
in (_70_27745)::(tys)::[])
in (_70_27747)::_70_27746))
in (FSharp_Format.reduce1 _70_27748))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_27751 = (let _70_27750 = (FSharp_Format.text "|")
in (_70_27750)::(d)::[])
in (FSharp_Format.reduce1 _70_27751))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_27755 = (let _70_27754 = (let _70_27753 = (let _70_27752 = (ptsym currentModule ([], x))
in (FSharp_Format.text _70_27752))
in (_70_27753)::[])
in (tparams)::_70_27754)
in (FSharp_Format.reduce1 _70_27755))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_27760 = (let _70_27759 = (let _70_27758 = (let _70_27757 = (let _70_27756 = (FSharp_Format.text "=")
in (_70_27756)::[])
in (doc)::_70_27757)
in (FSharp_Format.reduce1 _70_27758))
in (_70_27759)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_27760)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_27765 = (let _70_27764 = (FSharp_Format.text "type")
in (let _70_27763 = (let _70_27762 = (let _70_27761 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_27761 doc))
in (_70_27762)::[])
in (_70_27764)::_70_27763))
in (FSharp_Format.reduce1 _70_27765))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_27785 = (let _70_27784 = (let _70_27777 = (let _70_27776 = (FSharp_Format.text "module")
in (let _70_27775 = (let _70_27774 = (FSharp_Format.text x)
in (let _70_27773 = (let _70_27772 = (FSharp_Format.text "=")
in (_70_27772)::[])
in (_70_27774)::_70_27773))
in (_70_27776)::_70_27775))
in (FSharp_Format.reduce1 _70_27777))
in (let _70_27783 = (let _70_27782 = (doc_of_sig currentModule subsig)
in (let _70_27781 = (let _70_27780 = (let _70_27779 = (let _70_27778 = (FSharp_Format.text "end")
in (_70_27778)::[])
in (FSharp_Format.reduce1 _70_27779))
in (_70_27780)::[])
in (_70_27782)::_70_27781))
in (_70_27784)::_70_27783))
in (FSharp_Format.combine FSharp_Format.hardline _70_27785))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_27789 = (let _70_27788 = (FSharp_Format.text "exception")
in (let _70_27787 = (let _70_27786 = (FSharp_Format.text x)
in (_70_27786)::[])
in (_70_27788)::_70_27787))
in (FSharp_Format.reduce1 _70_27789))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_27791 = (let _70_27790 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27790 args))
in (FSharp_Format.parens _70_27791))
in (let _70_27797 = (let _70_27796 = (FSharp_Format.text "exception")
in (let _70_27795 = (let _70_27794 = (FSharp_Format.text x)
in (let _70_27793 = (let _70_27792 = (FSharp_Format.text "of")
in (_70_27792)::(args)::[])
in (_70_27794)::_70_27793))
in (_70_27796)::_70_27795))
in (FSharp_Format.reduce1 _70_27797))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_59_544, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _70_27803 = (let _70_27802 = (FSharp_Format.text "val")
in (let _70_27801 = (let _70_27800 = (FSharp_Format.text x)
in (let _70_27799 = (let _70_27798 = (FSharp_Format.text ": ")
in (_70_27798)::(ty)::[])
in (_70_27800)::_70_27799))
in (_70_27802)::_70_27801))
in (FSharp_Format.reduce1 _70_27803)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_27814 = (let _70_27813 = (FSharp_Format.text "exception")
in (let _70_27812 = (let _70_27811 = (FSharp_Format.text x)
in (_70_27811)::[])
in (_70_27813)::_70_27812))
in (FSharp_Format.reduce1 _70_27814))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_27816 = (let _70_27815 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27815 args))
in (FSharp_Format.parens _70_27816))
in (let _70_27822 = (let _70_27821 = (FSharp_Format.text "exception")
in (let _70_27820 = (let _70_27819 = (FSharp_Format.text x)
in (let _70_27818 = (let _70_27817 = (FSharp_Format.text "of")
in (_70_27817)::(args)::[])
in (_70_27819)::_70_27818))
in (_70_27821)::_70_27820))
in (FSharp_Format.reduce1 _70_27822))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _70_27830 = (let _70_27829 = (FSharp_Format.text "let")
in (let _70_27828 = (let _70_27827 = (FSharp_Format.text "_")
in (let _70_27826 = (let _70_27825 = (FSharp_Format.text "=")
in (let _70_27824 = (let _70_27823 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_70_27823)::[])
in (_70_27825)::_70_27824))
in (_70_27827)::_70_27826))
in (_70_27829)::_70_27828))
in (FSharp_Format.reduce1 _70_27830))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_583 ) -> (match (_59_583) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_590 ) -> (match (_59_590) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_27849 = (let _70_27848 = (FSharp_Format.text "module")
in (let _70_27847 = (let _70_27846 = (FSharp_Format.text x)
in (let _70_27845 = (let _70_27844 = (FSharp_Format.text ":")
in (let _70_27843 = (let _70_27842 = (FSharp_Format.text "sig")
in (_70_27842)::[])
in (_70_27844)::_70_27843))
in (_70_27846)::_70_27845))
in (_70_27848)::_70_27847))
in (FSharp_Format.reduce1 _70_27849))
in (let tail = (let _70_27851 = (let _70_27850 = (FSharp_Format.text "end")
in (_70_27850)::[])
in (FSharp_Format.reduce1 _70_27851))
in (let doc = (Support.Option.map (fun ( _59_596 ) -> (match (_59_596) with
| (s, _59_595) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_27861 = (let _70_27860 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_27859 = (let _70_27858 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_27857 = (let _70_27856 = (FSharp_Format.reduce sub)
in (let _70_27855 = (let _70_27854 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_27854)::[])
in (_70_27856)::_70_27855))
in (_70_27858)::_70_27857))
in (_70_27860)::_70_27859))
in (FSharp_Format.reduce _70_27861)))))))
end))
and for1_mod = (fun ( istop ) ( _59_609 ) -> (match (_59_609) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_610 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_27871 = (match ((not (istop))) with
| true -> begin
(let _70_27870 = (FSharp_Format.text "module")
in (let _70_27869 = (let _70_27868 = (FSharp_Format.text x)
in (let _70_27867 = (let _70_27866 = (FSharp_Format.text "=")
in (let _70_27865 = (let _70_27864 = (FSharp_Format.text "struct")
in (_70_27864)::[])
in (_70_27866)::_70_27865))
in (_70_27868)::_70_27867))
in (_70_27870)::_70_27869))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_27871))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_27873 = (let _70_27872 = (FSharp_Format.text "end")
in (_70_27872)::[])
in (FSharp_Format.reduce1 _70_27873))
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
in (let _70_27883 = (let _70_27882 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_27881 = (let _70_27880 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_27879 = (let _70_27878 = (FSharp_Format.reduce sub)
in (let _70_27877 = (let _70_27876 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_27876)::[])
in (_70_27878)::_70_27877))
in (_70_27880)::_70_27879))
in (_70_27882)::_70_27881))
in (FSharp_Format.reduce _70_27883))))))))
end))
in (let docs = (Support.List.map (fun ( _59_628 ) -> (match (_59_628) with
| (x, s, m) -> begin
(let _70_27885 = (for1_mod true (x, s, m))
in (x, _70_27885))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





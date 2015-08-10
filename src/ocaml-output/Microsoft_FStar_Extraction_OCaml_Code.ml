
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
(match ((let _70_27385 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _70_27385))) with
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
(let _70_27390 = (path_of_ns currentModule ns)
in (_70_27390, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _70_27393 = (Support.String.get s 0)
in (Support.Char.lowercase _70_27393)) <> (Support.String.get s 0))) with
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
(let _70_27400 = (let _70_27399 = (let _70_27398 = (ptsym_of_symbol s)
in (_70_27398)::[])
in (Support.List.append p _70_27399))
in (Support.String.concat "." _70_27400))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_58 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_58) with
| (p, s) -> begin
(let s = (match (((let _70_27405 = (Support.String.get s 0)
in (Support.Char.uppercase _70_27405)) <> (Support.String.get s 0))) with
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
(let _70_27447 = (let _70_27446 = (encode_char c)
in (Support.String.strcat "\'" _70_27446))
in (Support.String.strcat _70_27447 "\'"))
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
in (let _70_27459 = (Support.All.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _70_27459)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _70_27462 = (let _70_27461 = (let _70_27460 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27460 doc))
in (FSharp_Format.hbox _70_27461))
in (FSharp_Format.parens _70_27462))
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
in (let _70_27465 = (let _70_27464 = (let _70_27463 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27463 args))
in (FSharp_Format.hbox _70_27464))
in (FSharp_Format.parens _70_27465)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _70_27467 = (let _70_27466 = (as_standard_type name)
in (Support.Option.get _70_27466))
in (Support.Prims.snd _70_27467))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _70_27471 = (let _70_27470 = (let _70_27469 = (let _70_27468 = (FSharp_Format.text name)
in (_70_27468)::[])
in (args)::_70_27469)
in (FSharp_Format.reduce1 _70_27470))
in (FSharp_Format.hbox _70_27471))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _59_205, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_27476 = (let _70_27475 = (let _70_27474 = (let _70_27473 = (let _70_27472 = (FSharp_Format.text " -> ")
in (_70_27472)::(d2)::[])
in (d1)::_70_27473)
in (FSharp_Format.reduce1 _70_27474))
in (FSharp_Format.hbox _70_27475))
in (maybe_paren outer t_prio_fun _70_27476))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _70_27481 = (let _70_27480 = (let _70_27479 = (let _70_27478 = (let _70_27477 = (FSharp_Format.text " ")
in (_70_27477)::(d1)::[])
in (d2)::_70_27478)
in (FSharp_Format.reduce1 _70_27479))
in (FSharp_Format.hbox _70_27480))
in (maybe_paren outer t_prio_fun _70_27481))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27506 = (let _70_27505 = (let _70_27504 = (FSharp_Format.text "Obj.magic ")
in (_70_27504)::(doc)::[])
in (FSharp_Format.reduce _70_27505))
in (FSharp_Format.parens _70_27506)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _70_27510 = (let _70_27509 = (let _70_27508 = (FSharp_Format.text ";")
in (_70_27508)::(FSharp_Format.hardline)::[])
in (d)::_70_27509)
in (FSharp_Format.reduce _70_27510))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _70_27511 = (string_of_mlconstant c)
in (FSharp_Format.text _70_27511))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _59_239)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _70_27512 = (ptsym currentModule path)
in (FSharp_Format.text _70_27512))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_251 ) -> (match (_59_251) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27519 = (let _70_27518 = (let _70_27515 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_27515))
in (let _70_27517 = (let _70_27516 = (FSharp_Format.text "=")
in (_70_27516)::(doc)::[])
in (_70_27518)::_70_27517))
in (FSharp_Format.reduce1 _70_27519)))
end))
in (let _70_27522 = (let _70_27521 = (FSharp_Format.text "; ")
in (let _70_27520 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_27521 _70_27520)))
in (FSharp_Format.cbrackets _70_27522)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27524 = (let _70_27523 = (as_standard_constructor ctor)
in (Support.Option.get _70_27523))
in (Support.Prims.snd _70_27524))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27526 = (let _70_27525 = (as_standard_constructor ctor)
in (Support.Option.get _70_27525))
in (Support.Prims.snd _70_27526))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _70_27530 = (let _70_27529 = (FSharp_Format.parens x)
in (let _70_27528 = (let _70_27527 = (FSharp_Format.text "::")
in (_70_27527)::(xs)::[])
in (_70_27529)::_70_27528))
in (FSharp_Format.reduce _70_27530))
end
| (_59_270, _59_272) -> begin
(let _70_27536 = (let _70_27535 = (FSharp_Format.text name)
in (let _70_27534 = (let _70_27533 = (let _70_27532 = (let _70_27531 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27531 args))
in (FSharp_Format.parens _70_27532))
in (_70_27533)::[])
in (_70_27535)::_70_27534))
in (FSharp_Format.reduce1 _70_27536))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _70_27538 = (let _70_27537 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27537 docs))
in (FSharp_Format.parens _70_27538))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _70_27544 = (let _70_27543 = (let _70_27542 = (let _70_27541 = (let _70_27540 = (let _70_27539 = (FSharp_Format.text "in")
in (_70_27539)::(body)::[])
in (FSharp_Format.reduce1 _70_27540))
in (_70_27541)::[])
in (doc)::_70_27542)
in (FSharp_Format.combine FSharp_Format.hardline _70_27543))
in (FSharp_Format.parens _70_27544))))
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
in (let _70_27545 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _70_27545))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _70_27551 = (let _70_27550 = (let _70_27549 = (FSharp_Format.text ".")
in (let _70_27548 = (let _70_27547 = (let _70_27546 = (ptsym currentModule f)
in (FSharp_Format.text _70_27546))
in (_70_27547)::[])
in (_70_27549)::_70_27548))
in (e)::_70_27550)
in (FSharp_Format.reduce _70_27551))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_340 ) -> (match (_59_340) with
| ((x, _59_337), xt) -> begin
(let _70_27558 = (let _70_27557 = (FSharp_Format.text "(")
in (let _70_27556 = (let _70_27555 = (FSharp_Format.text x)
in (let _70_27554 = (let _70_27553 = (FSharp_Format.text ")")
in (_70_27553)::[])
in (_70_27555)::_70_27554))
in (_70_27557)::_70_27556))
in (FSharp_Format.reduce1 _70_27558))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _70_27564 = (let _70_27563 = (FSharp_Format.text "fun")
in (let _70_27562 = (let _70_27561 = (FSharp_Format.reduce1 ids)
in (let _70_27560 = (let _70_27559 = (FSharp_Format.text "->")
in (_70_27559)::(body)::[])
in (_70_27561)::_70_27560))
in (_70_27563)::_70_27562))
in (FSharp_Format.reduce1 _70_27564))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_27577 = (let _70_27576 = (let _70_27571 = (let _70_27570 = (FSharp_Format.text "if")
in (let _70_27569 = (let _70_27568 = (let _70_27567 = (FSharp_Format.text "then")
in (let _70_27566 = (let _70_27565 = (FSharp_Format.text "begin")
in (_70_27565)::[])
in (_70_27567)::_70_27566))
in (cond)::_70_27568)
in (_70_27570)::_70_27569))
in (FSharp_Format.reduce1 _70_27571))
in (let _70_27575 = (let _70_27574 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_27573 = (let _70_27572 = (FSharp_Format.text "end")
in (_70_27572)::[])
in (_70_27574)::_70_27573))
in (_70_27576)::_70_27575))
in (FSharp_Format.combine FSharp_Format.hardline _70_27577))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _70_27600 = (let _70_27599 = (let _70_27584 = (let _70_27583 = (FSharp_Format.text "if")
in (let _70_27582 = (let _70_27581 = (let _70_27580 = (FSharp_Format.text "then")
in (let _70_27579 = (let _70_27578 = (FSharp_Format.text "begin")
in (_70_27578)::[])
in (_70_27580)::_70_27579))
in (cond)::_70_27581)
in (_70_27583)::_70_27582))
in (FSharp_Format.reduce1 _70_27584))
in (let _70_27598 = (let _70_27597 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _70_27596 = (let _70_27595 = (let _70_27590 = (let _70_27589 = (FSharp_Format.text "end")
in (let _70_27588 = (let _70_27587 = (FSharp_Format.text "else")
in (let _70_27586 = (let _70_27585 = (FSharp_Format.text "begin")
in (_70_27585)::[])
in (_70_27587)::_70_27586))
in (_70_27589)::_70_27588))
in (FSharp_Format.reduce1 _70_27590))
in (let _70_27594 = (let _70_27593 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _70_27592 = (let _70_27591 = (FSharp_Format.text "end")
in (_70_27591)::[])
in (_70_27593)::_70_27592))
in (_70_27595)::_70_27594))
in (_70_27597)::_70_27596))
in (_70_27599)::_70_27598))
in (FSharp_Format.combine FSharp_Format.hardline _70_27600))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _70_27607 = (let _70_27606 = (let _70_27605 = (FSharp_Format.text "match")
in (let _70_27604 = (let _70_27603 = (FSharp_Format.parens cond)
in (let _70_27602 = (let _70_27601 = (FSharp_Format.text "with")
in (_70_27601)::[])
in (_70_27603)::_70_27602))
in (_70_27605)::_70_27604))
in (FSharp_Format.reduce1 _70_27606))
in (_70_27607)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _70_27612 = (let _70_27611 = (FSharp_Format.text "raise")
in (let _70_27610 = (let _70_27609 = (let _70_27608 = (ptctor currentModule exn)
in (FSharp_Format.text _70_27608))
in (_70_27609)::[])
in (_70_27611)::_70_27610))
in (FSharp_Format.reduce1 _70_27612))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _70_27621 = (let _70_27620 = (FSharp_Format.text "raise")
in (let _70_27619 = (let _70_27618 = (let _70_27613 = (ptctor currentModule exn)
in (FSharp_Format.text _70_27613))
in (let _70_27617 = (let _70_27616 = (let _70_27615 = (let _70_27614 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27614 args))
in (FSharp_Format.parens _70_27615))
in (_70_27616)::[])
in (_70_27618)::_70_27617))
in (_70_27620)::_70_27619))
in (FSharp_Format.reduce1 _70_27621)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _70_27638 = (let _70_27637 = (let _70_27625 = (let _70_27624 = (FSharp_Format.text "try")
in (let _70_27623 = (let _70_27622 = (FSharp_Format.text "begin")
in (_70_27622)::[])
in (_70_27624)::_70_27623))
in (FSharp_Format.reduce1 _70_27625))
in (let _70_27636 = (let _70_27635 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27634 = (let _70_27633 = (let _70_27629 = (let _70_27628 = (FSharp_Format.text "end")
in (let _70_27627 = (let _70_27626 = (FSharp_Format.text "with")
in (_70_27626)::[])
in (_70_27628)::_70_27627))
in (FSharp_Format.reduce1 _70_27629))
in (let _70_27632 = (let _70_27631 = (let _70_27630 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _70_27630))
in (_70_27631)::[])
in (_70_27633)::_70_27632))
in (_70_27635)::_70_27634))
in (_70_27637)::_70_27636))
in (FSharp_Format.combine FSharp_Format.hardline _70_27638))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_388 = (let _70_27643 = (as_bin_op p)
in (Support.Option.get _70_27643))
in (match (_59_388) with
| (_59_385, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _70_27646 = (let _70_27645 = (let _70_27644 = (FSharp_Format.text txt)
in (_70_27644)::(e2)::[])
in (e1)::_70_27645)
in (FSharp_Format.reduce1 _70_27646))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_398 = (let _70_27650 = (as_uni_op p)
in (Support.Option.get _70_27650))
in (match (_59_398) with
| (_59_396, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _70_27654 = (let _70_27653 = (FSharp_Format.text txt)
in (let _70_27652 = (let _70_27651 = (FSharp_Format.parens e1)
in (_70_27651)::[])
in (_70_27653)::_70_27652))
in (FSharp_Format.reduce1 _70_27654))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _70_27657 = (string_of_mlconstant c)
in (FSharp_Format.text _70_27657))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_415 ) -> (match (_59_415) with
| (name, p) -> begin
(let _70_27666 = (let _70_27665 = (let _70_27660 = (ptsym currentModule (path, name))
in (FSharp_Format.text _70_27660))
in (let _70_27664 = (let _70_27663 = (FSharp_Format.text "=")
in (let _70_27662 = (let _70_27661 = (doc_of_pattern currentModule p)
in (_70_27661)::[])
in (_70_27663)::_70_27662))
in (_70_27665)::_70_27664))
in (FSharp_Format.reduce1 _70_27666))
end))
in (let _70_27669 = (let _70_27668 = (FSharp_Format.text "; ")
in (let _70_27667 = (Support.List.map for1 fields)
in (FSharp_Format.combine _70_27668 _70_27667)))
in (FSharp_Format.cbrackets _70_27669)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _70_27671 = (let _70_27670 = (as_standard_constructor ctor)
in (Support.Option.get _70_27670))
in (Support.Prims.snd _70_27671))
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
(let _70_27673 = (let _70_27672 = (as_standard_constructor ctor)
in (Support.Option.get _70_27672))
in (Support.Prims.snd _70_27673))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _70_27676 = (let _70_27675 = (let _70_27674 = (FSharp_Format.text "::")
in (_70_27674)::(xs)::[])
in (x)::_70_27675)
in (FSharp_Format.reduce _70_27676))
end
| (_59_433, _59_435) -> begin
(let _70_27682 = (let _70_27681 = (FSharp_Format.text name)
in (let _70_27680 = (let _70_27679 = (let _70_27678 = (let _70_27677 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27677 ps))
in (FSharp_Format.parens _70_27678))
in (_70_27679)::[])
in (_70_27681)::_70_27680))
in (FSharp_Format.reduce1 _70_27682))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _70_27684 = (let _70_27683 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27683 ps))
in (FSharp_Format.parens _70_27684)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _70_27685 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _70_27685 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_449 ) -> (match (_59_449) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _70_27691 = (let _70_27690 = (FSharp_Format.text "|")
in (let _70_27689 = (let _70_27688 = (doc_of_pattern currentModule p)
in (_70_27688)::[])
in (_70_27690)::_70_27689))
in (FSharp_Format.reduce1 _70_27691))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _70_27697 = (let _70_27696 = (FSharp_Format.text "|")
in (let _70_27695 = (let _70_27694 = (doc_of_pattern currentModule p)
in (let _70_27693 = (let _70_27692 = (FSharp_Format.text "when")
in (_70_27692)::(c)::[])
in (_70_27694)::_70_27693))
in (_70_27696)::_70_27695))
in (FSharp_Format.reduce1 _70_27697)))
end)
in (let _70_27708 = (let _70_27707 = (let _70_27702 = (let _70_27701 = (let _70_27700 = (FSharp_Format.text "->")
in (let _70_27699 = (let _70_27698 = (FSharp_Format.text "begin")
in (_70_27698)::[])
in (_70_27700)::_70_27699))
in (case)::_70_27701)
in (FSharp_Format.reduce1 _70_27702))
in (let _70_27706 = (let _70_27705 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _70_27704 = (let _70_27703 = (FSharp_Format.text "end")
in (_70_27703)::[])
in (_70_27705)::_70_27704))
in (_70_27707)::_70_27706))
in (FSharp_Format.combine FSharp_Format.hardline _70_27708)))
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
in (let _70_27719 = (let _70_27718 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _70_27717 = (let _70_27716 = (FSharp_Format.reduce1 ids)
in (let _70_27715 = (let _70_27714 = (FSharp_Format.text "=")
in (_70_27714)::(e)::[])
in (_70_27716)::_70_27715))
in (_70_27718)::_70_27717))
in (FSharp_Format.reduce1 _70_27719)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _70_27723 = (let _70_27722 = (FSharp_Format.text "let")
in (let _70_27721 = (let _70_27720 = (FSharp_Format.text "rec")
in (_70_27720)::[])
in (_70_27722)::_70_27721))
in (FSharp_Format.reduce1 _70_27723))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _70_27727 = (let _70_27726 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_70_27726)::(doc)::[])
in (FSharp_Format.reduce1 _70_27727))) lets)
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
in (let _70_27736 = (let _70_27735 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _70_27735 doc))
in (FSharp_Format.parens _70_27736)))
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
in (let _70_27743 = (let _70_27742 = (let _70_27741 = (FSharp_Format.text ":")
in (_70_27741)::(ty)::[])
in (name)::_70_27742)
in (FSharp_Format.reduce1 _70_27743))))
end))
in (let _70_27746 = (let _70_27745 = (FSharp_Format.text "; ")
in (let _70_27744 = (Support.List.map forfield fields)
in (FSharp_Format.combine _70_27745 _70_27744)))
in (FSharp_Format.cbrackets _70_27746)))
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
in (let tys = (let _70_27749 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27749 tys))
in (let _70_27753 = (let _70_27752 = (FSharp_Format.text name)
in (let _70_27751 = (let _70_27750 = (FSharp_Format.text "of")
in (_70_27750)::(tys)::[])
in (_70_27752)::_70_27751))
in (FSharp_Format.reduce1 _70_27753))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _70_27756 = (let _70_27755 = (FSharp_Format.text "|")
in (_70_27755)::(d)::[])
in (FSharp_Format.reduce1 _70_27756))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _70_27760 = (let _70_27759 = (let _70_27758 = (let _70_27757 = (ptsym currentModule ([], x))
in (FSharp_Format.text _70_27757))
in (_70_27758)::[])
in (tparams)::_70_27759)
in (FSharp_Format.reduce1 _70_27760))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _70_27765 = (let _70_27764 = (let _70_27763 = (let _70_27762 = (let _70_27761 = (FSharp_Format.text "=")
in (_70_27761)::[])
in (doc)::_70_27762)
in (FSharp_Format.reduce1 _70_27763))
in (_70_27764)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _70_27765)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _70_27770 = (let _70_27769 = (FSharp_Format.text "type")
in (let _70_27768 = (let _70_27767 = (let _70_27766 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _70_27766 doc))
in (_70_27767)::[])
in (_70_27769)::_70_27768))
in (FSharp_Format.reduce1 _70_27770))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _70_27790 = (let _70_27789 = (let _70_27782 = (let _70_27781 = (FSharp_Format.text "module")
in (let _70_27780 = (let _70_27779 = (FSharp_Format.text x)
in (let _70_27778 = (let _70_27777 = (FSharp_Format.text "=")
in (_70_27777)::[])
in (_70_27779)::_70_27778))
in (_70_27781)::_70_27780))
in (FSharp_Format.reduce1 _70_27782))
in (let _70_27788 = (let _70_27787 = (doc_of_sig currentModule subsig)
in (let _70_27786 = (let _70_27785 = (let _70_27784 = (let _70_27783 = (FSharp_Format.text "end")
in (_70_27783)::[])
in (FSharp_Format.reduce1 _70_27784))
in (_70_27785)::[])
in (_70_27787)::_70_27786))
in (_70_27789)::_70_27788))
in (FSharp_Format.combine FSharp_Format.hardline _70_27790))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _70_27794 = (let _70_27793 = (FSharp_Format.text "exception")
in (let _70_27792 = (let _70_27791 = (FSharp_Format.text x)
in (_70_27791)::[])
in (_70_27793)::_70_27792))
in (FSharp_Format.reduce1 _70_27794))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_27796 = (let _70_27795 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27795 args))
in (FSharp_Format.parens _70_27796))
in (let _70_27802 = (let _70_27801 = (FSharp_Format.text "exception")
in (let _70_27800 = (let _70_27799 = (FSharp_Format.text x)
in (let _70_27798 = (let _70_27797 = (FSharp_Format.text "of")
in (_70_27797)::(args)::[])
in (_70_27799)::_70_27798))
in (_70_27801)::_70_27800))
in (FSharp_Format.reduce1 _70_27802))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_59_544, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _70_27808 = (let _70_27807 = (FSharp_Format.text "val")
in (let _70_27806 = (let _70_27805 = (FSharp_Format.text x)
in (let _70_27804 = (let _70_27803 = (FSharp_Format.text ": ")
in (_70_27803)::(ty)::[])
in (_70_27805)::_70_27804))
in (_70_27807)::_70_27806))
in (FSharp_Format.reduce1 _70_27808)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _70_27819 = (let _70_27818 = (FSharp_Format.text "exception")
in (let _70_27817 = (let _70_27816 = (FSharp_Format.text x)
in (_70_27816)::[])
in (_70_27818)::_70_27817))
in (FSharp_Format.reduce1 _70_27819))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _70_27821 = (let _70_27820 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _70_27820 args))
in (FSharp_Format.parens _70_27821))
in (let _70_27827 = (let _70_27826 = (FSharp_Format.text "exception")
in (let _70_27825 = (let _70_27824 = (FSharp_Format.text x)
in (let _70_27823 = (let _70_27822 = (FSharp_Format.text "of")
in (_70_27822)::(args)::[])
in (_70_27824)::_70_27823))
in (_70_27826)::_70_27825))
in (FSharp_Format.reduce1 _70_27827))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _70_27835 = (let _70_27834 = (FSharp_Format.text "let")
in (let _70_27833 = (let _70_27832 = (FSharp_Format.text "_")
in (let _70_27831 = (let _70_27830 = (FSharp_Format.text "=")
in (let _70_27829 = (let _70_27828 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_70_27828)::[])
in (_70_27830)::_70_27829))
in (_70_27832)::_70_27831))
in (_70_27834)::_70_27833))
in (FSharp_Format.reduce1 _70_27835))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_583 ) -> (match (_59_583) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_590 ) -> (match (_59_590) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _70_27854 = (let _70_27853 = (FSharp_Format.text "module")
in (let _70_27852 = (let _70_27851 = (FSharp_Format.text x)
in (let _70_27850 = (let _70_27849 = (FSharp_Format.text ":")
in (let _70_27848 = (let _70_27847 = (FSharp_Format.text "sig")
in (_70_27847)::[])
in (_70_27849)::_70_27848))
in (_70_27851)::_70_27850))
in (_70_27853)::_70_27852))
in (FSharp_Format.reduce1 _70_27854))
in (let tail = (let _70_27856 = (let _70_27855 = (FSharp_Format.text "end")
in (_70_27855)::[])
in (FSharp_Format.reduce1 _70_27856))
in (let doc = (Support.Option.map (fun ( _59_596 ) -> (match (_59_596) with
| (s, _59_595) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _70_27866 = (let _70_27865 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_27864 = (let _70_27863 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_27862 = (let _70_27861 = (FSharp_Format.reduce sub)
in (let _70_27860 = (let _70_27859 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_27859)::[])
in (_70_27861)::_70_27860))
in (_70_27863)::_70_27862))
in (_70_27865)::_70_27864))
in (FSharp_Format.reduce _70_27866)))))))
end))
and for1_mod = (fun ( istop ) ( _59_609 ) -> (match (_59_609) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _59_610 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _70_27876 = (match ((not (istop))) with
| true -> begin
(let _70_27875 = (FSharp_Format.text "module")
in (let _70_27874 = (let _70_27873 = (FSharp_Format.text x)
in (let _70_27872 = (let _70_27871 = (FSharp_Format.text "=")
in (let _70_27870 = (let _70_27869 = (FSharp_Format.text "struct")
in (_70_27869)::[])
in (_70_27871)::_70_27870))
in (_70_27873)::_70_27872))
in (_70_27875)::_70_27874))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _70_27876))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _70_27878 = (let _70_27877 = (FSharp_Format.text "end")
in (_70_27877)::[])
in (FSharp_Format.reduce1 _70_27878))
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
in (let _70_27888 = (let _70_27887 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _70_27886 = (let _70_27885 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _70_27884 = (let _70_27883 = (FSharp_Format.reduce sub)
in (let _70_27882 = (let _70_27881 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_70_27881)::[])
in (_70_27883)::_70_27882))
in (_70_27885)::_70_27884))
in (_70_27887)::_70_27886))
in (FSharp_Format.reduce _70_27888))))))))
end))
in (let docs = (Support.List.map (fun ( _59_628 ) -> (match (_59_628) with
| (x, s, m) -> begin
(let _70_27890 = (for1_mod true (x, s, m))
in (x, _70_27890))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))






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
(match ((let _65_24343 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _65_24343))) with
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
(let _59_46 = x
in (match (_59_46) with
| (ns, x) -> begin
(let _65_24348 = (path_of_ns currentModule ns)
in (_65_24348, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _65_24351 = (Support.String.get s 0)
in (Support.Char.lowercase _65_24351)) <> (Support.String.get s 0))) with
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
(let _59_52 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_52) with
| (p, s) -> begin
(let _65_24358 = (let _65_24357 = (let _65_24356 = (ptsym_of_symbol s)
in (_65_24356)::[])
in (Support.List.append p _65_24357))
in (Support.String.concat "." _65_24358))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _59_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_59_57) with
| (p, s) -> begin
(let s = (match (((let _65_24363 = (Support.String.get s 0)
in (Support.Char.uppercase _65_24363)) <> (Support.String.get s 0))) with
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

let as_bin_op = (fun ( _59_62 ) -> (match (_59_62) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_68 ) -> (match (_59_68) with
| (y, _, _) -> begin
(x = y)
end)) infix_prim_ops)
end
| false -> begin
None
end)
end))

let is_bin_op = (fun ( p ) -> ((as_bin_op p) <> None))

let as_uni_op = (fun ( _59_72 ) -> (match (_59_72) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_76 ) -> (match (_59_76) with
| (y, _) -> begin
(x = y)
end)) prim_uni_ops)
end
| false -> begin
None
end)
end))

let is_uni_op = (fun ( p ) -> ((as_uni_op p) <> None))

let as_standard_type = (fun ( _59_80 ) -> (match (_59_80) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_84 ) -> (match (_59_84) with
| (y, _) -> begin
(x = y)
end)) prim_types)
end
| false -> begin
None
end)
end))

let is_standard_type = (fun ( p ) -> ((as_standard_type p) <> None))

let as_standard_constructor = (fun ( _59_88 ) -> (match (_59_88) with
| (ns, x) -> begin
(match ((is_prims_ns ns)) with
| true -> begin
(Support.List.tryFind (fun ( _59_92 ) -> (match (_59_92) with
| (y, _) -> begin
(x = y)
end)) prim_constructors)
end
| false -> begin
None
end)
end))

let is_standard_constructor = (fun ( p ) -> ((as_standard_constructor p) <> None))

let maybe_paren = (fun ( _59_96 ) ( inner ) ( doc ) -> (match (_59_96) with
| (outer, side) -> begin
(let noparens = (fun ( _inner ) ( _outer ) ( side ) -> (let _59_105 = _inner
in (match (_59_105) with
| (pi, fi) -> begin
(let _59_108 = _outer
in (match (_59_108) with
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
(let _65_24405 = (let _65_24404 = (encode_char c)
in (Support.String.strcat "\'" _65_24404))
in (Support.String.strcat _65_24405 "\'"))
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
in (let _65_24417 = (Support.Prims.pipe_left escape_tyvar (Microsoft_FStar_Backends_ML_Syntax.idsym x))
in (FSharp_Format.text _65_24417)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _65_24420 = (let _65_24419 = (let _65_24418 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24418 doc))
in (FSharp_Format.hbox _65_24419))
in (FSharp_Format.parens _65_24420))
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
in (let _65_24423 = (let _65_24422 = (let _65_24421 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24421 args))
in (FSharp_Format.hbox _65_24422))
in (FSharp_Format.parens _65_24423)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _65_24425 = (let _65_24424 = (as_standard_type name)
in (Support.Option.get _65_24424))
in (Support.Prims.snd _65_24425))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _65_24429 = (let _65_24428 = (let _65_24427 = (let _65_24426 = (FSharp_Format.text name)
in (_65_24426)::[])
in (args)::_65_24427)
in (FSharp_Format.reduce1 _65_24428))
in (FSharp_Format.hbox _65_24429))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Fun ((t1, _, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_24434 = (let _65_24433 = (let _65_24432 = (let _65_24431 = (let _65_24430 = (FSharp_Format.text " -> ")
in (_65_24430)::(d2)::[])
in (d1)::_65_24431)
in (FSharp_Format.reduce1 _65_24432))
in (FSharp_Format.hbox _65_24433))
in (maybe_paren outer t_prio_fun _65_24434))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _65_24439 = (let _65_24438 = (let _65_24437 = (let _65_24436 = (let _65_24435 = (FSharp_Format.text " ")
in (_65_24435)::(d1)::[])
in (d2)::_65_24436)
in (FSharp_Format.reduce1 _65_24437))
in (FSharp_Format.hbox _65_24438))
in (maybe_paren outer t_prio_fun _65_24439))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Backends_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Backends_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24464 = (let _65_24463 = (let _65_24462 = (FSharp_Format.text "Obj.magic ")
in (_65_24462)::(doc)::[])
in (FSharp_Format.reduce _65_24463))
in (FSharp_Format.parens _65_24464)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _65_24468 = (let _65_24467 = (let _65_24466 = (FSharp_Format.text ";")
in (_65_24466)::(FSharp_Format.hardline)::[])
in (d)::_65_24467)
in (FSharp_Format.reduce _65_24468))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Const (c) -> begin
(let _65_24469 = (string_of_mlconstant c)
in (FSharp_Format.text _65_24469))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Var ((x, _)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Name (path) -> begin
(let _65_24470 = (ptsym currentModule path)
in (FSharp_Format.text _65_24470))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_250 ) -> (match (_59_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24477 = (let _65_24476 = (let _65_24473 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_24473))
in (let _65_24475 = (let _65_24474 = (FSharp_Format.text "=")
in (_65_24474)::(doc)::[])
in (_65_24476)::_65_24475))
in (FSharp_Format.reduce1 _65_24477)))
end))
in (let _65_24480 = (let _65_24479 = (FSharp_Format.text "; ")
in (let _65_24478 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_24479 _65_24478)))
in (FSharp_Format.cbrackets _65_24480)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24482 = (let _65_24481 = (as_standard_constructor ctor)
in (Support.Option.get _65_24481))
in (Support.Prims.snd _65_24482))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24484 = (let _65_24483 = (as_standard_constructor ctor)
in (Support.Option.get _65_24483))
in (Support.Prims.snd _65_24484))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _65_24488 = (let _65_24487 = (FSharp_Format.parens x)
in (let _65_24486 = (let _65_24485 = (FSharp_Format.text "::")
in (_65_24485)::(xs)::[])
in (_65_24487)::_65_24486))
in (FSharp_Format.reduce _65_24488))
end
| (_, _) -> begin
(let _65_24494 = (let _65_24493 = (FSharp_Format.text name)
in (let _65_24492 = (let _65_24491 = (let _65_24490 = (let _65_24489 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24489 args))
in (FSharp_Format.parens _65_24490))
in (_65_24491)::[])
in (_65_24493)::_65_24492))
in (FSharp_Format.reduce1 _65_24494))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _65_24496 = (let _65_24495 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24495 docs))
in (FSharp_Format.parens _65_24496))
in docs))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _65_24502 = (let _65_24501 = (let _65_24500 = (let _65_24499 = (let _65_24498 = (let _65_24497 = (FSharp_Format.text "in")
in (_65_24497)::(body)::[])
in (FSharp_Format.reduce1 _65_24498))
in (_65_24499)::[])
in (doc)::_65_24500)
in (FSharp_Format.combine FSharp_Format.hardline _65_24501))
in (FSharp_Format.parens _65_24502))))
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
in (let _65_24503 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _65_24503))))
end)
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _65_24509 = (let _65_24508 = (let _65_24507 = (FSharp_Format.text ".")
in (let _65_24506 = (let _65_24505 = (let _65_24504 = (ptsym currentModule f)
in (FSharp_Format.text _65_24504))
in (_65_24505)::[])
in (_65_24507)::_65_24506))
in (e)::_65_24508)
in (FSharp_Format.reduce _65_24509))
in doc))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _59_339 ) -> (match (_59_339) with
| ((x, _), xt) -> begin
(let _65_24516 = (let _65_24515 = (FSharp_Format.text "(")
in (let _65_24514 = (let _65_24513 = (FSharp_Format.text x)
in (let _65_24512 = (let _65_24511 = (FSharp_Format.text ")")
in (_65_24511)::[])
in (_65_24513)::_65_24512))
in (_65_24515)::_65_24514))
in (FSharp_Format.reduce1 _65_24516))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _65_24522 = (let _65_24521 = (FSharp_Format.text "fun")
in (let _65_24520 = (let _65_24519 = (FSharp_Format.reduce1 ids)
in (let _65_24518 = (let _65_24517 = (FSharp_Format.text "->")
in (_65_24517)::(body)::[])
in (_65_24519)::_65_24518))
in (_65_24521)::_65_24520))
in (FSharp_Format.reduce1 _65_24522))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_24535 = (let _65_24534 = (let _65_24529 = (let _65_24528 = (FSharp_Format.text "if")
in (let _65_24527 = (let _65_24526 = (let _65_24525 = (FSharp_Format.text "then")
in (let _65_24524 = (let _65_24523 = (FSharp_Format.text "begin")
in (_65_24523)::[])
in (_65_24525)::_65_24524))
in (cond)::_65_24526)
in (_65_24528)::_65_24527))
in (FSharp_Format.reduce1 _65_24529))
in (let _65_24533 = (let _65_24532 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_24531 = (let _65_24530 = (FSharp_Format.text "end")
in (_65_24530)::[])
in (_65_24532)::_65_24531))
in (_65_24534)::_65_24533))
in (FSharp_Format.combine FSharp_Format.hardline _65_24535))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _65_24558 = (let _65_24557 = (let _65_24542 = (let _65_24541 = (FSharp_Format.text "if")
in (let _65_24540 = (let _65_24539 = (let _65_24538 = (FSharp_Format.text "then")
in (let _65_24537 = (let _65_24536 = (FSharp_Format.text "begin")
in (_65_24536)::[])
in (_65_24538)::_65_24537))
in (cond)::_65_24539)
in (_65_24541)::_65_24540))
in (FSharp_Format.reduce1 _65_24542))
in (let _65_24556 = (let _65_24555 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _65_24554 = (let _65_24553 = (let _65_24548 = (let _65_24547 = (FSharp_Format.text "end")
in (let _65_24546 = (let _65_24545 = (FSharp_Format.text "else")
in (let _65_24544 = (let _65_24543 = (FSharp_Format.text "begin")
in (_65_24543)::[])
in (_65_24545)::_65_24544))
in (_65_24547)::_65_24546))
in (FSharp_Format.reduce1 _65_24548))
in (let _65_24552 = (let _65_24551 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _65_24550 = (let _65_24549 = (FSharp_Format.text "end")
in (_65_24549)::[])
in (_65_24551)::_65_24550))
in (_65_24553)::_65_24552))
in (_65_24555)::_65_24554))
in (_65_24557)::_65_24556))
in (FSharp_Format.combine FSharp_Format.hardline _65_24558))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _65_24565 = (let _65_24564 = (let _65_24563 = (FSharp_Format.text "match")
in (let _65_24562 = (let _65_24561 = (FSharp_Format.parens cond)
in (let _65_24560 = (let _65_24559 = (FSharp_Format.text "with")
in (_65_24559)::[])
in (_65_24561)::_65_24560))
in (_65_24563)::_65_24562))
in (FSharp_Format.reduce1 _65_24564))
in (_65_24565)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _65_24570 = (let _65_24569 = (FSharp_Format.text "raise")
in (let _65_24568 = (let _65_24567 = (let _65_24566 = (ptctor currentModule exn)
in (FSharp_Format.text _65_24566))
in (_65_24567)::[])
in (_65_24569)::_65_24568))
in (FSharp_Format.reduce1 _65_24570))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _65_24579 = (let _65_24578 = (FSharp_Format.text "raise")
in (let _65_24577 = (let _65_24576 = (let _65_24571 = (ptctor currentModule exn)
in (FSharp_Format.text _65_24571))
in (let _65_24575 = (let _65_24574 = (let _65_24573 = (let _65_24572 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24572 args))
in (FSharp_Format.parens _65_24573))
in (_65_24574)::[])
in (_65_24576)::_65_24575))
in (_65_24578)::_65_24577))
in (FSharp_Format.reduce1 _65_24579)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _65_24596 = (let _65_24595 = (let _65_24583 = (let _65_24582 = (FSharp_Format.text "try")
in (let _65_24581 = (let _65_24580 = (FSharp_Format.text "begin")
in (_65_24580)::[])
in (_65_24582)::_65_24581))
in (FSharp_Format.reduce1 _65_24583))
in (let _65_24594 = (let _65_24593 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24592 = (let _65_24591 = (let _65_24587 = (let _65_24586 = (FSharp_Format.text "end")
in (let _65_24585 = (let _65_24584 = (FSharp_Format.text "with")
in (_65_24584)::[])
in (_65_24586)::_65_24585))
in (FSharp_Format.reduce1 _65_24587))
in (let _65_24590 = (let _65_24589 = (let _65_24588 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _65_24588))
in (_65_24589)::[])
in (_65_24591)::_65_24590))
in (_65_24593)::_65_24592))
in (_65_24595)::_65_24594))
in (FSharp_Format.combine FSharp_Format.hardline _65_24596))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _59_387 = (let _65_24601 = (as_bin_op p)
in (Support.Option.get _65_24601))
in (match (_59_387) with
| (_, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _65_24604 = (let _65_24603 = (let _65_24602 = (FSharp_Format.text txt)
in (_65_24602)::(e2)::[])
in (e1)::_65_24603)
in (FSharp_Format.reduce1 _65_24604))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _59_397 = (let _65_24608 = (as_uni_op p)
in (Support.Option.get _65_24608))
in (match (_59_397) with
| (_, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _65_24612 = (let _65_24611 = (FSharp_Format.text txt)
in (let _65_24610 = (let _65_24609 = (FSharp_Format.parens e1)
in (_65_24609)::[])
in (_65_24611)::_65_24610))
in (FSharp_Format.reduce1 _65_24612))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Backends_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Const (c) -> begin
(let _65_24615 = (string_of_mlconstant c)
in (FSharp_Format.text _65_24615))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _59_414 ) -> (match (_59_414) with
| (name, p) -> begin
(let _65_24624 = (let _65_24623 = (let _65_24618 = (ptsym currentModule (path, name))
in (FSharp_Format.text _65_24618))
in (let _65_24622 = (let _65_24621 = (FSharp_Format.text "=")
in (let _65_24620 = (let _65_24619 = (doc_of_pattern currentModule p)
in (_65_24619)::[])
in (_65_24621)::_65_24620))
in (_65_24623)::_65_24622))
in (FSharp_Format.reduce1 _65_24624))
end))
in (let _65_24627 = (let _65_24626 = (FSharp_Format.text "; ")
in (let _65_24625 = (Support.List.map for1 fields)
in (FSharp_Format.combine _65_24626 _65_24625)))
in (FSharp_Format.cbrackets _65_24627)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _65_24629 = (let _65_24628 = (as_standard_constructor ctor)
in (Support.Option.get _65_24628))
in (Support.Prims.snd _65_24629))
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
(let _65_24631 = (let _65_24630 = (as_standard_constructor ctor)
in (Support.Option.get _65_24630))
in (Support.Prims.snd _65_24631))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _65_24634 = (let _65_24633 = (let _65_24632 = (FSharp_Format.text "::")
in (_65_24632)::(xs)::[])
in (x)::_65_24633)
in (FSharp_Format.reduce _65_24634))
end
| (_, _) -> begin
(let _65_24640 = (let _65_24639 = (FSharp_Format.text name)
in (let _65_24638 = (let _65_24637 = (let _65_24636 = (let _65_24635 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24635 ps))
in (FSharp_Format.parens _65_24636))
in (_65_24637)::[])
in (_65_24639)::_65_24638))
in (FSharp_Format.reduce1 _65_24640))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _65_24642 = (let _65_24641 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24641 ps))
in (FSharp_Format.parens _65_24642)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _65_24643 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _65_24643 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _59_448 ) -> (match (_59_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _65_24649 = (let _65_24648 = (FSharp_Format.text "|")
in (let _65_24647 = (let _65_24646 = (doc_of_pattern currentModule p)
in (_65_24646)::[])
in (_65_24648)::_65_24647))
in (FSharp_Format.reduce1 _65_24649))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _65_24655 = (let _65_24654 = (FSharp_Format.text "|")
in (let _65_24653 = (let _65_24652 = (doc_of_pattern currentModule p)
in (let _65_24651 = (let _65_24650 = (FSharp_Format.text "when")
in (_65_24650)::(c)::[])
in (_65_24652)::_65_24651))
in (_65_24654)::_65_24653))
in (FSharp_Format.reduce1 _65_24655)))
end)
in (let _65_24666 = (let _65_24665 = (let _65_24660 = (let _65_24659 = (let _65_24658 = (FSharp_Format.text "->")
in (let _65_24657 = (let _65_24656 = (FSharp_Format.text "begin")
in (_65_24656)::[])
in (_65_24658)::_65_24657))
in (case)::_65_24659)
in (FSharp_Format.reduce1 _65_24660))
in (let _65_24664 = (let _65_24663 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _65_24662 = (let _65_24661 = (FSharp_Format.text "end")
in (_65_24661)::[])
in (_65_24663)::_65_24662))
in (_65_24665)::_65_24664))
in (FSharp_Format.combine FSharp_Format.hardline _65_24666)))
end))
and doc_of_lets = (fun ( currentModule ) ( _59_457 ) -> (match (_59_457) with
| (rec_, lets) -> begin
(let for1 = (fun ( _59_464 ) -> (match (_59_464) with
| {Microsoft_FStar_Backends_ML_Syntax.mllb_name = name; Microsoft_FStar_Backends_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Backends_ML_Syntax.mllb_add_unit = _; Microsoft_FStar_Backends_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _59_470 ) -> (match (_59_470) with
| (x, _) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _65_24677 = (let _65_24676 = (FSharp_Format.text (Microsoft_FStar_Backends_ML_Syntax.idsym name))
in (let _65_24675 = (let _65_24674 = (FSharp_Format.reduce1 ids)
in (let _65_24673 = (let _65_24672 = (FSharp_Format.text "=")
in (_65_24672)::(e)::[])
in (_65_24674)::_65_24673))
in (_65_24676)::_65_24675))
in (FSharp_Format.reduce1 _65_24677)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _65_24681 = (let _65_24680 = (FSharp_Format.text "let")
in (let _65_24679 = (let _65_24678 = (FSharp_Format.text "rec")
in (_65_24678)::[])
in (_65_24680)::_65_24679))
in (FSharp_Format.reduce1 _65_24681))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _65_24685 = (let _65_24684 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_65_24684)::(doc)::[])
in (FSharp_Format.reduce1 _65_24685))) lets)
in (FSharp_Format.combine FSharp_Format.hardline lets)))))
end))

let doc_of_mltydecl = (fun ( currentModule ) ( decls ) -> (let for1 = (fun ( _59_483 ) -> (match (_59_483) with
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
in (let _65_24694 = (let _65_24693 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _65_24693 doc))
in (FSharp_Format.parens _65_24694)))
end)
in (let forbody = (fun ( body ) -> (match (body) with
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Abbrev (ty) -> begin
(doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_Record (fields) -> begin
(let forfield = (fun ( _59_501 ) -> (match (_59_501) with
| (name, ty) -> begin
(let name = (FSharp_Format.text name)
in (let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _65_24701 = (let _65_24700 = (let _65_24699 = (FSharp_Format.text ":")
in (_65_24699)::(ty)::[])
in (name)::_65_24700)
in (FSharp_Format.reduce1 _65_24701))))
end))
in (let _65_24704 = (let _65_24703 = (FSharp_Format.text "; ")
in (let _65_24702 = (Support.List.map forfield fields)
in (FSharp_Format.combine _65_24703 _65_24702)))
in (FSharp_Format.cbrackets _65_24704)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _59_509 ) -> (match (_59_509) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _ -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _65_24707 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24707 tys))
in (let _65_24711 = (let _65_24710 = (FSharp_Format.text name)
in (let _65_24709 = (let _65_24708 = (FSharp_Format.text "of")
in (_65_24708)::(tys)::[])
in (_65_24710)::_65_24709))
in (FSharp_Format.reduce1 _65_24711))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _65_24714 = (let _65_24713 = (FSharp_Format.text "|")
in (_65_24713)::(d)::[])
in (FSharp_Format.reduce1 _65_24714))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _65_24718 = (let _65_24717 = (let _65_24716 = (let _65_24715 = (ptsym currentModule ([], x))
in (FSharp_Format.text _65_24715))
in (_65_24716)::[])
in (tparams)::_65_24717)
in (FSharp_Format.reduce1 _65_24718))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _65_24723 = (let _65_24722 = (let _65_24721 = (let _65_24720 = (let _65_24719 = (FSharp_Format.text "=")
in (_65_24719)::[])
in (doc)::_65_24720)
in (FSharp_Format.reduce1 _65_24721))
in (_65_24722)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _65_24723)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _65_24728 = (let _65_24727 = (FSharp_Format.text "type")
in (let _65_24726 = (let _65_24725 = (let _65_24724 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _65_24724 doc))
in (_65_24725)::[])
in (_65_24727)::_65_24726))
in (FSharp_Format.reduce1 _65_24728))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Backends_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _65_24748 = (let _65_24747 = (let _65_24740 = (let _65_24739 = (FSharp_Format.text "module")
in (let _65_24738 = (let _65_24737 = (FSharp_Format.text x)
in (let _65_24736 = (let _65_24735 = (FSharp_Format.text "=")
in (_65_24735)::[])
in (_65_24737)::_65_24736))
in (_65_24739)::_65_24738))
in (FSharp_Format.reduce1 _65_24740))
in (let _65_24746 = (let _65_24745 = (doc_of_sig currentModule subsig)
in (let _65_24744 = (let _65_24743 = (let _65_24742 = (let _65_24741 = (FSharp_Format.text "end")
in (_65_24741)::[])
in (FSharp_Format.reduce1 _65_24742))
in (_65_24743)::[])
in (_65_24745)::_65_24744))
in (_65_24747)::_65_24746))
in (FSharp_Format.combine FSharp_Format.hardline _65_24748))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _65_24752 = (let _65_24751 = (FSharp_Format.text "exception")
in (let _65_24750 = (let _65_24749 = (FSharp_Format.text x)
in (_65_24749)::[])
in (_65_24751)::_65_24750))
in (FSharp_Format.reduce1 _65_24752))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_24754 = (let _65_24753 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24753 args))
in (FSharp_Format.parens _65_24754))
in (let _65_24760 = (let _65_24759 = (FSharp_Format.text "exception")
in (let _65_24758 = (let _65_24757 = (FSharp_Format.text x)
in (let _65_24756 = (let _65_24755 = (FSharp_Format.text "of")
in (_65_24755)::(args)::[])
in (_65_24757)::_65_24756))
in (_65_24759)::_65_24758))
in (FSharp_Format.reduce1 _65_24760))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Val ((x, (_, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _65_24766 = (let _65_24765 = (FSharp_Format.text "val")
in (let _65_24764 = (let _65_24763 = (FSharp_Format.text x)
in (let _65_24762 = (let _65_24761 = (FSharp_Format.text ": ")
in (_65_24761)::(ty)::[])
in (_65_24763)::_65_24762))
in (_65_24765)::_65_24764))
in (FSharp_Format.reduce1 _65_24766)))
end
| Microsoft_FStar_Backends_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _65_24777 = (let _65_24776 = (FSharp_Format.text "exception")
in (let _65_24775 = (let _65_24774 = (FSharp_Format.text x)
in (_65_24774)::[])
in (_65_24776)::_65_24775))
in (FSharp_Format.reduce1 _65_24777))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _65_24779 = (let _65_24778 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _65_24778 args))
in (FSharp_Format.parens _65_24779))
in (let _65_24785 = (let _65_24784 = (FSharp_Format.text "exception")
in (let _65_24783 = (let _65_24782 = (FSharp_Format.text x)
in (let _65_24781 = (let _65_24780 = (FSharp_Format.text "of")
in (_65_24780)::(args)::[])
in (_65_24782)::_65_24781))
in (_65_24784)::_65_24783))
in (FSharp_Format.reduce1 _65_24785))))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Backends_ML_Syntax.MLM_Top (e) -> begin
(let _65_24793 = (let _65_24792 = (FSharp_Format.text "let")
in (let _65_24791 = (let _65_24790 = (FSharp_Format.text "_")
in (let _65_24789 = (let _65_24788 = (FSharp_Format.text "=")
in (let _65_24787 = (let _65_24786 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_65_24786)::[])
in (_65_24788)::_65_24787))
in (_65_24790)::_65_24789))
in (_65_24792)::_65_24791))
in (FSharp_Format.reduce1 _65_24793))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _59_582 ) -> (match (_59_582) with
| Microsoft_FStar_Backends_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _59_589 ) -> (match (_59_589) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _65_24812 = (let _65_24811 = (FSharp_Format.text "module")
in (let _65_24810 = (let _65_24809 = (FSharp_Format.text x)
in (let _65_24808 = (let _65_24807 = (FSharp_Format.text ":")
in (let _65_24806 = (let _65_24805 = (FSharp_Format.text "sig")
in (_65_24805)::[])
in (_65_24807)::_65_24806))
in (_65_24809)::_65_24808))
in (_65_24811)::_65_24810))
in (FSharp_Format.reduce1 _65_24812))
in (let tail = (let _65_24814 = (let _65_24813 = (FSharp_Format.text "end")
in (_65_24813)::[])
in (FSharp_Format.reduce1 _65_24814))
in (let doc = (Support.Option.map (fun ( _59_595 ) -> (match (_59_595) with
| (s, _) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _65_24824 = (let _65_24823 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_24822 = (let _65_24821 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_24820 = (let _65_24819 = (FSharp_Format.reduce sub)
in (let _65_24818 = (let _65_24817 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_24817)::[])
in (_65_24819)::_65_24818))
in (_65_24821)::_65_24820))
in (_65_24823)::_65_24822))
in (FSharp_Format.reduce _65_24824)))))))
end))
and for1_mod = (fun ( istop ) ( _59_608 ) -> (match (_59_608) with
| (x, sigmod, Microsoft_FStar_Backends_ML_Syntax.MLLib (sub)) -> begin
(let _59_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _65_24834 = (match ((not (istop))) with
| true -> begin
(let _65_24833 = (FSharp_Format.text "module")
in (let _65_24832 = (let _65_24831 = (FSharp_Format.text x)
in (let _65_24830 = (let _65_24829 = (FSharp_Format.text "=")
in (let _65_24828 = (let _65_24827 = (FSharp_Format.text "struct")
in (_65_24827)::[])
in (_65_24829)::_65_24828))
in (_65_24831)::_65_24830))
in (_65_24833)::_65_24832))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _65_24834))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _65_24836 = (let _65_24835 = (FSharp_Format.text "end")
in (_65_24835)::[])
in (FSharp_Format.reduce1 _65_24836))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _59_616 ) -> (match (_59_616) with
| (_, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _65_24846 = (let _65_24845 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _65_24844 = (let _65_24843 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _65_24842 = (let _65_24841 = (FSharp_Format.reduce sub)
in (let _65_24840 = (let _65_24839 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_65_24839)::[])
in (_65_24841)::_65_24840))
in (_65_24843)::_65_24842))
in (_65_24845)::_65_24844))
in (FSharp_Format.reduce _65_24846))))))))
end))
in (let docs = (Support.List.map (fun ( _59_627 ) -> (match (_59_627) with
| (x, s, m) -> begin
(let _65_24848 = (for1_mod true (x, s, m))
in (x, _65_24848))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Backends_ML_Util.flatten_mlpath env.Microsoft_FStar_Backends_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Backends_ML_Util.flatten_mlpath env.Microsoft_FStar_Backends_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))





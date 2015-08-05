
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
| ([], _57_7) -> begin
true
end
| (x1::t1, x2::t2) when (x1 = x2) -> begin
(in_ns (t1, t2))
end
| (_57_17, _57_19) -> begin
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
(match ((let _68_24372 = (Support.ST.read Microsoft_FStar_Options.codegen_libs)
in (Support.List.tryPick chkin _68_24372))) with
| None -> begin
(outsupport ns)
end
| _57_31 -> begin
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
| _57_43 -> begin
(let _57_46 = x
in (match (_57_46) with
| (ns, x) -> begin
(let _68_24377 = (path_of_ns currentModule ns)
in (_68_24377, x))
end))
end))

let ptsym_of_symbol = (fun ( s ) -> (match (((let _68_24380 = (Support.String.get s 0)
in (Support.Char.lowercase _68_24380)) <> (Support.String.get s 0))) with
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
(let _68_24387 = (let _68_24386 = (let _68_24385 = (ptsym_of_symbol s)
in (_68_24385)::[])
in (Support.List.append p _68_24386))
in (Support.String.concat "." _68_24387))
end))
end))

let ptctor = (fun ( currentModule ) ( mlp ) -> (let _57_57 = (mlpath_of_mlpath currentModule mlp)
in (match (_57_57) with
| (p, s) -> begin
(let s = (match (((let _68_24392 = (Support.String.get s 0)
in (Support.Char.uppercase _68_24392)) <> (Support.String.get s 0))) with
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
| (y, _57_65, _57_67) -> begin
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
| (y, _57_75) -> begin
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
| (y, _57_83) -> begin
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
| (y, _57_91) -> begin
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
| (_57_132, NonAssoc) -> begin
((pi = po) && (fi = fo))
end
| (_57_136, _57_138) -> begin
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
| _57_156 -> begin
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
(let _68_24434 = (let _68_24433 = (encode_char c)
in (Support.String.strcat "\'" _68_24433))
in (Support.String.strcat _68_24434 "\'"))
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
in (let _68_24446 = (Support.Prims.pipe_left escape_tyvar (Microsoft_FStar_Extraction_ML_Syntax.idsym x))
in (FSharp_Format.text _68_24446)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Tuple (tys) -> begin
(let doc = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let doc = (let _68_24449 = (let _68_24448 = (let _68_24447 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24447 doc))
in (FSharp_Format.hbox _68_24448))
in (FSharp_Format.parens _68_24449))
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
| _57_198 -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let _68_24452 = (let _68_24451 = (let _68_24450 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24450 args))
in (FSharp_Format.hbox _68_24451))
in (FSharp_Format.parens _68_24452)))
end)
in (let name = (match ((is_standard_type name)) with
| true -> begin
(let _68_24454 = (let _68_24453 = (as_standard_type name)
in (Support.Option.get _68_24453))
in (Support.Prims.snd _68_24454))
end
| false -> begin
(ptsym currentModule name)
end)
in (let _68_24458 = (let _68_24457 = (let _68_24456 = (let _68_24455 = (FSharp_Format.text name)
in (_68_24455)::[])
in (args)::_68_24456)
in (FSharp_Format.reduce1 _68_24457))
in (FSharp_Format.hbox _68_24458))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Fun ((t1, _57_204, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _68_24463 = (let _68_24462 = (let _68_24461 = (let _68_24460 = (let _68_24459 = (FSharp_Format.text " -> ")
in (_68_24459)::(d2)::[])
in (d1)::_68_24460)
in (FSharp_Format.reduce1 _68_24461))
in (FSharp_Format.hbox _68_24462))
in (maybe_paren outer t_prio_fun _68_24463))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_App ((t1, t2)) -> begin
(let d1 = (doc_of_mltype currentModule (t_prio_fun, Left) t1)
in (let d2 = (doc_of_mltype currentModule (t_prio_fun, Right) t2)
in (let _68_24468 = (let _68_24467 = (let _68_24466 = (let _68_24465 = (let _68_24464 = (FSharp_Format.text " ")
in (_68_24464)::(d1)::[])
in (d2)::_68_24465)
in (FSharp_Format.reduce1 _68_24466))
in (FSharp_Format.hbox _68_24467))
in (maybe_paren outer t_prio_fun _68_24468))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTY_Top -> begin
(FSharp_Format.text "Obj.t")
end))
and doc_of_mltype = (fun ( currentModule ) ( outer ) ( ty ) -> (doc_of_mltype' currentModule outer (Microsoft_FStar_Extraction_ML_Util.resugar_mlty ty)))

let rec doc_of_expr = (fun ( currentModule ) ( outer ) ( e ) -> (match (e) with
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Coerce ((e, t, t')) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24493 = (let _68_24492 = (let _68_24491 = (FSharp_Format.text "Obj.magic ")
in (_68_24491)::(doc)::[])
in (FSharp_Format.reduce _68_24492))
in (FSharp_Format.parens _68_24493)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Seq (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (Support.List.map (fun ( d ) -> (let _68_24497 = (let _68_24496 = (let _68_24495 = (FSharp_Format.text ";")
in (_68_24495)::(FSharp_Format.hardline)::[])
in (d)::_68_24496)
in (FSharp_Format.reduce _68_24497))) docs)
in (FSharp_Format.reduce docs)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Const (c) -> begin
(let _68_24498 = (string_of_mlconstant c)
in (FSharp_Format.text _68_24498))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Var ((x, _57_238)) -> begin
(FSharp_Format.text x)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Name (path) -> begin
(let _68_24499 = (ptsym currentModule path)
in (FSharp_Format.text _68_24499))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Record ((path, fields)) -> begin
(let for1 = (fun ( _57_250 ) -> (match (_57_250) with
| (name, e) -> begin
(let doc = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24506 = (let _68_24505 = (let _68_24502 = (ptsym currentModule (path, name))
in (FSharp_Format.text _68_24502))
in (let _68_24504 = (let _68_24503 = (FSharp_Format.text "=")
in (_68_24503)::(doc)::[])
in (_68_24505)::_68_24504))
in (FSharp_Format.reduce1 _68_24506)))
end))
in (let _68_24509 = (let _68_24508 = (FSharp_Format.text "; ")
in (let _68_24507 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_24508 _68_24507)))
in (FSharp_Format.cbrackets _68_24509)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24511 = (let _68_24510 = (as_standard_constructor ctor)
in (Support.Option.get _68_24510))
in (Support.Prims.snd _68_24511))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (FSharp_Format.text name))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_CTor ((ctor, args)) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24513 = (let _68_24512 = (as_standard_constructor ctor)
in (Support.Option.get _68_24512))
in (Support.Prims.snd _68_24513))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let doc = (match ((name, args)) with
| ("::", x::xs::[]) -> begin
(let _68_24517 = (let _68_24516 = (FSharp_Format.parens x)
in (let _68_24515 = (let _68_24514 = (FSharp_Format.text "::")
in (_68_24514)::(xs)::[])
in (_68_24516)::_68_24515))
in (FSharp_Format.reduce _68_24517))
end
| (_57_269, _57_271) -> begin
(let _68_24523 = (let _68_24522 = (FSharp_Format.text name)
in (let _68_24521 = (let _68_24520 = (let _68_24519 = (let _68_24518 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24518 args))
in (FSharp_Format.parens _68_24519))
in (_68_24520)::[])
in (_68_24522)::_68_24521))
in (FSharp_Format.reduce1 _68_24523))
end)
in (maybe_paren outer e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Tuple (es) -> begin
(let docs = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es)
in (let docs = (let _68_24525 = (let _68_24524 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24524 docs))
in (FSharp_Format.parens _68_24525))
in docs))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Let (((rec_, lets), body)) -> begin
(let doc = (doc_of_lets currentModule (rec_, lets))
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let _68_24531 = (let _68_24530 = (let _68_24529 = (let _68_24528 = (let _68_24527 = (let _68_24526 = (FSharp_Format.text "in")
in (_68_24526)::(body)::[])
in (FSharp_Format.reduce1 _68_24527))
in (_68_24528)::[])
in (doc)::_68_24529)
in (FSharp_Format.combine FSharp_Format.hardline _68_24530))
in (FSharp_Format.parens _68_24531))))
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
| _57_321 -> begin
(let e = (doc_of_expr currentModule (e_app_prio, ILeft) e)
in (let args = (Support.List.map (doc_of_expr currentModule (e_app_prio, IRight)) args)
in (let _68_24532 = (FSharp_Format.reduce1 ((e)::args))
in (FSharp_Format.parens _68_24532))))
end)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Proj ((e, f)) -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let doc = (let _68_24538 = (let _68_24537 = (let _68_24536 = (FSharp_Format.text ".")
in (let _68_24535 = (let _68_24534 = (let _68_24533 = (ptsym currentModule f)
in (FSharp_Format.text _68_24533))
in (_68_24534)::[])
in (_68_24536)::_68_24535))
in (e)::_68_24537)
in (FSharp_Format.reduce _68_24538))
in doc))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Fun ((ids, body)) -> begin
(let ids = (Support.List.map (fun ( _57_339 ) -> (match (_57_339) with
| ((x, _57_336), xt) -> begin
(let _68_24545 = (let _68_24544 = (FSharp_Format.text "(")
in (let _68_24543 = (let _68_24542 = (FSharp_Format.text x)
in (let _68_24541 = (let _68_24540 = (FSharp_Format.text ")")
in (_68_24540)::[])
in (_68_24542)::_68_24541))
in (_68_24544)::_68_24543))
in (FSharp_Format.reduce1 _68_24545))
end)) ids)
in (let body = (doc_of_expr currentModule (min_op_prec, NonAssoc) body)
in (let doc = (let _68_24551 = (let _68_24550 = (FSharp_Format.text "fun")
in (let _68_24549 = (let _68_24548 = (FSharp_Format.reduce1 ids)
in (let _68_24547 = (let _68_24546 = (FSharp_Format.text "->")
in (_68_24546)::(body)::[])
in (_68_24548)::_68_24547))
in (_68_24550)::_68_24549))
in (FSharp_Format.reduce1 _68_24551))
in (FSharp_Format.parens doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, None)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_24564 = (let _68_24563 = (let _68_24558 = (let _68_24557 = (FSharp_Format.text "if")
in (let _68_24556 = (let _68_24555 = (let _68_24554 = (FSharp_Format.text "then")
in (let _68_24553 = (let _68_24552 = (FSharp_Format.text "begin")
in (_68_24552)::[])
in (_68_24554)::_68_24553))
in (cond)::_68_24555)
in (_68_24557)::_68_24556))
in (FSharp_Format.reduce1 _68_24558))
in (let _68_24562 = (let _68_24561 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _68_24560 = (let _68_24559 = (FSharp_Format.text "end")
in (_68_24559)::[])
in (_68_24561)::_68_24560))
in (_68_24563)::_68_24562))
in (FSharp_Format.combine FSharp_Format.hardline _68_24564))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_If ((cond, e1, Some (e2))) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let doc = (let _68_24587 = (let _68_24586 = (let _68_24571 = (let _68_24570 = (FSharp_Format.text "if")
in (let _68_24569 = (let _68_24568 = (let _68_24567 = (FSharp_Format.text "then")
in (let _68_24566 = (let _68_24565 = (FSharp_Format.text "begin")
in (_68_24565)::[])
in (_68_24567)::_68_24566))
in (cond)::_68_24568)
in (_68_24570)::_68_24569))
in (FSharp_Format.reduce1 _68_24571))
in (let _68_24585 = (let _68_24584 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let _68_24583 = (let _68_24582 = (let _68_24577 = (let _68_24576 = (FSharp_Format.text "end")
in (let _68_24575 = (let _68_24574 = (FSharp_Format.text "else")
in (let _68_24573 = (let _68_24572 = (FSharp_Format.text "begin")
in (_68_24572)::[])
in (_68_24574)::_68_24573))
in (_68_24576)::_68_24575))
in (FSharp_Format.reduce1 _68_24577))
in (let _68_24581 = (let _68_24580 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e2)
in (let _68_24579 = (let _68_24578 = (FSharp_Format.text "end")
in (_68_24578)::[])
in (_68_24580)::_68_24579))
in (_68_24582)::_68_24581))
in (_68_24584)::_68_24583))
in (_68_24586)::_68_24585))
in (FSharp_Format.combine FSharp_Format.hardline _68_24587))
in (maybe_paren outer e_bin_prio_if doc)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Match ((cond, pats)) -> begin
(let cond = (doc_of_expr currentModule (min_op_prec, NonAssoc) cond)
in (let pats = (Support.List.map (doc_of_branch currentModule) pats)
in (let doc = (let _68_24594 = (let _68_24593 = (let _68_24592 = (FSharp_Format.text "match")
in (let _68_24591 = (let _68_24590 = (FSharp_Format.parens cond)
in (let _68_24589 = (let _68_24588 = (FSharp_Format.text "with")
in (_68_24588)::[])
in (_68_24590)::_68_24589))
in (_68_24592)::_68_24591))
in (FSharp_Format.reduce1 _68_24593))
in (_68_24594)::pats)
in (let doc = (FSharp_Format.combine FSharp_Format.hardline doc)
in (FSharp_Format.parens doc)))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, [])) -> begin
(let _68_24599 = (let _68_24598 = (FSharp_Format.text "raise")
in (let _68_24597 = (let _68_24596 = (let _68_24595 = (ptctor currentModule exn)
in (FSharp_Format.text _68_24595))
in (_68_24596)::[])
in (_68_24598)::_68_24597))
in (FSharp_Format.reduce1 _68_24599))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Raise ((exn, args)) -> begin
(let args = (Support.List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args)
in (let _68_24608 = (let _68_24607 = (FSharp_Format.text "raise")
in (let _68_24606 = (let _68_24605 = (let _68_24600 = (ptctor currentModule exn)
in (FSharp_Format.text _68_24600))
in (let _68_24604 = (let _68_24603 = (let _68_24602 = (let _68_24601 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24601 args))
in (FSharp_Format.parens _68_24602))
in (_68_24603)::[])
in (_68_24605)::_68_24604))
in (_68_24607)::_68_24606))
in (FSharp_Format.reduce1 _68_24608)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLE_Try ((e, pats)) -> begin
(let _68_24625 = (let _68_24624 = (let _68_24612 = (let _68_24611 = (FSharp_Format.text "try")
in (let _68_24610 = (let _68_24609 = (FSharp_Format.text "begin")
in (_68_24609)::[])
in (_68_24611)::_68_24610))
in (FSharp_Format.reduce1 _68_24612))
in (let _68_24623 = (let _68_24622 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24621 = (let _68_24620 = (let _68_24616 = (let _68_24615 = (FSharp_Format.text "end")
in (let _68_24614 = (let _68_24613 = (FSharp_Format.text "with")
in (_68_24613)::[])
in (_68_24615)::_68_24614))
in (FSharp_Format.reduce1 _68_24616))
in (let _68_24619 = (let _68_24618 = (let _68_24617 = (Support.List.map (doc_of_branch currentModule) pats)
in (FSharp_Format.combine FSharp_Format.hardline _68_24617))
in (_68_24618)::[])
in (_68_24620)::_68_24619))
in (_68_24622)::_68_24621))
in (_68_24624)::_68_24623))
in (FSharp_Format.combine FSharp_Format.hardline _68_24625))
end))
and doc_of_binop = (fun ( currentModule ) ( p ) ( e1 ) ( e2 ) -> (let _57_387 = (let _68_24630 = (as_bin_op p)
in (Support.Option.get _68_24630))
in (match (_57_387) with
| (_57_384, prio, txt) -> begin
(let e1 = (doc_of_expr currentModule (prio, Left) e1)
in (let e2 = (doc_of_expr currentModule (prio, Right) e2)
in (let doc = (let _68_24633 = (let _68_24632 = (let _68_24631 = (FSharp_Format.text txt)
in (_68_24631)::(e2)::[])
in (e1)::_68_24632)
in (FSharp_Format.reduce1 _68_24633))
in (FSharp_Format.parens doc))))
end)))
and doc_of_uniop = (fun ( currentModule ) ( p ) ( e1 ) -> (let _57_397 = (let _68_24637 = (as_uni_op p)
in (Support.Option.get _68_24637))
in (match (_57_397) with
| (_57_395, txt) -> begin
(let e1 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e1)
in (let doc = (let _68_24641 = (let _68_24640 = (FSharp_Format.text txt)
in (let _68_24639 = (let _68_24638 = (FSharp_Format.parens e1)
in (_68_24638)::[])
in (_68_24640)::_68_24639))
in (FSharp_Format.reduce1 _68_24641))
in (FSharp_Format.parens doc)))
end)))
and doc_of_pattern = (fun ( currentModule ) ( pattern ) -> (match (pattern) with
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Wild -> begin
(FSharp_Format.text "_")
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Const (c) -> begin
(let _68_24644 = (string_of_mlconstant c)
in (FSharp_Format.text _68_24644))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Var (x) -> begin
(FSharp_Format.text (Support.Prims.fst x))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Record ((path, fields)) -> begin
(let for1 = (fun ( _57_414 ) -> (match (_57_414) with
| (name, p) -> begin
(let _68_24653 = (let _68_24652 = (let _68_24647 = (ptsym currentModule (path, name))
in (FSharp_Format.text _68_24647))
in (let _68_24651 = (let _68_24650 = (FSharp_Format.text "=")
in (let _68_24649 = (let _68_24648 = (doc_of_pattern currentModule p)
in (_68_24648)::[])
in (_68_24650)::_68_24649))
in (_68_24652)::_68_24651))
in (FSharp_Format.reduce1 _68_24653))
end))
in (let _68_24656 = (let _68_24655 = (FSharp_Format.text "; ")
in (let _68_24654 = (Support.List.map for1 fields)
in (FSharp_Format.combine _68_24655 _68_24654)))
in (FSharp_Format.cbrackets _68_24656)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_CTor ((ctor, [])) -> begin
(let name = (match ((is_standard_constructor ctor)) with
| true -> begin
(let _68_24658 = (let _68_24657 = (as_standard_constructor ctor)
in (Support.Option.get _68_24657))
in (Support.Prims.snd _68_24658))
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
(let _68_24660 = (let _68_24659 = (as_standard_constructor ctor)
in (Support.Option.get _68_24659))
in (Support.Prims.snd _68_24660))
end
| false -> begin
(ptctor currentModule ctor)
end)
in (let doc = (match ((name, ps)) with
| ("::", x::xs::[]) -> begin
(let _68_24663 = (let _68_24662 = (let _68_24661 = (FSharp_Format.text "::")
in (_68_24661)::(xs)::[])
in (x)::_68_24662)
in (FSharp_Format.reduce _68_24663))
end
| (_57_432, _57_434) -> begin
(let _68_24669 = (let _68_24668 = (FSharp_Format.text name)
in (let _68_24667 = (let _68_24666 = (let _68_24665 = (let _68_24664 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24664 ps))
in (FSharp_Format.parens _68_24665))
in (_68_24666)::[])
in (_68_24668)::_68_24667))
in (FSharp_Format.reduce1 _68_24669))
end)
in (maybe_paren (min_op_prec, NonAssoc) e_app_prio doc))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Tuple (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let _68_24671 = (let _68_24670 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24670 ps))
in (FSharp_Format.parens _68_24671)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLP_Branch (ps) -> begin
(let ps = (Support.List.map (doc_of_pattern currentModule) ps)
in (let ps = (Support.List.map FSharp_Format.parens ps)
in (let _68_24672 = (FSharp_Format.text " | ")
in (FSharp_Format.combine _68_24672 ps))))
end))
and doc_of_branch = (fun ( currentModule ) ( _57_448 ) -> (match (_57_448) with
| (p, cond, e) -> begin
(let case = (match (cond) with
| None -> begin
(let _68_24678 = (let _68_24677 = (FSharp_Format.text "|")
in (let _68_24676 = (let _68_24675 = (doc_of_pattern currentModule p)
in (_68_24675)::[])
in (_68_24677)::_68_24676))
in (FSharp_Format.reduce1 _68_24678))
end
| Some (c) -> begin
(let c = (doc_of_expr currentModule (min_op_prec, NonAssoc) c)
in (let _68_24684 = (let _68_24683 = (FSharp_Format.text "|")
in (let _68_24682 = (let _68_24681 = (doc_of_pattern currentModule p)
in (let _68_24680 = (let _68_24679 = (FSharp_Format.text "when")
in (_68_24679)::(c)::[])
in (_68_24681)::_68_24680))
in (_68_24683)::_68_24682))
in (FSharp_Format.reduce1 _68_24684)))
end)
in (let _68_24695 = (let _68_24694 = (let _68_24689 = (let _68_24688 = (let _68_24687 = (FSharp_Format.text "->")
in (let _68_24686 = (let _68_24685 = (FSharp_Format.text "begin")
in (_68_24685)::[])
in (_68_24687)::_68_24686))
in (case)::_68_24688)
in (FSharp_Format.reduce1 _68_24689))
in (let _68_24693 = (let _68_24692 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let _68_24691 = (let _68_24690 = (FSharp_Format.text "end")
in (_68_24690)::[])
in (_68_24692)::_68_24691))
in (_68_24694)::_68_24693))
in (FSharp_Format.combine FSharp_Format.hardline _68_24695)))
end))
and doc_of_lets = (fun ( currentModule ) ( _57_457 ) -> (match (_57_457) with
| (rec_, lets) -> begin
(let for1 = (fun ( _57_464 ) -> (match (_57_464) with
| {Microsoft_FStar_Extraction_ML_Syntax.mllb_name = name; Microsoft_FStar_Extraction_ML_Syntax.mllb_tysc = tys; Microsoft_FStar_Extraction_ML_Syntax.mllb_add_unit = _57_461; Microsoft_FStar_Extraction_ML_Syntax.mllb_def = e} -> begin
(let e = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (let ids = []
in (let ids = (Support.List.map (fun ( _57_470 ) -> (match (_57_470) with
| (x, _57_469) -> begin
(FSharp_Format.text x)
end)) ids)
in (let _68_24706 = (let _68_24705 = (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym name))
in (let _68_24704 = (let _68_24703 = (FSharp_Format.reduce1 ids)
in (let _68_24702 = (let _68_24701 = (FSharp_Format.text "=")
in (_68_24701)::(e)::[])
in (_68_24703)::_68_24702))
in (_68_24705)::_68_24704))
in (FSharp_Format.reduce1 _68_24706)))))
end))
in (let letdoc = (match (rec_) with
| true -> begin
(let _68_24710 = (let _68_24709 = (FSharp_Format.text "let")
in (let _68_24708 = (let _68_24707 = (FSharp_Format.text "rec")
in (_68_24707)::[])
in (_68_24709)::_68_24708))
in (FSharp_Format.reduce1 _68_24710))
end
| false -> begin
(FSharp_Format.text "let")
end)
in (let lets = (Support.List.map for1 lets)
in (let lets = (Support.List.mapi (fun ( i ) ( doc ) -> (let _68_24714 = (let _68_24713 = (match ((i = 0)) with
| true -> begin
letdoc
end
| false -> begin
(FSharp_Format.text "and")
end)
in (_68_24713)::(doc)::[])
in (FSharp_Format.reduce1 _68_24714))) lets)
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
| _57_488 -> begin
(let doc = (Support.List.map (fun ( x ) -> (FSharp_Format.text (Microsoft_FStar_Extraction_ML_Syntax.idsym x))) tparams)
in (let _68_24723 = (let _68_24722 = (FSharp_Format.text ", ")
in (FSharp_Format.combine _68_24722 doc))
in (FSharp_Format.parens _68_24723)))
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
in (let _68_24730 = (let _68_24729 = (let _68_24728 = (FSharp_Format.text ":")
in (_68_24728)::(ty)::[])
in (name)::_68_24729)
in (FSharp_Format.reduce1 _68_24730))))
end))
in (let _68_24733 = (let _68_24732 = (FSharp_Format.text "; ")
in (let _68_24731 = (Support.List.map forfield fields)
in (FSharp_Format.combine _68_24732 _68_24731)))
in (FSharp_Format.cbrackets _68_24733)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLTD_DType (ctors) -> begin
(let forctor = (fun ( _57_509 ) -> (match (_57_509) with
| (name, tys) -> begin
(match (tys) with
| [] -> begin
(FSharp_Format.text name)
end
| _57_512 -> begin
(let tys = (Support.List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys)
in (let tys = (let _68_24736 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24736 tys))
in (let _68_24740 = (let _68_24739 = (FSharp_Format.text name)
in (let _68_24738 = (let _68_24737 = (FSharp_Format.text "of")
in (_68_24737)::(tys)::[])
in (_68_24739)::_68_24738))
in (FSharp_Format.reduce1 _68_24740))))
end)
end))
in (let ctors = (Support.List.map forctor ctors)
in (let ctors = (Support.List.map (fun ( d ) -> (let _68_24743 = (let _68_24742 = (FSharp_Format.text "|")
in (_68_24742)::(d)::[])
in (FSharp_Format.reduce1 _68_24743))) ctors)
in (FSharp_Format.combine FSharp_Format.hardline ctors))))
end))
in (let doc = (let _68_24747 = (let _68_24746 = (let _68_24745 = (let _68_24744 = (ptsym currentModule ([], x))
in (FSharp_Format.text _68_24744))
in (_68_24745)::[])
in (tparams)::_68_24746)
in (FSharp_Format.reduce1 _68_24747))
in (match (body) with
| None -> begin
doc
end
| Some (body) -> begin
(let body = (forbody body)
in (let _68_24752 = (let _68_24751 = (let _68_24750 = (let _68_24749 = (let _68_24748 = (FSharp_Format.text "=")
in (_68_24748)::[])
in (doc)::_68_24749)
in (FSharp_Format.reduce1 _68_24750))
in (_68_24751)::(body)::[])
in (FSharp_Format.combine FSharp_Format.hardline _68_24752)))
end))))
end))
in (let doc = (Support.List.map for1 decls)
in (let doc = (match (((Support.List.length doc) > 0)) with
| true -> begin
(let _68_24757 = (let _68_24756 = (FSharp_Format.text "type")
in (let _68_24755 = (let _68_24754 = (let _68_24753 = (FSharp_Format.text " \n and ")
in (FSharp_Format.combine _68_24753 doc))
in (_68_24754)::[])
in (_68_24756)::_68_24755))
in (FSharp_Format.reduce1 _68_24757))
end
| false -> begin
(FSharp_Format.text "")
end)
in doc))))

let rec doc_of_sig1 = (fun ( currentModule ) ( s ) -> (match (s) with
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Mod ((x, subsig)) -> begin
(let _68_24777 = (let _68_24776 = (let _68_24769 = (let _68_24768 = (FSharp_Format.text "module")
in (let _68_24767 = (let _68_24766 = (FSharp_Format.text x)
in (let _68_24765 = (let _68_24764 = (FSharp_Format.text "=")
in (_68_24764)::[])
in (_68_24766)::_68_24765))
in (_68_24768)::_68_24767))
in (FSharp_Format.reduce1 _68_24769))
in (let _68_24775 = (let _68_24774 = (doc_of_sig currentModule subsig)
in (let _68_24773 = (let _68_24772 = (let _68_24771 = (let _68_24770 = (FSharp_Format.text "end")
in (_68_24770)::[])
in (FSharp_Format.reduce1 _68_24771))
in (_68_24772)::[])
in (_68_24774)::_68_24773))
in (_68_24776)::_68_24775))
in (FSharp_Format.combine FSharp_Format.hardline _68_24777))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, [])) -> begin
(let _68_24781 = (let _68_24780 = (FSharp_Format.text "exception")
in (let _68_24779 = (let _68_24778 = (FSharp_Format.text x)
in (_68_24778)::[])
in (_68_24780)::_68_24779))
in (FSharp_Format.reduce1 _68_24781))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _68_24783 = (let _68_24782 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24782 args))
in (FSharp_Format.parens _68_24783))
in (let _68_24789 = (let _68_24788 = (FSharp_Format.text "exception")
in (let _68_24787 = (let _68_24786 = (FSharp_Format.text x)
in (let _68_24785 = (let _68_24784 = (FSharp_Format.text "of")
in (_68_24784)::(args)::[])
in (_68_24786)::_68_24785))
in (_68_24788)::_68_24787))
in (FSharp_Format.reduce1 _68_24789))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Val ((x, (_57_543, ty))) -> begin
(let ty = (doc_of_mltype currentModule (min_op_prec, NonAssoc) ty)
in (let _68_24795 = (let _68_24794 = (FSharp_Format.text "val")
in (let _68_24793 = (let _68_24792 = (FSharp_Format.text x)
in (let _68_24791 = (let _68_24790 = (FSharp_Format.text ": ")
in (_68_24790)::(ty)::[])
in (_68_24792)::_68_24791))
in (_68_24794)::_68_24793))
in (FSharp_Format.reduce1 _68_24795)))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLS_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end))
and doc_of_sig = (fun ( currentModule ) ( s ) -> (let docs = (Support.List.map (doc_of_sig1 currentModule) s)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let doc_of_mod1 = (fun ( currentModule ) ( m ) -> (match (m) with
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, [])) -> begin
(let _68_24806 = (let _68_24805 = (FSharp_Format.text "exception")
in (let _68_24804 = (let _68_24803 = (FSharp_Format.text x)
in (_68_24803)::[])
in (_68_24805)::_68_24804))
in (FSharp_Format.reduce1 _68_24806))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Exn ((x, args)) -> begin
(let args = (Support.List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args)
in (let args = (let _68_24808 = (let _68_24807 = (FSharp_Format.text " * ")
in (FSharp_Format.combine _68_24807 args))
in (FSharp_Format.parens _68_24808))
in (let _68_24814 = (let _68_24813 = (FSharp_Format.text "exception")
in (let _68_24812 = (let _68_24811 = (FSharp_Format.text x)
in (let _68_24810 = (let _68_24809 = (FSharp_Format.text "of")
in (_68_24809)::(args)::[])
in (_68_24811)::_68_24810))
in (_68_24813)::_68_24812))
in (FSharp_Format.reduce1 _68_24814))))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Ty (decls) -> begin
(doc_of_mltydecl currentModule decls)
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Let ((rec_, lets)) -> begin
(doc_of_lets currentModule (rec_, lets))
end
| Microsoft_FStar_Extraction_ML_Syntax.MLM_Top (e) -> begin
(let _68_24822 = (let _68_24821 = (FSharp_Format.text "let")
in (let _68_24820 = (let _68_24819 = (FSharp_Format.text "_")
in (let _68_24818 = (let _68_24817 = (FSharp_Format.text "=")
in (let _68_24816 = (let _68_24815 = (doc_of_expr currentModule (min_op_prec, NonAssoc) e)
in (_68_24815)::[])
in (_68_24817)::_68_24816))
in (_68_24819)::_68_24818))
in (_68_24821)::_68_24820))
in (FSharp_Format.reduce1 _68_24822))
end))

let doc_of_mod = (fun ( currentModule ) ( m ) -> (let docs = (Support.List.map (doc_of_mod1 currentModule) m)
in (let docs = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) docs)
in (FSharp_Format.reduce docs))))

let rec doc_of_mllib_r = (fun ( _57_582 ) -> (match (_57_582) with
| Microsoft_FStar_Extraction_ML_Syntax.MLLib (mllib) -> begin
(let rec for1_sig = (fun ( _57_589 ) -> (match (_57_589) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let head = (let _68_24841 = (let _68_24840 = (FSharp_Format.text "module")
in (let _68_24839 = (let _68_24838 = (FSharp_Format.text x)
in (let _68_24837 = (let _68_24836 = (FSharp_Format.text ":")
in (let _68_24835 = (let _68_24834 = (FSharp_Format.text "sig")
in (_68_24834)::[])
in (_68_24836)::_68_24835))
in (_68_24838)::_68_24837))
in (_68_24840)::_68_24839))
in (FSharp_Format.reduce1 _68_24841))
in (let tail = (let _68_24843 = (let _68_24842 = (FSharp_Format.text "end")
in (_68_24842)::[])
in (FSharp_Format.reduce1 _68_24843))
in (let doc = (Support.Option.map (fun ( _57_595 ) -> (match (_57_595) with
| (s, _57_594) -> begin
(doc_of_sig x s)
end)) sigmod)
in (let sub = (Support.List.map for1_sig sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_24853 = (let _68_24852 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_24851 = (let _68_24850 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_24849 = (let _68_24848 = (FSharp_Format.reduce sub)
in (let _68_24847 = (let _68_24846 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_24846)::[])
in (_68_24848)::_68_24847))
in (_68_24850)::_68_24849))
in (_68_24852)::_68_24851))
in (FSharp_Format.reduce _68_24853)))))))
end))
and for1_mod = (fun ( istop ) ( _57_608 ) -> (match (_57_608) with
| (x, sigmod, Microsoft_FStar_Extraction_ML_Syntax.MLLib (sub)) -> begin
(let _57_609 = (Support.Microsoft.FStar.Util.fprint1 "Gen Code: %s\n" x)
in (let head = (let _68_24863 = (match ((not (istop))) with
| true -> begin
(let _68_24862 = (FSharp_Format.text "module")
in (let _68_24861 = (let _68_24860 = (FSharp_Format.text x)
in (let _68_24859 = (let _68_24858 = (FSharp_Format.text "=")
in (let _68_24857 = (let _68_24856 = (FSharp_Format.text "struct")
in (_68_24856)::[])
in (_68_24858)::_68_24857))
in (_68_24860)::_68_24859))
in (_68_24862)::_68_24861))
end
| false -> begin
[]
end)
in (FSharp_Format.reduce1 _68_24863))
in (let tail = (match ((not (istop))) with
| true -> begin
(let _68_24865 = (let _68_24864 = (FSharp_Format.text "end")
in (_68_24864)::[])
in (FSharp_Format.reduce1 _68_24865))
end
| false -> begin
(FSharp_Format.reduce1 [])
end)
in (let doc = (Support.Option.map (fun ( _57_616 ) -> (match (_57_616) with
| (_57_614, m) -> begin
(doc_of_mod x m)
end)) sigmod)
in (let sub = (Support.List.map (for1_mod false) sub)
in (let sub = (Support.List.map (fun ( x ) -> (FSharp_Format.reduce ((x)::(FSharp_Format.hardline)::(FSharp_Format.hardline)::[]))) sub)
in (let _68_24875 = (let _68_24874 = (FSharp_Format.cat head FSharp_Format.hardline)
in (let _68_24873 = (let _68_24872 = (match (doc) with
| None -> begin
FSharp_Format.empty
end
| Some (s) -> begin
(FSharp_Format.cat s FSharp_Format.hardline)
end)
in (let _68_24871 = (let _68_24870 = (FSharp_Format.reduce sub)
in (let _68_24869 = (let _68_24868 = (FSharp_Format.cat tail FSharp_Format.hardline)
in (_68_24868)::[])
in (_68_24870)::_68_24869))
in (_68_24872)::_68_24871))
in (_68_24874)::_68_24873))
in (FSharp_Format.reduce _68_24875))))))))
end))
in (let docs = (Support.List.map (fun ( _57_627 ) -> (match (_57_627) with
| (x, s, m) -> begin
(let _68_24877 = (for1_mod true (x, s, m))
in (x, _68_24877))
end)) mllib)
in docs))
end))

let doc_of_mllib = (fun ( mllib ) -> (doc_of_mllib_r mllib))

let string_of_mlexpr = (fun ( env ) ( e ) -> (let doc = (doc_of_expr (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))

let string_of_mlty = (fun ( env ) ( e ) -> (let doc = (doc_of_mltype (Microsoft_FStar_Extraction_ML_Util.flatten_mlpath env.Microsoft_FStar_Extraction_ML_Env.currentModule) (min_op_prec, NonAssoc) e)
in (FSharp_Format.pretty 0 doc)))




